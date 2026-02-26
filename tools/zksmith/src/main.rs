use std::{
    collections::{HashMap, HashSet, VecDeque},
    net::SocketAddr,
    sync::Arc,
};

use clap::Parser;
use cli_lib::prover_utils::{
    default_backend_for_build, u32_from_hex_string, ProgramProver, ProgramProverConfig,
    ProgramSource, ProofArtifact, ProofTarget,
};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_json::Value;
use warp::Filter;

// Anvil currently exposes ZKsync OS witness via this method name.
const ANVIL_WITNESS_RPC_METHOD: &str = "anvil_zks_getBoojumWitness";

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(short, long)]
    anvil_url: String,
    #[arg(long)]
    zksync_os_bin_path: String,
    #[arg(long)]
    output_dir: Option<String>,

    /// If not set: 127.0.0.1:3030
    #[arg(long)]
    host_port: Option<String>,
}

async fn fetch_data_from_json_rpc(
    url: &str,
    batch_number: u64,
) -> Result<Option<String>, reqwest::Error> {
    let client = Client::new();
    let request_body = serde_json::json!({
        "jsonrpc": "2.0",
        "method": ANVIL_WITNESS_RPC_METHOD,
        "params": [batch_number],
        "id": 1,
    });

    let response = client
        .post(url)
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await?
        .json::<Value>()
        .await?;

    match &response["result"] {
        Value::String(data) => {
            let tmp_data = data.strip_prefix("0x").unwrap_or(data);
            Ok(Some(tmp_data.to_string()))
        }
        _ => Ok(None),
    }
}

struct LocalProver {
    prover: ProgramProver,
}

impl LocalProver {
    fn new(zksync_os_bin_path: String) -> LocalProver {
        let source = ProgramSource::from_paths(zksync_os_bin_path, None);
        let config = ProgramProverConfig {
            target: ProofTarget::RecursionUnified,
            backend: default_backend_for_build(),
            ..Default::default()
        };

        let prover = ProgramProver::new(source, config)
            .unwrap_or_else(|e| panic!("failed to initialize program prover: {}", e));

        LocalProver { prover }
    }

    fn create_proof_for_data(
        &self,
        data: &String,
        batch: u64,
    ) -> (ProofArtifact, u64, u64, usize, Vec<usize>) {
        let now = std::time::Instant::now();
        let non_determinism_data = u32_from_hex_string(data);

        let artifact = self
            .prover
            .prove_words(batch, non_determinism_data)
            .unwrap_or_else(|e| panic!("failed to prove batch {}: {}", batch, e));

        let basic_duration = artifact.timings_ms.base_ms;
        let basic_proofs = artifact.proof_counts.family_proof_count;
        let delegation_proofs = artifact
            .proof_counts
            .delegation_proof_count_by_type
            .iter()
            .map(|(_, count)| *count)
            .collect::<Vec<_>>();

        println!("==== Batch {} took {:?} ====", batch, now.elapsed());
        (
            artifact,
            now.elapsed().as_millis() as u64,
            basic_duration,
            basic_proofs,
            delegation_proofs,
        )
    }
}

struct BlockProcessor {
    inner: tokio::sync::Mutex<BlockProcessorInner>,
}

struct BlockProofInfo {
    block_id: u64,
    proof: ProofArtifact,
    duration: u64,
    basic_duration: u64,
    basic_proof_count: usize,
    delegation_proof_count: Vec<usize>,
}

struct BlockProcessorInner {
    blocks_to_do: VecDeque<(u64, String)>,
    blocks_proven: HashMap<u64, BlockProofInfo>,
    in_progress: HashSet<u64>,
}

impl BlockProcessor {
    fn new() -> Self {
        Self {
            inner: tokio::sync::Mutex::new(BlockProcessorInner {
                blocks_to_do: Default::default(),
                blocks_proven: Default::default(),
                in_progress: Default::default(),
            }),
        }
    }

    async fn get_blocks_todo(&self) -> Vec<u64> {
        let inner = self.inner.lock().await;
        inner.blocks_to_do.iter().map(|(id, _)| *id).collect()
    }

    fn get_blocks_todo_sync(&self) -> Vec<u64> {
        tokio::task::block_in_place(|| futures::executor::block_on(self.get_blocks_todo()))
    }

    fn pop_next_block_todo_sync(&self) -> Option<(u64, String)> {
        tokio::task::block_in_place(|| futures::executor::block_on(self.pop_next_block_todo()))
    }

    async fn pop_next_block_todo(&self) -> Option<(u64, String)> {
        let mut inner = self.inner.lock().await;
        let pop = inner.blocks_to_do.pop_front();
        if let Some(pop) = &pop {
            inner.in_progress.insert(pop.0);
        }
        pop
    }

    async fn add_new_block(&self, block_id: u64, data: String) {
        let mut inner = self.inner.lock().await;
        inner.blocks_to_do.push_back((block_id, data));
    }

    fn add_new_block_sync(&self, block_id: u64, data: String) {
        tokio::task::block_in_place(|| {
            futures::executor::block_on(self.add_new_block(block_id, data))
        });
    }

    async fn mark_block_as_proven(&self, proof_info: BlockProofInfo) {
        let mut inner = self.inner.lock().await;

        if let Some(pos) = inner
            .blocks_to_do
            .iter()
            .position(|(id, _)| *id == proof_info.block_id)
        {
            inner.blocks_to_do.remove(pos);
        }
        inner.in_progress.remove(&proof_info.block_id);

        inner.blocks_proven.insert(proof_info.block_id, proof_info);
    }

    fn mark_block_as_proven_sync(&self, proof_info: BlockProofInfo) {
        tokio::task::block_in_place(|| {
            futures::executor::block_on(self.mark_block_as_proven(proof_info))
        })
    }

    async fn show_proven_blocks(&self) -> Vec<(u64, u64, u64, usize, String)> {
        let inner = self.inner.lock().await;
        let mut keys = inner.blocks_proven.keys().cloned().collect::<Vec<_>>();
        keys.sort();
        keys.into_iter()
            .filter_map(|block_id| inner.blocks_proven.get(&block_id))
            .map(|info| {
                (
                    info.block_id,
                    info.duration,
                    info.basic_duration,
                    info.basic_proof_count,
                    info.delegation_proof_count
                        .iter()
                        .map(|count| count.to_string())
                        .collect::<Vec<_>>()
                        .join(","),
                )
            })
            .collect::<Vec<_>>()
    }

    fn show_proven_blocks_sync(&self) -> Vec<(u64, u64, u64, usize, String)> {
        tokio::task::block_in_place(|| futures::executor::block_on(self.show_proven_blocks()))
    }

    async fn get_proof(&self, block_id: u64) -> Option<String> {
        let inner = self.inner.lock().await;
        inner.blocks_proven.get(&block_id).map(|info| {
            let proof = &info.proof;
            serde_json::to_string(proof).unwrap()
        })
    }

    fn get_proof_sync(&self, block_id: u64) -> Option<String> {
        tokio::task::block_in_place(|| futures::executor::block_on(self.get_proof(block_id)))
    }

    async fn get_in_progress(&self) -> Option<u64> {
        let inner = self.inner.lock().await;
        if inner.in_progress.is_empty() {
            None
        } else {
            Some(*inner.in_progress.iter().next().unwrap())
        }
    }

    fn get_in_progress_sync(&self) -> Option<u64> {
        tokio::task::block_in_place(|| futures::executor::block_on(self.get_in_progress()))
    }
}

#[derive(Deserialize)]
struct RpcRequest {
    id: u64,
    method: String,
}

#[derive(Serialize)]
struct RpcResponse {
    jsonrpc: String,
    id: u64,
    result: serde_json::Value,
}

#[tokio::main(flavor = "multi_thread", worker_threads = 10)]
async fn main() {
    init_logger();

    let index_html = include_str!("index.html");

    let cli = Cli::parse();
    println!("Initializing prover...");
    let prover = LocalProver::new(cli.zksync_os_bin_path.clone());

    let anvil_url = cli.anvil_url;
    println!("Connecting to Anvil at {}", anvil_url);

    let processor = Arc::new(BlockProcessor::new());
    let processor_clone = processor.clone();
    let processor_web_clone = processor.clone();
    let processor_download = processor.clone();

    tokio::spawn(async move {
        let mut interval = tokio::time::interval(std::time::Duration::from_secs(3));
        let mut next_batch = 1;

        loop {
            interval.tick().await;

            loop {
                let data = fetch_data_from_json_rpc(&anvil_url, next_batch).await;

                match data {
                    Ok(Some(data)) => {
                        println!("Fetched data for batch : {}", next_batch);
                        processor.add_new_block_sync(next_batch, data);
                        next_batch += 1;
                    }
                    Ok(None) => {
                        println!("No data found for block ID - sleeping: {}", next_batch);
                        break;
                    }
                    Err(e) => {
                        eprintln!("Error fetching data: {}", e);
                        break;
                    }
                }
            }
        }
    });

    tokio::spawn(async move {
        let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));

        loop {
            interval.tick().await;
            let next_block = processor_clone.pop_next_block_todo_sync();
            if let Some((block_id, data)) = next_block {
                println!("Proving block ID: {}", block_id);
                let (proof, duration, basic_duration, basic_proof_count, delegation_proof_count) =
                    prover.create_proof_for_data(&data, block_id);
                println!(
                    "Proof created for block ID {}: {} family proofs in {}ms",
                    block_id, basic_proof_count, duration
                );
                processor_clone.mark_block_as_proven_sync(BlockProofInfo {
                    block_id,
                    proof,
                    duration,
                    basic_duration,
                    basic_proof_count,
                    delegation_proof_count,
                });
            }
        }
    });

    let rpc = warp::path("rpc")
        .and(warp::post())
        .and(warp::body::json())
        .map(move |req: RpcRequest| {
            let result = match req.method.as_str() {
                "getBlocks" => {
                    let blocks = processor_web_clone.get_blocks_todo_sync();
                    json!(
                        blocks
                            .into_iter()
                            .map(|id| json!({"id": id, "name": format!("Block {}", id)}))
                            .collect::<Vec<_>>()
                    )
                }
                "getProofs" => {
                    let blocks = processor_web_clone.show_proven_blocks_sync();

                    json!(
                        blocks
                            .into_iter()
                            .map(|(id, duration, basic_duration, proofs, delegation_proofs)| json!({"id": id, "duration": duration, "basicDuration": basic_duration, "proofs": proofs, "delegationProofs": delegation_proofs, "link": format!("/downloads/{}", id)}))
                            .collect::<Vec<_>>()
                    )
                }
                "inProgress" => {
                    let in_progress = processor_web_clone.get_in_progress_sync();
                    json!({"inProgress": in_progress})
                }
                _ => json!(null),
            };
            warp::reply::json(&RpcResponse {
                jsonrpc: "2.0".into(),
                id: req.id,
                result,
            })
        });

    let index = warp::path::end().map({
        let html = index_html;
        move || warp::reply::html(html)
    });

    let downloads = warp::path!("downloads" / u64).map(move |proof_id: u64| {
        let proof = processor_download.get_proof_sync(proof_id);
        warp::reply::html(proof.unwrap())
    });

    let routes = rpc.or(downloads).or(index);

    let addr = cli.host_port.unwrap_or("127.0.0.1:3030".to_string());
    println!("Server running at http://{}", addr);

    warp::serve(routes)
        .run(addr.parse::<SocketAddr>().unwrap())
        .await;
}

fn init_logger() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .target(env_logger::Target::Stdout)
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::time::Instant;

    // Test binaries may run either from repository root (CI runtime job) or crate dir.
    fn default_hashed_fibonacci_bin_path() -> String {
        let cwd_relative = PathBuf::from("examples/hashed_fibonacci/app.bin");
        if cwd_relative.exists() {
            return cwd_relative.to_string_lossy().to_string();
        }

        let manifest_relative = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/hashed_fibonacci/app.bin");
        if manifest_relative.exists() {
            return manifest_relative.to_string_lossy().to_string();
        }

        panic!("could not locate examples/hashed_fibonacci/app.bin");
    }

    /// This test requires GPU.
    #[tokio::test]
    async fn test_local_prover_with_files() {
        init_logger();

        let test_files = vec![
            include_str!("../testdata/1.json"),
            include_str!("../testdata/2.json"),
        ];
        let mut timings = Vec::new();

        let prover = LocalProver::new(default_hashed_fibonacci_bin_path());

        for (i, data) in test_files.iter().enumerate() {
            let parsed_data: Value = serde_json::from_str(data).expect("Failed to parse JSON");
            let result_field = parsed_data["result"]
                .as_str()
                .expect("Missing or invalid 'result' field")
                .to_string();
            let tmp_data = result_field
                .strip_prefix("0x")
                .unwrap_or(&result_field)
                .to_string();

            let batch_id = (i + 1) as u64;

            let start = Instant::now();
            let (_proof, duration, basic_duration, basic_proof_count, delegation_proof_count) =
                prover.create_proof_for_data(&tmp_data, batch_id);
            let elapsed = start.elapsed().as_millis();

            timings.push((
                batch_id,
                elapsed,
                duration,
                basic_duration,
                basic_proof_count,
                delegation_proof_count,
            ));
        }

        println!("Timing results:");
        for (
            batch_id,
            elapsed,
            duration,
            basic_duration,
            basic_proof_count,
            delegation_proof_count,
        ) in timings
        {
            println!(
                "Batch ID: {}, Total Time: {}ms, Proof Duration: {}ms, Basic Duration: {}ms, Basic Proofs: {}, Delegation Proofs: {:?}",
                batch_id,
                elapsed,
                duration,
                basic_duration,
                basic_proof_count,
                delegation_proof_count
            );
        }
    }
}
