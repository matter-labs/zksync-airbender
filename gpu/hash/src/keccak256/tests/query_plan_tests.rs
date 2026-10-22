use era_cudart::memory::DeviceAllocation;
use era_cudart::stream::CudaStream;

use super::super::{launch_coset_query_plan, MAX_PLAN_QUERIES};
use super::{download, upload, TestRng};

fn cpu_coset_query_plan(queries: &[u32], log_lde: u32) -> (Vec<u32>, Vec<u32>, u32) {
    let mask = (1u32 << log_lde) - 1;
    let mut touched = Vec::new();
    for &query in queries {
        if !touched.contains(&(query & mask)) {
            touched.push(query & mask);
        }
    }
    let count = touched.len() as u32;
    let active = (0..queries.len() as u32)
        .map(|s| u32::from(s < count))
        .collect();
    touched.resize(queries.len(), 0);
    (touched, active, count)
}

// Query sets of spec 3.1: all in one coset, duplicates, one per coset, the last valid index,
// Q = 1, touched order [last, 1, 0], Q = 1,024, random.
fn query_sets(log_lde: u32, log_leaves: u32, rng: &mut TestRng) -> Vec<(&'static str, Vec<u32>)> {
    let cosets = 1u32 << log_lde;
    let query = |leaf: u32, coset: u32| (leaf << log_lde) | coset;
    let last = (1u32 << (log_leaves + log_lde)) - 1;
    vec![
        (
            "one coset",
            (0..14).map(|i| query(i * 7, 5 % cosets)).collect(),
        ),
        (
            "duplicates",
            vec![
                query(3, 1),
                query(3, 1),
                query(9, 2),
                query(3, 1),
                query(9, 2),
            ],
        ),
        (
            "one per coset",
            (0..cosets.min(MAX_PLAN_QUERIES as u32))
                .map(|c| query(c, c))
                .collect(),
        ),
        ("last valid index", vec![last, 0, last]),
        ("single", vec![query(17, cosets - 1)]),
        (
            "touched order [last, 1, 0]",
            vec![query(1, cosets - 1), query(2, 1), query(3, 0), query(4, 1)],
        ),
        (
            "1024 random",
            (0..1024).map(|_| (rng.next_u64() as u32) & last).collect(),
        ),
        (
            "14 random",
            (0..14).map(|_| (rng.next_u64() as u32) & last).collect(),
        ),
    ]
}

#[test]
fn keccak256_coset_query_plan_matches_cpu() {
    let stream = CudaStream::create().unwrap();
    let mut rng = TestRng::new(0x3110_0001);
    for (log_lde, log_leaves) in [(0u32, 10u32), (1, 12), (6, 20), (9, 19), (12, 12)] {
        for (name, queries) in query_sets(log_lde, log_leaves, &mut rng) {
            let (touched, active, count) = cpu_coset_query_plan(&queries, log_lde);
            let device_queries = upload(&queries, &stream);
            let mut device_touched = DeviceAllocation::<u32>::alloc(queries.len()).unwrap();
            let mut device_active = DeviceAllocation::<u32>::alloc(queries.len()).unwrap();
            let mut device_count = DeviceAllocation::<u32>::alloc(1).unwrap();
            launch_coset_query_plan(
                &device_queries,
                log_lde,
                &mut device_touched,
                &mut device_active,
                &mut device_count,
                &stream,
            )
            .unwrap();
            assert_eq!(
                download(&device_touched, u32::MAX, &stream),
                touched,
                "{name} at log_lde {log_lde}: touched"
            );
            assert_eq!(
                download(&device_active, u32::MAX, &stream),
                active,
                "{name} at log_lde {log_lde}: active"
            );
            assert_eq!(
                download(&device_count, u32::MAX, &stream),
                vec![count],
                "{name} at log_lde {log_lde}: count"
            );
        }
    }
}
