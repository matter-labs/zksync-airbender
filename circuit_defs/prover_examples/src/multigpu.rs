use std::{ffi::CStr, thread, time::Duration};

use crossbeam::channel::{unbounded, Receiver, Sender, TryRecvError};
use era_cudart::{
    device::{get_device_count, get_device_properties, set_device},
    result::CudaResult,
};
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext};

use crate::gpu::create_default_prover_context;

#[derive(Debug)]
enum GpuJob {
    ComputeSomething(u32),
    Shutdown,
}

/// Thread that is responsible for running all computation on a single gpu.
pub struct GpuThread {
    pub device_id: i32,
    gpu_thread: Option<Sender<GpuJob>>,
}

impl GpuThread {
    pub fn init_multigpu() -> CudaResult<Vec<GpuThread>> {
        let device_count = get_device_count()?;
        let mut gpu_threads = Vec::with_capacity(device_count as usize);
        for device_id in 0..device_count {
            let gpu_thread = GpuThread::new(device_id)?;
            gpu_threads.push(gpu_thread);
        }

        Ok(gpu_threads)
    }

    pub fn start_multigpu(gpu_threads: &mut Vec<GpuThread>) {
        if !MemPoolProverContext::is_host_allocator_initialized() {
            // allocate 4 x 1 GB ((1 << 8) << 22) of pinned host memory with 4 MB (1 << 22) chunking
            MemPoolProverContext::initialize_host_allocator(4, 1 << 8, 22).unwrap();
        }
        for gpu_thread in gpu_threads.iter_mut() {
            gpu_thread.start();
        }
    }

    /// Creates a new GPU thread.
    pub fn new(device_id: i32) -> CudaResult<Self> {
        //set_device(device_id)?;
        let props = get_device_properties(device_id)?;
        let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
        println!(
            "Device {}: {} ({} SMs, {} GB memory)",
            device_id,
            name,
            props.multiProcessorCount,
            props.totalGlobalMem as f32 / 1024.0 / 1024.0 / 1024.0
        );

        Ok(Self {
            device_id,
            gpu_thread: None,
        })
    }

    pub fn start(&mut self) {
        if self.gpu_thread.is_none() {
            let gpu_thread = Self::spawn_gpu_thread(self.device_id);
            self.gpu_thread = Some(gpu_thread);
        } else {
            println!(
                "GPU thread for device {} is already running.",
                self.device_id
            );
        }
    }

    fn spawn_gpu_thread(device_id: i32) -> Sender<GpuJob> {
        // Create a channel.  We only need Sender in the parent; Receiver moves into the GPU thread.
        let (tx, rx): (Sender<GpuJob>, Receiver<GpuJob>) = unbounded();

        // Spawn the dedicated GPU thread:
        thread::spawn(move || {
            println!("[GPU {}] Initializing GPU context...", device_id);
            set_device(device_id).unwrap();
            let context = create_default_prover_context();

            println!("[GPU {}] GPU context ready.", device_id);
            loop {
                match rx.try_recv() {
                    Ok(job) => match job {
                        GpuJob::ComputeSomething(value) => {
                            println!(
                                "[GPU thread] Got ComputeSomething({}), sending it to GPU ...",
                                value
                            );
                            thread::sleep(Duration::from_millis(50));
                            println!("[GPU thread] Finished ComputeSomething({}).", value);
                        }
                        GpuJob::Shutdown => {
                            println!("[GPU thread] Received Shutdown. Cleaning up and exiting ...");
                            break;
                        }
                    },
                    Err(TryRecvError::Empty) => {
                        // No message right now → just loop again immediately.
                        // We do NOT call `thread::sleep` or `recv()`, because we intentionally want
                        // the thread to stay “busy” (never yield CPU in a blocking wait).
                        continue;
                    }
                    Err(TryRecvError::Disconnected) => {
                        // All senders have been dropped. We will exit.
                        println!("[GPU thread] Channel closed, exiting ...");
                        break;
                    }
                }
            }

            // (Optional) Any final cleanup here before thread exits.
            println!("[GPU {}] Exiting now.", device_id);
        });

        tx
    }
}
