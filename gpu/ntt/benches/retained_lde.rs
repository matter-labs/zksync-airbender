//! Diagnostic comparison of equivalent full-LDE and retained-M transform work.
//! Run one shape per process under the shared GPU lock. No hashing, arena fit,
//! or proof-time claim is made by this benchmark.
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::nvtx::{end_range, start_range};
use gpu_ntt::ntt::{
    hypercube_evals_to_monomials, hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20,
    hypercube_to_multi_coset_bitrev_evals_fused, hypercube_to_retained_monomials_and_coset,
    natural_monomials_to_bitreversed_evals_multi_coset, retained_monomials_to_coset,
    RetainedLdeOptions,
};
use gpu_ntt::ntt_twiddles::DeviceContext;

#[derive(Clone, Copy)]
enum Arm {
    Full,
    Retained(RetainedLdeOptions),
}
const ARMS: [(&str, Arm); 5] = [
    ("full", Arm::Full),
    (
        "cached_prefetch",
        Arm::Retained(RetainedLdeOptions {
            stream_first_coset_stores: false,
            prefetch_next_monomial_column: true,
        }),
    ),
    (
        "cached_no_prefetch",
        Arm::Retained(RetainedLdeOptions {
            stream_first_coset_stores: false,
            prefetch_next_monomial_column: false,
        }),
    ),
    (
        "streamed_prefetch",
        Arm::Retained(RetainedLdeOptions {
            stream_first_coset_stores: true,
            prefetch_next_monomial_column: true,
        }),
    ),
    (
        "streamed_no_prefetch",
        Arm::Retained(RetainedLdeOptions {
            stream_first_coset_stores: true,
            prefetch_next_monomial_column: false,
        }),
    ),
];

struct Harness {
    context: DeviceContext,
    stream: CudaStream,
    properties: DeviceProperties,
    log_n: usize,
    log_f: usize,
    columns: usize,
    raw: DeviceAllocation<BF>,
    monomials: DeviceAllocation<BF>,
    coset: DeviceAllocation<BF>,
    full: DeviceAllocation<BF>,
    scratch: DeviceAllocation<BF>,
}

impl Harness {
    fn new(log_n: usize, log_f: usize, columns: usize, force_two: bool) -> Self {
        assert!((20..=24).contains(&log_n));
        assert!((1..=3).contains(&log_f));
        assert!(columns > 0);
        assert!(!force_two || log_n >= 23);
        let context = DeviceContext::create(13).unwrap();
        let stream = CudaStream::create().unwrap();
        let mut properties = DeviceProperties::new().unwrap();
        if force_two {
            properties.l2_cache_size_bytes = 16 << 20;
        }
        let n = 1usize << log_n;
        let len = n * columns;
        let mut raw = DeviceAllocation::alloc(len).unwrap();
        let host = (0..len)
            .map(|i| BF::new((i as u32).wrapping_mul(2654435761).wrapping_add(71)))
            .collect::<Vec<_>>();
        memory_copy_async(&mut raw, &host[..], &stream).unwrap();
        stream.synchronize().unwrap();
        Self {
            context,
            stream,
            properties,
            log_n,
            log_f,
            columns,
            raw,
            monomials: DeviceAllocation::alloc(len).unwrap(),
            coset: DeviceAllocation::alloc(len).unwrap(),
            full: DeviceAllocation::alloc(len << log_f).unwrap(),
            scratch: DeviceAllocation::alloc(n).unwrap(),
        }
    }

    fn sample(&self, values: &era_cudart::slice::DeviceSlice<BF>, coset: usize, host: &mut [BF]) {
        let n = 1usize << self.log_n;
        for column in 0..self.columns {
            let slot = (coset * self.columns + column) * 2;
            memory_copy_async(
                &mut host[slot..slot + 1],
                &values[column * n..column * n + 1],
                &self.stream,
            )
            .unwrap();
            memory_copy_async(
                &mut host[slot + 1..slot + 2],
                &values[(column + 1) * n - 1..(column + 1) * n],
                &self.stream,
            )
            .unwrap();
        }
    }

    fn run(&mut self, arm: Arm, mut coverage: Option<&mut [BF]>) {
        let n = 1usize << self.log_n;
        let len = n * self.columns;
        let f = 1usize << self.log_f;
        match arm {
            Arm::Full => {
                let mut finest = false;
                for column in 0..self.columns {
                    let offset = column * n;
                    let input = &self.raw[offset..offset + n];
                    if self.log_n == 20 {
                        hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20(
                            input,
                            &mut self.scratch,
                            &mut self.full[offset..],
                            self.log_f,
                            self.columns,
                            &self.stream,
                            &self.properties,
                        )
                        .unwrap();
                        continue;
                    }
                    let next = (column + 1 < self.columns)
                        .then(|| unsafe { self.raw.as_ptr().add(offset + n) });
                    if hypercube_to_multi_coset_bitrev_evals_fused(
                        input,
                        &mut self.full[offset..],
                        self.log_n,
                        self.log_f,
                        self.columns,
                        finest,
                        next,
                        &self.stream,
                        &self.properties,
                    )
                    .unwrap()
                    {
                        finest = next.is_some();
                    } else {
                        finest = false;
                        hypercube_evals_to_monomials(
                            input,
                            &mut self.scratch,
                            self.log_n,
                            false,
                            &self.stream,
                            &self.properties,
                        )
                        .unwrap();
                        natural_monomials_to_bitreversed_evals_multi_coset(
                            &self.scratch[..],
                            &mut self.full[offset..],
                            self.log_n,
                            self.log_f,
                            self.columns,
                            false,
                            &self.context,
                            None,
                            &self.stream,
                            &self.properties,
                        )
                        .unwrap();
                    }
                }
                if let Some(host) = coverage.as_deref_mut() {
                    for coset in 0..f {
                        self.sample(&self.full[coset * len..(coset + 1) * len], coset, host);
                    }
                }
            }
            Arm::Retained(options) => {
                hypercube_to_retained_monomials_and_coset(
                    &self.raw,
                    &mut self.monomials,
                    &mut self.coset,
                    self.log_n,
                    self.log_f,
                    1,
                    options,
                    &self.properties,
                    &self.stream,
                )
                .unwrap();
                if let Some(host) = coverage.as_deref_mut() {
                    self.sample(&self.coset, 1, host);
                }
                for coset in (0..f).filter(|c| *c != 1) {
                    retained_monomials_to_coset(
                        &self.monomials,
                        &mut self.coset,
                        self.log_n,
                        self.log_f,
                        coset,
                        options,
                        &self.properties,
                        &self.stream,
                    )
                    .unwrap();
                    if let Some(host) = coverage.as_deref_mut() {
                        self.sample(&self.coset, coset, host);
                    }
                }
            }
        }
    }
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    assert!(
        (3..=4).contains(&args.len()),
        "usage: retained_lde LOG_N LOG_F COLUMNS [two-pass]"
    );
    let log_n = args[0].parse().unwrap();
    let log_f = args[1].parse().unwrap();
    let columns = args[2].parse().unwrap();
    let force_two = args.get(3).is_some_and(|v| {
        assert_eq!(v, "two-pass");
        true
    });
    let mut h = Harness::new(log_n, log_f, columns, force_two);
    let profile_only = std::env::var_os("AB_RETAINED_LDE_PROFILE").is_some();
    let measurement_rounds = if profile_only { 1 } else { 10 };
    println!("{{\"kind\":\"protocol\",\"scope\":\"transform-only\",\"log_n\":{log_n},\"log_f\":{log_f},\"columns\":{columns},\"forced_two_pass\":{force_two},\"l2_dispatch_bytes\":{},\"warmup_rounds\":2,\"rounds\":{measurement_rounds},\"profile_only\":{profile_only},\"iterations\":3}}", h.properties.l2_cache_size_bytes);
    let mut expected = vec![BF::new(0); 2 * columns * (1usize << log_f)];
    h.run(Arm::Full, Some(&mut expected));
    h.stream.synchronize().unwrap();
    for &(name, arm) in &ARMS[1..] {
        let mut actual = vec![BF::new(123); expected.len()];
        h.run(arm, Some(&mut actual));
        h.stream.synchronize().unwrap();
        assert_eq!(actual, expected, "coverage mismatch: {name}");
    }
    println!("{{\"kind\":\"coverage\",\"cosets\":{},\"columns\":{columns},\"sampled_rows_per_column\":2,\"passed\":true}}", 1usize << log_f);
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    // A profiler capture uses the same warmup, then one diagnostic round.
    // Ten rotations, alternating direction, put each arm in each position twice.
    for round in 0..if profile_only { 3 } else { 12 } {
        let capture = (profile_only && round == 2)
            .then(|| start_range(Some("gpu_ntt.bench"), "bench.retained_lde.measure"));
        for position in 0..ARMS.len() {
            let index = if round % 2 == 0 {
                (round + position) % ARMS.len()
            } else {
                (round + ARMS.len() - 1 - position) % ARMS.len()
            };
            let (name, arm) = ARMS[index];
            let arm_range = capture.map(|_| start_range(Some("gpu_ntt.bench"), name));
            start.record(&h.stream).unwrap();
            let host_start = std::time::Instant::now();
            for _ in 0..3 {
                h.run(arm, None);
            }
            let schedule_ms = host_start.elapsed().as_secs_f64() * 1000.0 / 3.0;
            end.record(&h.stream).unwrap();
            h.stream.synchronize().unwrap();
            let gpu_ms = elapsed_time(&start, &end).unwrap() / 3.0;
            if let Some(range) = arm_range {
                end_range(range);
            }
            println!("{{\"kind\":\"sample\",\"warmup\":{},\"round\":{round},\"arm\":\"{name}\",\"gpu_ms\":{gpu_ms},\"schedule_ms\":{schedule_ms}}}", round<2);
        }
        if let Some(range) = capture {
            end_range(range);
        }
    }
}
