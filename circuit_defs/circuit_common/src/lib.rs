pub const RISC_V_CIRCUIT_DOMAIN_SIZE: usize = 1 << 20;
pub const NUM_PROC_CYCLES_PER_CIRCUIT: usize = RISC_V_CIRCUIT_DOMAIN_SIZE - 1;

use ::field::{Mersenne31Complex, Mersenne31Field};
use fft::*;
use worker::Worker;

pub fn run_for_witness() -> () {
    ()
}

pub fn u32_from_field_elems(src: &[Mersenne31Field; 2]) -> u32 {
    use field::PrimeField;

    let low = u16::try_from(src[0].as_u32_reduced()).expect("read value is not 16 bit long") as u32;
    let high =
        u16::try_from(src[1].as_u32_reduced()).expect("read value is not 16 bit long") as u32;
    low + (high << 16)
}

pub fn u32_into_field_elems(src: u32) -> [Mersenne31Field; 2] {
    let low = src as u16;
    let high = (src >> 16) as u16;

    [Mersenne31Field(low as u32), Mersenne31Field(high as u32)]
}

pub fn create_lde_precomputations<A: GoodAllocator>(
    trace_len: usize,
    lde_factor: usize,
    source_domains: &[usize],
    worker: &Worker,
) -> (Twiddles<Mersenne31Complex, A>, LdePrecomputations<A>) {
    assert!(trace_len.is_power_of_two());

    let twiddles: Twiddles<_, A> = Twiddles::new(trace_len, &worker);
    let lde_precomputations =
        LdePrecomputations::new(trace_len, lde_factor, source_domains, &worker);

    (twiddles, lde_precomputations)
}
