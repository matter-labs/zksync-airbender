use super::*;

use crate::prover_stages::stage1::compute_wide_ldes;
use crate::prover_stages::stage1::compute_wide_ldes_row_major;
use rand::rngs::StdRng;
use rand::SeedableRng;
use trace_holder::RowMajorTrace;

#[test]
fn test_compute_wide_lde() {
    if cfg!(target_feature = "avx512f") {
        println!("avx512f is enabled");
    }
    let trace_len: usize = 1 << 21;
    // let log_n = trace_len.trailing_zeros();
    let num_cores = 16;
    let worker = Worker::new_with_num_threads(num_cores);
    let lde_factor = 2;

    let mut input = vec![Mersenne31Complex::ONE; trace_len];

    let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF);
    for i in 0..input.len() {
        input[i] = Mersenne31Complex::random_element(&mut rng);
    }

    //ref
    let num_columns = 256;

    let trace = RowMajorTrace::<Mersenne31Field, 32, _>::new_zeroed_for_size(
        trace_len,
        num_columns,
        Global,
    );

    let twiddles = Twiddles::<Mersenne31Complex, Global>::new(trace_len, &worker);
    let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);

    // copy to the trace
    let mut row_view = trace.row_view(0..trace_len);
    for i in 0..trace_len {
        let row = row_view.current_row();
        for pair in row.chunks_mut(2) {
            pair[0] = input[i].c0;
            pair[1] = input[i].c1;
        }
        // row[0] = input[i].c0;
        // row[1] = input[i].c1;
        row_view.advance_row()
    }

    let trace_test = trace.clone();
    let source_domain_index = 0;

    let mut timer = Timer::new();

    let row_major_ldes = compute_wide_ldes_row_major(
        trace,
        &twiddles,
        &lde_precomputations,
        source_domain_index,
        lde_factor,
        &worker,
    );

    timer.measure_running_time("perform row major lde");

    //test
    let grinded_ldes = compute_wide_ldes(
        trace_test,
        &twiddles,
        &lde_precomputations,
        source_domain_index,
        lde_factor,
        &worker,
    );

    timer.measure_running_time("perform grinded lde");

    //check
    let mut row_view_ref = row_major_ldes[0].trace.row_view(0..trace_len);
    let mut row_view_test = grinded_ldes[0].trace.row_view(0..trace_len);
    for row_idx in 0..trace_len {
        let row_ref = row_view_ref.current_row_ref();
        let row_test = row_view_test.current_row_ref();
        assert_eq!(row_test[0], row_ref[0], "c0 failed at row {}", row_idx);
        assert_eq!(row_test[1], row_ref[1], "c1 failed at row {}", row_idx);
        row_view_ref.advance_row();
        row_view_test.advance_row();
    }

    let mut row_view_ref = row_major_ldes[1].trace.row_view(0..trace_len);
    let mut row_view_test = grinded_ldes[1].trace.row_view(0..trace_len);
    for row_idx in 0..trace_len {
        let row_ref = row_view_ref.current_row_ref();
        let row_test = row_view_test.current_row_ref();
        assert_eq!(row_test[0], row_ref[0], "c0 failed at row {}", row_idx);
        assert_eq!(row_test[1], row_ref[1], "c1 failed at row {}", row_idx);
        row_view_ref.advance_row();
        row_view_test.advance_row();
    }
}
