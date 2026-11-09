use std::panic::{catch_unwind, AssertUnwindSafe};

use gpu_gkr_compiler::MainContinuationWindowShape;

use crate::proth120::backward::main_continuation::{
    publication_shape_pr, resolve_pr_main_continuation_kernel, MainContinuationSequencePr,
};
use crate::proth120::backward::main_continuation_window_manifest::{
    PR_MAIN_CONTINUATION_MASKS, PR_MAIN_CONTINUATION_WINDOW_KERNELS,
};

fn panic_message(result: std::thread::Result<()>) -> String {
    let payload = result.expect_err("expected a named panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
        .expect("panic payload is text")
}

#[test]
fn pr_continuation_mask_dispatch_panics_by_name() {
    let manifest_masks: Vec<u8> = PR_MAIN_CONTINUATION_WINDOW_KERNELS
        .iter()
        .map(|entry| entry.mask)
        .collect();
    assert_eq!(manifest_masks, PR_MAIN_CONTINUATION_MASKS);
    assert_eq!(
        PR_MAIN_CONTINUATION_MASKS,
        gpu_gkr_compiler::PR_MAIN_CONTINUATION_MASKS
    );
    assert!(PR_MAIN_CONTINUATION_MASKS
        .windows(2)
        .all(|pair| pair[0] < pair[1]));
    assert!(PR_MAIN_CONTINUATION_MASKS.iter().all(|mask| *mask <= 0x1f));
    for &mask in PR_MAIN_CONTINUATION_MASKS {
        assert_eq!(
            resolve_pr_main_continuation_kernel(u16::from(mask)).mask,
            mask
        );
    }

    let programs = super::super::cpu_abi::programs();
    let folding_steps = programs.runtime_circuit.trace_len.trailing_zeros() as usize;
    assert_eq!(folding_steps, 21);
    let layer_masks: Vec<u16> = programs
        .main_continuation_window
        .iter()
        .map(|program| program.shape.bits())
        .collect();
    assert_eq!(layer_masks, [0x1f, 0x07, 0x07, 0x03, 0x01]);
    for (layer, program) in programs.main_continuation_window.iter().enumerate() {
        assert_eq!(
            u16::from(resolve_pr_main_continuation_kernel(program.shape.bits()).mask),
            program.shape.bits()
        );
        let sequence = MainContinuationSequencePr::new(program, layer, folding_steps);
        assert_eq!(sequence.window_count(), 4);
        assert_eq!(sequence.tail_start_round(), 15);
    }

    let unsupported = (0u16..=0x1f)
        .filter(|mask| {
            u8::try_from(*mask).is_ok_and(|mask| !PR_MAIN_CONTINUATION_MASKS.contains(&mask))
        })
        .chain([0x20, 0xff, 0x100, u16::MAX]);
    for mask in unsupported {
        let message = panic_message(catch_unwind(|| {
            resolve_pr_main_continuation_kernel(mask);
        }));
        assert!(
            message.contains("Proth120 main continuation")
                && message.contains(&format!("{mask:#04x}")),
            "mask {mask:#04x}: {message}"
        );
    }

    let mut forged = programs.main_continuation_window[0].clone();
    forged.shape = MainContinuationWindowShape::GROUPED;
    let message = panic_message(catch_unwind(AssertUnwindSafe(|| {
        MainContinuationSequencePr::new(&forged, 0, folding_steps);
    })));
    assert!(
        message.contains("Proth120 main continuation has no kernel for mask 0x02"),
        "{message}"
    );

    let message = panic_message(catch_unwind(AssertUnwindSafe(|| {
        MainContinuationSequencePr::new(&programs.main_continuation_window[4], 4, 9);
    })));
    assert!(
        message.contains("Proth120 main continuation requires at least one window pass"),
        "{message}"
    );

    let program = &programs.main_continuation_window[0];
    let tiles: Vec<usize> = [3, 6, 9, 12]
        .into_iter()
        .map(|start| {
            let (shape, row_tiles) = publication_shape_pr(program, folding_steps, start).unwrap();
            assert_eq!(shape.columns, program.sources.len());
            assert_eq!(shape.column_elems, 8 << (18 - start));
            row_tiles
        })
        .collect();
    assert_eq!(tiles, [1024, 128, 16, 2]);
}
