use std::sync::Arc;

use cs::definitions::GKRAddress;
use field::{Mersenne31Field as BF, Mersenne31Quartic as E4};
use gpu_gkr_model::storage_layout::handcrafted_layout;

use crate::prover::gkr::GpuGKRStorage;
use crate::prover::test_utils::make_test_context;

#[test]
#[serial_test::serial]
fn consolidated_views_share_backing_and_offset() {
    let context = make_test_context(64, 1);

    let base_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let base_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let ext_a = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let ext_b = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let layout = Arc::new(handcrafted_layout(base_a, base_b, ext_a, ext_b));

    let mut storage: GpuGKRStorage<BF, E4> = GpuGKRStorage::default();
    storage.set_layout(Arc::clone(&layout));

    // Two base views on the same class share backing; offsets differ by
    // exactly `trace_len` elements.
    let view_a = storage.allocate_base_view(0, base_a, &context).unwrap();
    let view_b = storage.allocate_base_view(0, base_b, &context).unwrap();
    assert!(view_a.shares_backing_with(&view_b));
    assert_eq!(view_a.offset(), 0);
    assert_eq!(view_b.offset(), layout.trace_len);
    assert_eq!(view_a.len(), layout.trace_len);
    assert_eq!(view_b.len(), layout.trace_len);
    unsafe {
        assert_eq!(view_a.as_ptr().add(layout.trace_len), view_b.as_ptr());
    }
    // `as_mut_ptr()` reports the same address as `as_ptr()`.
    assert_eq!(view_a.as_ptr() as *mut BF, view_a.as_mut_ptr());
    assert_eq!(view_b.as_ptr() as *mut BF, view_b.as_mut_ptr());

    // Two ext views on the same class share their (separate) backing.
    let ext_view_a = storage.allocate_ext_view(0, ext_a, &context).unwrap();
    let ext_view_b = storage.allocate_ext_view(0, ext_b, &context).unwrap();
    assert!(ext_view_a.shares_backing_with(&ext_view_b));
    assert_eq!(ext_view_a.offset(), 0);
    assert_eq!(ext_view_b.offset(), layout.trace_len);
    unsafe {
        assert_eq!(
            ext_view_a.as_ptr().add(layout.trace_len),
            ext_view_b.as_ptr()
        );
    }

    // Repeat allocations for the same address return views into the same
    // backing (caller is responsible for not aliasing writes; this is
    // the same property that lets circuit_prover keep pointers alive across
    // descriptor builds).
    let view_a_again = storage.allocate_base_view(0, base_a, &context).unwrap();
    assert!(view_a.shares_backing_with(&view_a_again));
    assert_eq!(view_a.offset(), view_a_again.offset());
}

#[test]
#[serial_test::serial]
fn allocate_base_view_panics_when_address_is_ext_typed() {
    let context = make_test_context(64, 1);
    let base_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let base_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let ext_a = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let ext_b = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let layout = Arc::new(handcrafted_layout(base_a, base_b, ext_a, ext_b));

    let mut storage: GpuGKRStorage<BF, E4> = GpuGKRStorage::default();
    storage.set_layout(layout);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        storage.allocate_base_view(0, ext_a, &context).unwrap()
    }));
    assert!(
        result.is_err(),
        "allocate_base_view must panic when called with an ext-typed address"
    );
}
