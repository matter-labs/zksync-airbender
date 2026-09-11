//! A WHIR-side poly that is folded by LSB steps through a PAIR of pooled
//! buffers: every fold reads the current buffer and writes the other one
//! (half the length), so there is no in-place pair pass followed by a serial
//! strided compaction. The buffers come from the [`AllocationPool`] and go
//! back to it in [`PingPongPoly::release`].

use crate::allocation_pool::{AllocationPool, Buffer, ColumnLayout};
use crate::gkr::prover::gkr_backend::GKRBackend;
use field::{Field, FieldExtension, PrimeField};
use worker::Worker;

pub struct PingPongPoly<E> {
    bufs: [Buffer<E>; 2],
    /// which buffer holds the poly
    cur: usize,
    len: usize,
}

impl<E: Field> PingPongPoly<E> {
    /// Two pooled buffers of `len` and `len / 2` elements (the second is the
    /// target of the first fold; both keep their capacity for later folds).
    /// The poly is written by `fill` into the first one.
    pub fn new_ext<F: PrimeField>(
        len: usize,
        pool: &dyn AllocationPool<F, E>,
        fill: impl FnOnce(&mut [core::mem::MaybeUninit<E>]),
    ) -> Self
    where
        E: FieldExtension<F>,
    {
        assert!(len.is_power_of_two());
        let mut a = pool.alloc_ext(len, ColumnLayout::Contiguous);
        let b = pool.alloc_ext((len / 2).max(1), ColumnLayout::Contiguous);
        fill(a.as_mut());
        Self {
            bufs: [a, b],
            cur: 0,
            len,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }
    #[inline(always)]
    pub fn as_slice(&self) -> &[E] {
        // SAFETY: the first `len` elements of the current buffer are the poly
        // (written by `fill` or by the last fold)
        unsafe { &self.bufs[self.cur].as_ref_assume_init()[..self.len] }
    }
    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [E] {
        let len = self.len;
        unsafe { &mut self.bufs[self.cur].as_mut_assume_init()[..len] }
    }

    /// One LSB folding step through the backend's kernel; the result lives
    /// in the other buffer.
    pub fn fold<F: PrimeField, GB: GKRBackend<F, E>>(
        &mut self,
        challenge: &E,
        gkr_backend: &GB,
        worker: &Worker,
    ) where
        E: FieldExtension<F>,
    {
        let half = self.len / 2;
        assert!(half > 0, "cannot fold a single element");
        let (src, dst) = {
            let [a, b] = &mut self.bufs;
            if self.cur == 0 {
                (a, b)
            } else {
                (b, a)
            }
        };
        assert!(dst.len() >= half);
        let src_slice: &[E] = unsafe { &src.as_ref_assume_init()[..half * 2] };
        gkr_backend.fold_eq_poly_into(src_slice, challenge, &mut dst.as_mut()[..half], worker);
        self.cur ^= 1;
        self.len = half;
    }

    /// Give both buffers back to the pool.
    pub fn release<F: PrimeField>(self, pool: &dyn AllocationPool<F, E>)
    where
        E: FieldExtension<F>,
    {
        let [a, b] = self.bufs;
        pool.give_ext(a);
        pool.give_ext(b);
    }
}
