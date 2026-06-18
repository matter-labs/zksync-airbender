use super::*;
use cs::witness_placer::*;
use field::PrimeField;

pub trait WitnessProxy<F: PrimeField, W: WitnessTypeSet<F>>: Sized + Send + Sync {
    fn get_memory_place(&self, idx: usize) -> W::Field;
    fn get_witness_place(&self, idx: usize) -> W::Field;
    fn get_scratch_place(&self, idx: usize) -> W::Field;
    fn get_oracle_value(&self, placeholder: Placeholder, subindex: usize) -> W::Field;

    fn set_memory_place(&mut self, idx: usize, value: W::Field);
    fn set_witness_place(&mut self, idx: usize, value: W::Field);
    fn set_scratch_place(&mut self, idx: usize, value: W::Field);

    #[inline(always)]
    fn get_memory_place_u32(&self, idx: usize) -> W::U32 {
        self.get_memory_place(idx).as_integer()
    }
    #[inline(always)]
    fn get_witness_place_u32(&self, idx: usize) -> W::U32 {
        self.get_witness_place(idx).as_integer()
    }
    #[inline(always)]
    fn get_scratch_place_u32(&self, idx: usize) -> W::U32 {
        self.get_scratch_place(idx).as_integer()
    }
    fn get_oracle_value_u32(&self, placeholder: Placeholder) -> W::U32;

    #[inline(always)]
    fn get_memory_place_u16(&self, idx: usize) -> W::U16 {
        self.get_memory_place_u32(idx).truncate()
    }
    #[inline(always)]
    fn get_witness_place_u16(&self, idx: usize) -> W::U16 {
        self.get_witness_place_u32(idx).truncate()
    }
    #[inline(always)]
    fn get_scratch_place_u16(&self, idx: usize) -> W::U16 {
        self.get_scratch_place_u32(idx).truncate()
    }
    #[inline(always)]
    fn get_oracle_value_u16(&self, placeholder: Placeholder) -> W::U16 {
        self.get_oracle_value_u32(placeholder).truncate()
    }

    #[inline(always)]
    fn get_memory_place_u8(&self, idx: usize) -> W::U8 {
        self.get_memory_place_u16(idx).truncate()
    }
    #[inline(always)]
    fn get_witness_place_u8(&self, idx: usize) -> W::U8 {
        self.get_witness_place_u16(idx).truncate()
    }
    #[inline(always)]
    fn get_scratch_place_u8(&self, idx: usize) -> W::U8 {
        self.get_scratch_place_u16(idx).truncate()
    }
    #[inline(always)]
    fn get_oracle_value_u8(&self, placeholder: Placeholder) -> W::U8 {
        self.get_oracle_value_u16(placeholder).truncate()
    }

    #[inline(always)]
    fn get_memory_place_boolean(&self, idx: usize) -> W::Mask {
        self.get_memory_place(idx).into_mask()
    }
    #[inline(always)]
    fn get_witness_place_boolean(&self, idx: usize) -> W::Mask {
        self.get_witness_place(idx).into_mask()
    }
    #[inline(always)]
    fn get_scratch_place_boolean(&self, idx: usize) -> W::Mask {
        self.get_scratch_place(idx).into_mask()
    }
    #[inline(always)]
    fn get_oracle_value_boolean(&self, placeholder: Placeholder) -> W::Mask {
        self.get_oracle_value(placeholder, 0).into_mask()
    }

    #[inline(always)]
    fn set_memory_place_u32(&mut self, idx: usize, value: W::U32) {
        let value = W::Field::from_integer(value);
        self.set_memory_place(idx, value);
    }
    #[inline(always)]
    fn set_witness_place_u32(&mut self, idx: usize, value: W::U32) {
        let value = W::Field::from_integer(value);
        self.set_witness_place(idx, value);
    }
    #[inline(always)]
    fn set_scratch_place_u32(&mut self, idx: usize, value: W::U32) {
        let value = W::Field::from_integer(value);
        self.set_scratch_place(idx, value);
    }

    #[inline(always)]
    fn set_memory_place_u16(&mut self, idx: usize, value: W::U16) {
        let value = value.widen();
        self.set_memory_place_u32(idx, value);
    }
    #[inline(always)]
    fn set_witness_place_u16(&mut self, idx: usize, value: W::U16) {
        let value = value.widen();
        self.set_witness_place_u32(idx, value);
    }
    #[inline(always)]
    fn set_scratch_place_u16(&mut self, idx: usize, value: W::U16) {
        let value = value.widen();
        self.set_scratch_place_u32(idx, value);
    }

    #[inline(always)]
    fn set_memory_place_u8(&mut self, idx: usize, value: W::U8) {
        let value = value.widen();
        self.set_memory_place_u16(idx, value);
    }
    #[inline(always)]
    fn set_witness_place_u8(&mut self, idx: usize, value: W::U8) {
        let value = value.widen();
        self.set_witness_place_u16(idx, value);
    }
    #[inline(always)]
    fn set_scratch_place_u8(&mut self, idx: usize, value: W::U8) {
        let value = value.widen();
        self.set_scratch_place_u16(idx, value);
    }

    #[inline(always)]
    fn set_memory_place_boolean(&mut self, idx: usize, value: W::Mask) {
        let value = W::Field::from_mask(value);
        self.set_memory_place(idx, value);
    }
    #[inline(always)]
    fn set_witness_place_boolean(&mut self, idx: usize, value: W::Mask) {
        let value = W::Field::from_mask(value);
        self.set_witness_place(idx, value);
    }
    #[inline(always)]
    fn set_scratch_place_boolean(&mut self, idx: usize, value: W::Mask) {
        let value = W::Field::from_mask(value);
        self.set_scratch_place(idx, value);
    }

    // and very thin function for lookup
    fn lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[W::Field; M],
        table_id: W::U16,
        lookup_mapping_idx: usize,
    ) -> [W::Field; N];

    fn maybe_lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[W::Field; M],
        table_id: W::U16,
        condition: W::Mask,
    ) -> [W::Field; N];

    fn lookup_enforce<const M: usize>(
        &mut self,
        inputs: &[W::Field; M],
        table_id: W::U16,
        lookup_mapping_idx: usize,
    );
}
