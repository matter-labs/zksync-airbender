use crate::forward::isa::DstLine;

pub const BATCH_COEFFICIENT_MAX: u16 = 0x3ffe;
pub const BATCH_COEFFICIENT_ONE: u16 = 0x3fff;

pub fn pack_batch_dst(id: u16) -> Result<DstLine, u16> {
    if id > BATCH_COEFFICIENT_ONE {
        return Err(id);
    }
    Ok(DstLine::GlobalMaterialize {
        slot: (id & 0x000f) as u8,
        col: id >> 4,
    })
}
