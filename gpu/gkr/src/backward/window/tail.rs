/// Cells of the reduced window tensor, `9 * a0 + 3 * a1 + a2` over
/// `{0, 1, infinity}`, where axis `r` is the variable round `r` binds — i.e.
/// trace-row bit `r`, which is the window executor's `x2` for axis 0.
pub(crate) const WINDOW_TAIL_TENSOR_CELLS: usize = 27;
