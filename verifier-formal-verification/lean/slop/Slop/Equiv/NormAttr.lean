import Lean

/-! `sail_norm`: simp lemmas that put arguments of Sail calls into the form the layer lemmas are stated in
(e.g. `pm_transform_PA (Virtaddr a) 0 = Virtaddr a`, the privilege after reset is `Machine`). -/

register_simp_attr sail_norm
