import Slop.ISA.Equiv.Walk

/-! The configuration facts `walk_decoder` reads (Sail's decoder asks which extensions are enabled, and a few
clauses read the privilege), each evaluated once in the kernel. The walk finds them by name
(`Slop.Equiv.Known.<constructor>`, `knownFact?`); without them it evaluates them again in every walk, ~0.3 s each
(`currentlyEnabled` is well-founded recursion). -/

open Sail SailRV32 SailRV32.Functions

namespace Slop.Equiv.Known

theorem Ext_Zihintpause : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zihintpause) = some true := by
  decide +kernel
theorem Ext_Zicfilp : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zicfilp) = some false := by
  decide +kernel
theorem Ext_Zimop : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zimop) = some true := by
  decide +kernel
theorem Ext_M : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_M) = some true := by
  decide +kernel
theorem Ext_Zicsr : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zicsr) = some true := by
  decide +kernel
theorem Ext_Zmmul : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zmmul) = some true := by
  decide +kernel
theorem Ext_Zicfiss : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zicfiss) = some false := by
  decide +kernel
theorem Ext_Svinval : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Svinval) = some true := by
  decide +kernel
theorem Ext_S : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_S) = some false := by
  decide +kernel
theorem Ext_H : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_H) = some false := by
  decide +kernel
theorem Ext_Zihintntl : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zihintntl) = some false := by
  decide +kernel
theorem Ext_Zicbop : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zicbop) = some false := by
  decide +kernel
theorem Ext_Zbkb : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zbkb) = some true := by
  decide +kernel
theorem Ext_Zbb : runOracle knownDemo (fun _ => none) (currentlyEnabled .Ext_Zbb) = some false := by
  decide +kernel

theorem cur_privilege : runOracle knownDemo (fun _ => none) (readReg Register.cur_privilege) = some .Machine :=
  some_of_idx _ privilege_idx_inj (by decide +kernel)

end Slop.Equiv.Known
