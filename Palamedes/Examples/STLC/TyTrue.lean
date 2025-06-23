
import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def arbTy : Gen Ty := by sorry
  -- generator_search (fun v => Ty.fold (fun x x => true) true v = true)
  -- let cg : CorrectGen (fun v => Ty.fold (fun x x => true) true v = true) := by
  --   gapply (Ty.s_unfold)
  -- let g : Gen (Ty) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  -- exact g
