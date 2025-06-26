import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)
  -- let cg : CorrectGen (fun xs => List.fold (fun x b => b + 1) 0 xs = k) := by
  --   apply convert (by
  --     funext
  --     simp [guard, *]
  --     simp_list_predicate) (List.s_unfold _)
  -- let g : Gen (List Nat) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  -- exact g
