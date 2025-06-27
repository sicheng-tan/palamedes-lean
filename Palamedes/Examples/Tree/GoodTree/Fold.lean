import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genGoodTreeFold (n₁ n₂ : Nat) : Gen (Tree Nat) := by
  -- generator_search (fun t => Tree.fold (fun x x x => false) (n₁ == n₂) t = true)
  let cg : CorrectGen (fun (t : Tree Nat) => Tree.fold (fun bl x br => bl && false && br) (n₁ == n₂) t = true) := by
    gapply (Tree.s_unfold _)
    intros b s
    apply caseBool (by assumption) <;> intro h
    . exact (Subtype.mk (assume (n₁ == n₂) (fun _ => pure TreeF.leaf)) <| by simp_all)
    . gapply (s_pick _ _)
      . exact (Subtype.mk (assume (¬n₁ == n₂) (fun _ => pure TreeF.leaf)) <| by simp_all)
      . cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  exact g
