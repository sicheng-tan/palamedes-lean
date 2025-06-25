import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

-- def genCompleteTreeFold (n : Nat) : Gen (Tree Nat) := by
--   -- generator_search (fun t => Tree.fold (fun bl x br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n = true)
--   let cg : CorrectGen (fun (t : Tree Nat) => Tree.fold (fun bl x br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n = true) := by
--     apply convert (by
--       funext
--       simp [guard, *]
--       rw [← Tree.fold_accu_Option_function_true] <;> try (intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop) )
--       (Tree.s_unfold _)
--     intros
--     apply (caseBool (by assumption))
--     . cgenerator_search
--     . intros
--       gapply (s_pure _)
--   let g : Gen (Tree Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

@[simp]
def isCompleteTree : Tree α → Nat → Bool := λ t n =>
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isCompleteTree l (n - 1) &&
    isCompleteTree r (n - 1)

-- def genCompleteTree (n : Nat) : Gen (Tree Nat) := by
--   generator_search (fun t => isCompleteTree t n = true)
