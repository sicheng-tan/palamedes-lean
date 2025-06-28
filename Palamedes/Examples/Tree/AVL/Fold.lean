import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

set_option palamedes.debug true

namespace AVLFold

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
   -- generator_search (fun t =>
  -- Tree.fold (fun bl x br h => decide (h > 0) && bl (h - 1) && br (h - 1)) (fun h => decide (h ≤ 1)) t height = true ∧
  --   Tree.fold
  --       (fun bl x br bounds =>
  --         match bounds with
  --         | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr) && bl (sl, x - 1) && br (x + 1, sr))
  --       (fun x => true) t (lo, hi) =
  --     true)
  let cg : CorrectGen (fun (t : Tree Nat) =>
      Tree.fold
          (fun bl x br bounds =>
            match bounds with
            | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr) && bl (sl, x - 1) && br (x + 1, sr))
          (fun x => true) t (lo, hi) =
        true ∧
        Tree.fold (fun bl x br h => decide (h > 0) && bl (h - 1) && br (h - 1)) (fun h => decide (h ≤ 1)) t height = true) := by
      apply convert (by
        funext
        simp [guard, *]
        rw [← Tree.merge_accuM]
        apply and_congr
        . simp_tree_predicate
        . simp_tree_predicate
        ) (Tree.s_unfold _)
      intros b s
      replace ⟨ ⟨ low, high ⟩ , h ⟩ := s
      apply caseNat (by assumption)
      . intro h'
        cgenerator_search
      . intros n' h'
        apply caseNat (by assumption)
        . intros
          gapply (s_pick _ _)
          . cgenerator_search
          . cgenerator_search
        . intros n''
          intros h''
          apply convert (by
            funext
            simp [guard, Option.bind_eq_some_iff, *]
            rfl
            ) (s_bind _ _)
          . cgenerator_search
          . cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  exact g
