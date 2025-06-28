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
      (repeat apply duncurry); intro
      (repeat apply duncurry); intro
      (repeat apply duncurry); intro
      (repeat apply duncurry); intro
      (repeat apply duncurry); intro
      rename_i n; apply s_caseNat n
      . cgenerator_search
      . intro
        intro
        rename_i n _; apply s_caseNat n
        . cgenerator_search
        . intro
          intro
          apply convert (by norm_for_bind) (s_bind _ _)
          . cgenerator_search
          . cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  exact g
