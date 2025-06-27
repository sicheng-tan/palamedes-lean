import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwos

@[simp]
def recAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && recAllTwos xs

set_option palamedes.debug true

def genLengthKAllTwos (k : Nat): Gen (List Nat) := by
  -- generator_search (fun xs => (decide (xs.length = k) && recAllTwos xs) = true)
  let cg : CorrectGen (fun xs => (decide (xs.length = k) && recAllTwos xs) = true) := by
    -- NOTE: this is exactly the same as the fold version
    apply convert (by
      funext
      simp [guard, *]
      rw [← List.merge_accuM]
      apply and_congr
      . simp_list_predicate
      . simp_list_predicate
    ) (List.s_unfold _)
    intros b s
    replace ⟨ n , () ⟩ := b
    apply caseNat (by assumption)
    . intros
      apply convert (by
        funext
        simp [guard, *, Option.bind_eq_some]
        rfl) (s_pure _)
    . intros
      apply convert (by
        funext
        simp [guard, *, Option.bind_eq_some, and_assoc]
        apply exists_congr
        intro
        rw [true_and]
        ) (s_bind _ _)
      . cgenerator_search
      . cgenerator_search
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

end LengthKAllTwos
