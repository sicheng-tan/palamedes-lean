import Palamedes.Synthesizer

open Gen CorrectGen

def genAllTwosEvenLenFold : Gen (List Nat) := by
  -- generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun x b => !b) true xs = true)
  let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun x b => !b) true xs = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← List.merge_accuM]
      apply and_congr
      . simp_list_predicate
      . simp_list_predicate
    ) (List.s_unfold _)
    intros s b
    replace ⟨s1, s2⟩ := s
    apply caseBool s2
    . intro
      gapply (s_pick _ _)
      . cgenerator_search
      . apply convert (by
          funext
          simp [guard, *, Option.bind_eq_some_iff]
          apply exists_congr; intro; rw [true_and]) (s_bind _ _)
        . cgenerator_search
        . cgenerator_search
    . intro
      apply convert (by
        funext
        simp [guard, *]
        rw [exists_comm]
        apply exists_congr; intro; rw [true_and]
      ) (s_bind _ _)
      . cgenerator_search
      . intro
        apply convert (by
          funext
          simp [guard, *, Option.bind_eq_some_iff]
          rfl) (s_pure _)
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g
