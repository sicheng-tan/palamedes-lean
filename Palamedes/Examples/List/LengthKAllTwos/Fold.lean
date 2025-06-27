import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
  -- generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true)
  let cg : CorrectGen (fun xs => List.fold (fun x b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true) := by
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













--   let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x l => l + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true) := by
--     apply convert (by
--       funext
--       simp [guard, *]
--       rw [List.fold_accu_Option_basic] <;> try (aesop; done)
--       rw [List.fold_accu_Option_true] <;> try (aesop; done)
--       rw [List.merge_accuM]
--     ) (List.cunfold _)
--     intros n s
--     replace ⟨ n, () ⟩ := n
--     apply caseNat (by assumption)
--     . intro h
--       rw [h]
--       apply convert (by
--         funext
--         simp [guard, Option.bind_eq_some, *]
--         rfl
--         ) (cpure _)
--     . intro n' h
--       rw [h]
--       apply convert (by
--         funext
--         simp [guard, Option.bind_eq_some, *] -- TODO here
--         sorry) (cbind _ _)
--       sorry
--   let g : Gen (List Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g
