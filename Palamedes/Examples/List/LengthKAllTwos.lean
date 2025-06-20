import Palamedes.Synthesizer

open Gen CorrectGen

-- def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
--   -- generator_search (fun (xs : List Nat) => List.fold (fun x l => l + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true)
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
