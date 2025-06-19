import Palamedes.Synthesizer

open Gen CorrectGen

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true)

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => !b) true xs = true)

def genIncreasingByOneFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b prev => x == prev + 1 && b x) (fun x => true) xs 0 = true)

-- def genSortedBetweenFold (lo hi : Nat) : Gen (List Nat) := by
--   generator_search
--     (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun x => true) xs lo = true)
--     allow_partial

-- set_option palamedes.debug true
-- set_option pp.proofs true

-- def genEvenLenTwosFold : Gen (List Nat) := by
--   -- generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun x b => !b) true xs = true)
--   let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun x b => !b) true xs = true) := by
--     apply convert (by
--       funext
--       simp [guard, *]
--       rw [List.fold_accu_Option_true] <;> try (aesop; done)
--       rw [List.fold_accu_Option_basic] <;> try (aesop; done)
--       rw [List.merge_accuM]
--     ) (List.cunfold _)
--     intros b s
--     replace ⟨ (), b ⟩ := b
    -- simp only [Option.bind_eq_bind, Option.some_bind, Option.some.injEq,
--     --   Prod.mk.injEq, Option.bind_eq_some, Option.guard_eq_some, true_and]
--     apply caseBool (by assumption) <;> intro h <;> rw [h]
--     . gapply (cpick _ _)
--       . cgenerator_search
--       . apply convert (by
--           funext
--           -- TODO here
--           simp only [Option.bind_eq_bind, Option.some_bind, Option.some.injEq, Prod.mk.injEq,
--           Bool.true_eq_false, and_false, false_and, guard, beq_iff_eq, Option.pure_def,
--           Option.bind_eq_some, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
--           Bool.not_eq_eq_eq_not, Bool.not_false, true_and, exists_const, Prod.exists,
--           Bool.exists_bool, Bool.false_eq_true, and_true, false_or, or_false, exists_and_left]
--           rfl
--           ) (cbind _ _)
--         . cgenerator_search
--         . cgenerator_search
--     . apply convert (by
--         funext
--         -- TODO here
--         simp only [Option.bind_eq_bind, Option.some_bind, Option.some.injEq, Prod.mk.injEq,
--         Bool.true_eq_false, and_false, false_and, guard, beq_iff_eq, Option.pure_def,

--         Option.bind_eq_some, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
--         Bool.not_eq_eq_eq_not, Bool.not_false, true_and, exists_const,
--         Prod.exists, Bool.exists_bool,
--         Bool.false_eq_true, and_true, false_or, exists_and_left, eq_iff_iff]
--         rfl
--         ) (cbind _ _)
--       . cgenerator_search
--       . cgenerator_search
--   let g : Gen (List Nat) := by
--       optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     sorry
--   let _ : Gen.total g := by
--     sorry
--   exact g

-- def genLengthKTwosFold (k : Nat) : Gen (List Nat) := by
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
