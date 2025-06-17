import Palamedes.V2.Synthesizer

open Gen CorrectGen

-- def genAllTwosFold : Gen (List Nat) := by
--   generator_search fun xs => List.fold (fun x b => x == 2 && b) true xs = true

-- def genTrueFold : Gen (List Nat) := by
--   generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

-- def genEvenLenFold : Gen (List Nat) := by
--   generator_search (fun (xs : List Nat) => List.fold (fun x b => !b) true xs = true)

-- def genLengthKFold {k : Nat} : Gen (List Nat) := by
--   generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)

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
--     apply caseBool (by assumption) <;> intro h
--     . gapply (cpick _ _)
--       . cgenerator_search
--       . gapply (cbind _ _) --?
--         . cgenerator_search
--         . intro x
--           replace ⟨ x, _ ⟩ := x
--           gapply (cbind _ _)
--           . cgenerator_search
--           . intro y
--             replace ⟨ (), _ ⟩ := y
--             generalize hbx : (x == 2) = bx
--             apply (caseBool (by assumption)) <;> intro h
--             . rw [h, Nat.beq_eq_true_eq] at hbx
--               cgenerator_search
--             . rw [h] at hbx
--               simp_all only [beq_eq_false_iff_ne, ne_eq, ite_false, Option.bind, Eq.symm, Option.some_ne_none]
--               -- cgenerator_search
--               --simp only [bind, failure, Option.bind]
--               sorry
--     . simp_all
--       gapply (cbind _ _)
--       . cgenerator_search
--       . intro y
--         replace ⟨ y, _ ⟩ := y
--         simp_all
--         generalize hb : (y == 2) = b
--         apply (caseBool (by assumption)) <;> intro h <;> simp_all
--         . cgenerator_search
--         . sorry
--   all_goals sorry


  -- let g : Gen (List Nat) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  -- exact g

-- def genLengthKTwosFold (k : Nat) : Gen (List Nat) := by
--   -- generator_search (fun (xs : List Nat) =>
--   --     List.fold (fun _ l => l + 1) 0 v = k ∧
--   --     List.fold (fun x () => guard (x == 2)) () v = Option.some ())
--   sorry


-- set_option palamedes.debug true

def genIncreasingByOneFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b prev => x == prev + 1 && b x) (fun x => true) xs 0 = true)

-- def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
--   generator_search
--     (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun x => true) xs lo = true)
--     allow_partial

    -- apply convert (by
    --   first
    --   | funext
    --     simp [guard, *]
    --     first
    --       | exact Eq.comm
    --       | (first
    --         | rw [← List.fold_accu_Option_true]; (try aesop); done
    --         | rw [← List.fold_accu_Option_function]; (try aesop); done
    --         | rw [← List.fold_accu_Option_function_true]; (try aesop); done
    --         | rw [← List.fold_accu_Option_basic]; (try aesop); done)
    --       | apply exists_congr; intro; rw [true_and]
    --       | rfl
    --   | rfl) (List.cunfold _)

-- set_option palamedes.debug true

-- add_aesop_rules unsafe (rule_sets := [synthesis]) [
--   (by fail_if_no_progress intros),
--   (by assumption),
--   (by gapply (cpure _)),
--   (by gapply (cpick _ _)),
--   (by gapply (cbind _ _)),
--   (by gapply (List.cunfold _)),
--   (by gapply carbUnit),
--   (by gapply carbBool),
--   (by gapply carbNat),
--   (by gapply cgt),
--   (by gapply cbetween_partial),
--   (by gapply (cbetween (by first | aesop | omega))),
-- ]

-- add_aesop_rules 5% (rule_sets := [synthesis]) [
--   (by apply caseBool (by assumption)),
--   (by apply caseNat (by assumption))
-- ]
