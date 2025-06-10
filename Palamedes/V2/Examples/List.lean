import Palamedes.V2.Synthesizer

open Gen CorrectGen


def genAllTwosFold : Gen (List Nat) := by
  generator_search fun xs => List.fold (fun x b => x == 2 && b) true xs = true

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => !b) true xs = true)

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)

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
--     simp_all
--     apply caseBool (by assumption) <;> intro h
--     . gapply (cpick _ _)
--         . cgenerator_search
--         . sorry
--     . simp_all
--       --gapply (cbind _ _)
--       cgenerator_search
--   let g : Gen (List Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

-- def genLengthKTwosFold (k : Nat) : Gen (List Nat) := by
--   -- generator_search (fun (xs : List Nat) =>
--   --     List.fold (fun _ l => l + 1) 0 v = k ∧
--   --     List.fold (fun x () => guard (x == 2)) () v = Option.some ())
--   sorry


-- -- TODO int
def genIncreasingByOneFold : Gen (List Nat) := by
  -- generator_search (fun xs => List.fold (fun x b prev => x == prev + 1 && b x) (fun x => true) xs 0 = true)
  let cg : CorrectGen (fun xs => List.fold (fun x b prev => x == prev + 1 && b x) (fun x => true) xs 0 = true) := by
    apply convert (by
      funext v
      simp [guard, *]
      rw [← List.fold_accu_Option_function_true]
      intros x acc s
      apply Iff.intro <;> intro h
      . -- (->)
        rw [Bool.and_eq_true] at h
        replace ⟨ h, hacc ⟩ := h
        simp
        apply And.intro
        . apply h
        . apply hacc
      . -- (<-)
        aesop
      ) (List.cunfold _)
    cgenerator_search
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genBetween (lo hi : Nat): Gen Nat := by
    generator_search (fun n => lo ≤ n ∧ n ≤ hi) allow_partial

-- -- -- @[aesop simp (rule_sets := [palamedes])]
-- -- def sortedBetween (hi : Nat) : List Nat → Nat → Bool := λ xs =>
-- --   match xs with
-- --   | [] => λ _ => true
-- --   | x :: xs => λ lo => lo ≤ x && x ≤ hi && (sortedBetween hi xs) x

-- set_option palamedes.debug true

def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  -- generator_search (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun x => true) xs lo = true)
  -- let cg : CorrectGen (fun (xs : List Nat) => List.fold (fun x b s => s ≤ x && x ≤ hi && b x) (fun x => true) xs lo = true) := by

  --   apply convert (by
  --     funext
  --     simp [guard, *]
  --     rw [← List.fold_accu_Option_function_true]
  --     intros x acc s
  --     apply Iff.intro <;> intro h
  --     . rw [Bool.and_eq_true] at h
  --       rw [Bool.and_eq_true] at h
  --       replace ⟨ ⟨ hs, hhi ⟩, h ⟩ := h
  --       aesop
  --     . simp_all
  --       sorry
  --     ) (List.cunfold _)
  --   sorry --cgenerator_search
  -- let g : Gen (List Nat) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   -- totality
  -- exact g
  sorry


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
