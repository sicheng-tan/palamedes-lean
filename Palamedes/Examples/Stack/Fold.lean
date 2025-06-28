import Palamedes.Synthesizer

open Gen CorrectGen

namespace GoodStackFold

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

-- set_option palamedes.debug true

def genGoodStackFold (n : Nat) : Gen Stack := by
  -- generator_search (λ s => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true)
  let cg : CorrectGen (λ (s : Stack) => Stack.fold (λ i => i == 0) (λ x acc i => i > 0 && isGoodAtom x && acc (i - 1)) (λ pc acc i => i > 0 && isGoodAtom pc && acc (i - 1)) s n = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Stack.fold_accu_Option_function_true]
        <;> (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      ) (Stack.s_unfold _)
    intros b i
    apply s_caseNat (by assumption)
    . intros h
      gapply (s_pure _)
    . intros i' h
      gapply (s_pick _ _)
      -- apply convert (by
      --   funext
      --   simp only [guard, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
      --     false_and, Nat.zero_lt_succ, decide_true, Bool.true_and, Bool.or_eq_true, beq_iff_eq,
      --     Option.pure_def, --ite_eq_left_iff, /-not_or, imp_false,-/ not_and, Decidable.not_not,
      --     exists_and_left, false_or, eq_iff_iff, h]
      --   ) (s_pick _ _)
      . apply (s_bind _ _)
        . apply convert (by simp [← Decidable.or_iff_not_imp_left]; rfl) _
          cgenerator_search
        . cgenerator_search
      . apply (s_bind _ _)
        . apply convert (by simp [← Decidable.or_iff_not_imp_left]; rfl) _
          cgenerator_search
        . cgenerator_search
  let g : Gen (Stack) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

end GoodStackFold
