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
      norm_for_Stack_unfold
      -- funext
      -- simp_predicate
      -- rw [← Stack.fold_accu_Option_function_true]
      --   <;> (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      ) (Stack.s_unfold _)
    intros b i
    -- rename_i n
    -- apply s_caseNat n
    apply s_caseNat (by assumption)
    . cgenerator_search
    . cgenerator_search
  let g : Gen (Stack) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

end GoodStackFold
