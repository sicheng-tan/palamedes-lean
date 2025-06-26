import Palamedes.Synthesizer

open Gen CorrectGen

def isGoodInt : Int → Bool
  | 0 => true
  | 1 => true
  | _ => false

def isGoodAtom : Atom → Bool
  | .atm z _ => isGoodInt z

set_option palamedes.debug true

def genGoodStackFold (n : Nat) : Gen Stack := by
  -- generator_search (λ s => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true)
  let cg : CorrectGen (λ (s : Stack) => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Stack.fold_accu_Option_function_true]
        <;> (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      ) (Stack.s_unfold _)
    sorry
  let g : Gen (Stack) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    sorry -- totality
  exact g
