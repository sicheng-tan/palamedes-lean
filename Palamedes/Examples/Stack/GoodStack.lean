import Palamedes.Synthesizer

open Gen CorrectGen

def isGoodInt : Int → Bool
  | 0 => true
  | 1 => true
  | _ => false

def isGoodAtom : Atom → Bool
  | .atm z _ => isGoodInt z

@[simp]
def isGoodStack (n : Nat) (s : Stack) : Bool :=
  match s, n with
  | .mty, 0 => true
  | .cons x s, n' + 1 => isGoodAtom x && isGoodStack n' s
  | .ret_cons pc s, n' + 1 => isGoodAtom pc && isGoodStack n' s
  | _, _ => false

def isGoodStackFold (s : Stack) (n : Nat) : Bool :=
  Stack.fold
    (λ s => s == 0)
    (λ x acc s => isGoodAtom x && acc (s - 1))
    (λ pc acc s => isGoodAtom pc && acc (s - 1))
    s
    n

set_option palamedes.debug true

-- def genGoodStackFold (n : Nat) : Gen Stack := by
--   -- generator_search (λ s => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true)
--   let cg : CorrectGen (λ (s : Stack) => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true) := by
--     apply convert (by
--       funext
--       simp [guard, isGoodStackFold, *]
--       rw [← Stack.fold_accu_Option_function]
--       . intros
--         simp_all
--         sorry
--       . sorry
--       ) (Stack.s_unfold _)

--   let g : Gen (Stack) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

-- def genGoodStack (n : Nat) : Gen Stack := by
--   -- generator_search (λ s => isGoodStack s n = true)
--   let cg : CorrectGen (λ s => isGoodStack n s = true) := by
--     apply convert (by
--       funext
--       simp [*]
--       conv => rhs; lhs; apply (Stack.coerce_to_fold (by aesop) (by intros; simp_all; rflm) (by intros; simp_all; rflm))
--       sorry) (Stack.s_unfold _)
--   let g : Gen (Stack) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g
--   sorry
