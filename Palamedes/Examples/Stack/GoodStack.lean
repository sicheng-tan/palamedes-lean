import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def isGoodInt : Int → Bool
  | 0 => true
  | 1 => true
  | _ => false

@[simp]
def isGoodAtom : Atom → Bool
  | .atm z _ => isGoodInt z

@[simp]
def isGoodStack (n : Nat) (s : Stack) : Bool :=
  match s, n with
  | .mty, 0 => true
  | .cons x s, n' + 1 => isGoodAtom x && isGoodStack n' s
  | .ret_cons pc s, n' + 1 => isGoodAtom pc && isGoodStack n' s
  | _, _ => false

set_option palamedes.debug true

-- def genGoodStack (n : Nat) : Gen Stack := by
--   -- generator_search (fun s => isGoodStack s n = true)
--   let cg : CorrectGen (fun s => isGoodStack n s = true) := by
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
