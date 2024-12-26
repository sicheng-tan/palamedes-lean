import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | sized : (Nat → Gen (Option α)) → Gen α
  | fail : Gen α

instance : Monad Gen where
  pure := .ret
  bind := .bind

def pick (x y : Gen α) : Gen α :=
  .bind (.choose 0 1 (by simp)) λ b =>
    if b == 0 then x else y

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  .choose lo hi h
