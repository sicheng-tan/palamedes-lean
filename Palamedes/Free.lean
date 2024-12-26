import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | sized : (Nat → Gen (Option α)) → Gen α
  | guardIn : (P : Prop) → Decidable P → (P → Gen α) → Gen α

instance : Monad Gen where
  pure := .ret
  bind := .bind

def pick (x y : Gen α) : Gen α := .pick x y

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  .choose lo hi h
