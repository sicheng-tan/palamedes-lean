import Aesop

inductive ListF (α β : Type) : Type where
  | nil
  | cons (a : α) (b : β)

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | unfoldr : (β → Gen (ListF α β)) → β → Gen (List α)
  | fail : Gen α

instance [Inhabited α] : Inhabited (Gen α) where
  default := .fail

instance : Monad Gen where
  pure := .ret
  bind := .bind

def pick (x y : Gen α) : Gen α :=
  .bind (.choose 0 1 (by simp)) λ b =>
    if b == 0 then x else y

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  .choose lo hi h

def unfoldr : (β → Gen (ListF α β)) → β → Gen (List α) :=
  .unfoldr
