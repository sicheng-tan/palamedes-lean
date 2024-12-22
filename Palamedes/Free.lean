import Aesop
import Palamedes.W

inductive ListF (α β : Type) : Type where
  | nil
  | cons (a : α) (b : β)

inductive TreeF (α β : Type) : Type where
  | leaf
  | node (l : β) (x : α) (r : β)

inductive Tree (α : Type) : Type where
  | leaf
  | node (l : Tree α) (x : α) (r : Tree α)

def foldTree (f : TreeF α β → β) : Tree α → β
  | .leaf => f .leaf
  | .node l x r => f (.node (foldTree f l) x (foldTree f r))

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | choose : (lo : Nat) → (hi : Nat) → lo ≤ hi → Gen Nat
  | sized : (Nat → Gen (Option α)) → Gen α
  | unfoldr : (β → Gen (ListF α β)) → β → Gen (List α)
  | unfoldTree : (β → Gen (TreeF α β)) → β → Gen (Tree α)
  | unfoldW {α γ : Type} {β : α → Type} : (γ → Gen (Σ a : α, β a → γ)) → γ → Gen (W β)

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
