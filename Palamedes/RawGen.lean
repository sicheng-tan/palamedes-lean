import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | sized : (Nat → Gen (Option α)) → Gen α
  | guardIn : (P : Prop) → Decidable P → (P → Gen α) → Gen α
