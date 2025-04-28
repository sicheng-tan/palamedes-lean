import Aesop

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | indexed : (Nat → Gen (Option α)) → Gen α
  | assume : (b : Bool) → (b → Gen α) → Gen α
