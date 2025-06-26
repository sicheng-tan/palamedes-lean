import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

-- def recGoodTree (n₁ n₂ : Nat) : Tree α → Bool
--   | .leaf => n₁ == n₂
--   | .node l _ r => false && recGoodTree n₁ n₂ l && recGoodTree n₁ n₂ r

-- def genGoodTreeRec (n₁ n₂ : Nat) : Gen (Tree Nat) := by
--   generator_search (fun (t : Tree Nat) => recGoodTree n₁ n₂ t) allow_partial

-- def isGoodTree (n₁ n₂ : Nat) : Tree α → Bool
--   | .leaf => n₁ == n₂
--   | .node _ _ _ => false

-- def genGoodTree (n₁ n₂ : Nat) : Gen (Tree Nat) := by
  -- generator_search (fun (t : Tree Nat) => isGoodTreetv n₁ n₂) allow_partial
  -- sorry
