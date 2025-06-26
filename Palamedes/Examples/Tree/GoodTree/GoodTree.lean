import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genGoodTreeFold (n₁ n₂ : Nat) : Gen (Tree Nat) := by
  -- generator_search (fun t => Tree.fold (fun x x x => false) (n₁ == n₂) t = true)
  let cg : CorrectGen (fun t => Tree.fold (fun x x x => false) (n₁ == n₂) t = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Tree.fold_accu_Option_basic]; aesop) (Tree.s_unfold _)
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

-- def isGoodTree (n₁ n₂ : Nat) : Tree α → Bool
--   | .leaf => n₁ == n₂
--   | .node _ _ _ => false

-- def recGoodTree (n₁ n₂ : Nat) : Tree α → Bool
--   | .leaf => n₁ == n₂
--   | .node l _ r => false && recGoodTree n₁ n₂ l && recGoodTree n₁ n₂ r

-- def genGoodTreeRec (n₁ n₂ : Nat) : Gen (Tree Nat) := by
--   generator_search (λ (t : Tree Nat) => recGoodTree n₁ n₂ t) allow_partial

-- def genGoodTree (n₁ n₂ : Nat) : Gen (Tree Nat) := by
  -- generator_search (λ (t : Tree Nat) => isGoodTreetv n₁ n₂) allow_partial
  -- sorry
