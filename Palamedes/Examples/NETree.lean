import Palamedes.Synth
-- import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert

namespace NETree

#set_up_palamedes_simp

@[aesop simp (rule_sets := [palamedes])]
def size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + size l + size r

@[aesop simp (rule_sets := [palamedes])]
def isNETree (t : Tree α) : Bool :=
  size t == 0

def genNETree [Arbitrary α] : CGen (λ (v : Tree α) => isNETree v) := by
  unfold isNETree
  conv => arg 1; intro v; lhs; lhs; apply Tree.coerce_to_fold (by exact rfl) (by intros l x r; simp only [size]; generalize size l = sl; generalize size r = sr; exact rfl)
  -- conv => arg 1; intro v; lhs; lhs; apply Tree.fold_accu_Option_true
  -- palamedes
  sorry
