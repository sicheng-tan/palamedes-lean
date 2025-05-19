import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Total
import Mathlib.Tactic.Convert

namespace TotalExperiment

#set_up_palamedes_simp

@[aesop simp]
def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

def genBST (lo hi : Nat) : CGen (λ v => isBST v ⟨lo, hi⟩) := by
  -- TODO: Turn coercions into ones that use synth_conv
  apply synth_conv (by ext v; rw [Tree.coerce_to_accuM (by aesop) (by aesop)]) _
  apply synth_accuTreeM
  intro b s
  -- TODO: Replace Aesop's simplification with simplification within synth_conv
  apply synth_conv (by simp; exact rfl) _
  apply synth_or
  · apply synth_pure -- TODO: Again, allow Aesop to do this kind of simplification
  · apply synth_conv (by ext v; congr!; rw [true_and]) (synth_bind _ _)
    . apply Arbitrary.arbitrary
    . intro a
      apply synth_conv (by ext v; conv => rhs; congr; intro a; rw [and_comm]) (synth_bind _ _)
      · apply synth_between
      · intro a_1
        apply synth_conv (by ext v; congr!; rw [true_and]) (synth_bind _ _)
        . apply Arbitrary.arbitrary
        . intro a_1
          apply synth_pure

add_aesop_rules unsafe [
  total_optBind,
  total_optPick,
  total_unfoldTree,
  total_choose,
  total_internalizeProofs,
  (by simp [total])
]

example {lo hi : Nat} : total (genBST lo hi).val := by
  simp [genBST, total, pick, bind, Functor.map, CGen.internalizeProofs, Gen.internalizeProofs]
  aesop
