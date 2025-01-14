import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Palamedes.GuardFree
import Mathlib.Tactic.Convert

attribute [simp]
  guard
  failure
  ite -- NOTE This may be a problem
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
attribute [-simp]
  Prod.forall
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  (by (conv => congr; intro v; rw [eq_comm]); apply synth_pure),
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def isBST_natural (p : Nat × Nat) (t : Tree Nat) : Option Unit :=
  match t with
  | .leaf => pure ()
  | .node l x r => do
    guard (p.fst ≤ x ∧ x ≤ p.snd)
    isBST_natural (p.fst, x - 1) l
    isBST_natural (x + 1, p.snd) r

def isBST_fold (lo hi : Nat) (t : Tree Nat) : Option Unit :=
  Tree.fold (λ fl x fr => λ (p : Nat × Nat) => do
              guard (p.fst ≤ x ∧ x ≤ p.snd)
              fl (p.fst, x - 1)
              fr (x + 1, p.snd))
            (λ _ => pure ())
            t
            (lo, hi)

example : isBST_natural (lo, hi) t = isBST_fold lo hi t := by
  unfold isBST_fold
  delta Tree.fold
  delta isBST_natural
  simp

def isBST (lo hi : Nat) (t : Tree Nat) : Option Unit :=
  Tree.accuM (λ x p => ((p.fst, x - 1), (x + 1, p.snd)))
             (λ () x () => λ (p : Nat × Nat) => do guard (p.fst ≤ x ∧ x ≤ p.snd))
             (λ _ => pure ())
             t
             (lo, hi)

example : isBST_fold lo hi t = isBST lo hi t := by
  unfold isBST
  unfold isBST_fold
  apply fold_accuM
  aesop
    (add simp Option.bind)
    (add unsafe apply fold_accuM)

def genBST (lo hi : Nat) : CGen (λ v => isBST lo hi v = some ()) := by
  aesop

syntax "rw_add_comm" : tactic
macro_rules
  | `(tactic| rw_add_comm) => `(tactic| conv => congr; intro v; congr; intro x; rw [and_comm])

def genBST_explicit (lo hi : Nat) : CGen (λ v => isBST lo hi v = some ()) := by
  apply synth_accuTreeM
  intro b s
  simp_all [TreeF_or]
  apply synth_or
  · apply synth_pure
  · apply synth_bind_arb
    intro ()
    rw_add_comm
    apply synth_bind
    · apply synth_between
    · intro x
      apply synth_bind_arb
      intro ()
      apply synth_pure
