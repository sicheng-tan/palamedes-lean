import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Palamedes.Opt

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
  (by (conv in _ = _ => rw [eq_comm]); apply synth_pure),
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def genTwo : CGen (λ v => v = 2) := by
  aesop

def genTwo' : CGen (2 = .) := by
  aesop

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  aesop

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  aesop

def genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  apply synth_tuple
  on_goal 3 => {
    intro x
    apply synth_pure
  }
  intro p
  apply Iff.intro
  intro a
  simp_all
  apply And.intro
  on_goal 2 => {rfl
  }
  on_goal 3 => apply synth_pure
  · simp_all only
    rfl
  · intro a
    simp_all only [and_self]

def genTwoAndThree' : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  aesop

def genAllTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop

def genEvenLength [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ b => not b) true v) := by
  aesop

def genLengthK {k : Nat} [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ len_xs => len_xs + 1) 0 v = k) := by
  aesop

def genEvenLengthTwos :
    CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  aesop

def genLengthKTwos {k : Nat} :
    CGen (λ (v : List Nat) =>
      List.foldr (λ _ l => l + 1) 0 v = k ∧
      List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop (add 5% cases Nat)

def genIncreasingByOne :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  aesop

def genTreeIncreasingByOne :
    CGen (λ v =>
      Tree.accuM (λ x _ => (x, x))
                 (λ () x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  aesop

def genBetween : CGen (λ v => 3 ≤ v ∧ v ≤ 10) := by
  aesop

def genSortedBetween
    (lo hi : Nat) :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Nat) => do guard (prev ≤ x ∧ x ≤ hi))
                 (λ _ => pure ())
                 v
                 lo = some ()) := by
  aesop

abbrev genBST
    (lo hi : Nat) :
    CGen (λ v =>
      Tree.accuM (λ x p => ((p.fst, x - 1), (x + 1, p.snd)))
                 (λ () x () => λ (p : Nat × Nat) => do guard (p.fst ≤ x ∧ x ≤ p.snd))
                 (λ _ => pure ())
                 v
                 (lo, hi) = some ()) := by
  aesop

#eval sampleN 10 (optimize (genSortedBetween 2 10).val)
#eval sampleN 10 (optimize (genBST 2 10).val)

def main := IO.print =<< sampleN 10 (genSortedBetween 2 10).val
