import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Mathlib.Tactic.Convert

macro "simp_in_proof" : tactic =>
  `(tactic|apply synth_conv (by conv => simp) _)

macro "palamedes" : tactic =>
  `(tactic|aesop (config := {maxRuleApplicationDepth := 0, maxRuleApplications := 0}))

macro "palamedes?" : tactic =>
  `(tactic|aesop? (config := {maxRuleApplicationDepth := 0, maxRuleApplications := 0}))

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
  apply synth_gt,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  (by apply synth_conv (by ext v; conv => rhs; congr; intro a; rw [and_comm]) (synth_bind _ _)),
  (by apply synth_conv (by aesop (config := {maxRuleApplications := 10, maxRuleApplicationDepth := 10, terminal := true})) (synth_pure _)),
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def genTwo : CGen (λ v => v = 2) := by
  palamedes

def genTwo' : CGen (2 = .) := by
  palamedes

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  palamedes

def getMoreThanThree : CGen (λ v => v > 3) := by
  palamedes

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  palamedes

def genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  palamedes

def genTwoAndThree' : CGen (λ (v : Nat × Nat) => ∃ a, ∃ b, a = 2 ∧ b = 3 ∧ v = (a, b)) := by
  palamedes

def genThreeAndTwo : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  palamedes

def genThreeAndTwo' : CGen (λ (v : Int × Int) => ∃ a, ∃ b, b = 3 ∧ a = 2 ∧ v = (a, b)) := by
  palamedes

def genAllTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  palamedes

def genInRange : CGen (λ v => 10 ≤ v ∧ v ≤ 20) := by
  palamedes

def genTwoInRange : CGen (λ (v : Nat × Nat) => 0 ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ 100) := by
  apply synth_tuple
  on_goal 2 =>
    apply synth_between
  on_goal 4 =>
    intro x
    apply synth_between
  on_goal 1 =>
    intro v
    apply Iff.intro
    on_goal 1 =>
      rintro ⟨⟨h1, h2⟩, h3, h4⟩
      apply And.intro
      on_goal 1 =>
        assumption
      on_goal 1 =>
        apply And.intro
        on_goal 2 => assumption
    on_goal 2 =>
      rintro⟨h1, h2, h3⟩
      apply And.intro
      on_goal 1 =>
        apply And.intro
        on_goal 1 => simp
      on_goal 2 =>
        apply And.intro
        on_goal 2 => assumption
  on_goal 2 =>
    exact Nat.le_trans h2 h3
  on_goal 2 =>
    have : id v.fst ≤ v.snd := by assumption
    apply this
  assumption

def genTwoBetweens : CGen (λ (v : Nat × Nat) => ∃ x, (2 ≤ x ∧ x ≤ 6) ∧ ∃ y, (2 ≤ y ∧ y ≤ 100) ∧ v = (x,y)) := by
  -- apply synth_bind
  --   (by apply synth_between) (by
  --   intro x; apply synth_bind (by apply synth_between) (by
  --     intro y; apply synth_pure
  --   )
  --   )
  -- apply synth_bind
  -- apply synth_between
  -- intro x
  -- apply synth_bind
  -- apply synth_between
  -- intro y
  -- apply synth_pure
  -- apply synth_bind
  -- apply synth_between -- once I comment this out search fails
  palamedes?

def genEvenLength [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ b => not b) true v) := by
  palamedes

def genLengthK {k : Nat} [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ len_xs => len_xs + 1) 0 v = k) := by
  palamedes

def genEvenLengthTwos :
    CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  palamedes

def genLengthKTwos (k : Nat) :
    CGen (λ (v : List Nat) =>
      List.foldr (λ _ l => l + 1) 0 v = k ∧
      List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  palamedes

def genIncreasingByOne :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  palamedes

def genTreeIncreasingByOne :
    CGen (λ v =>
      Tree.accuM (λ x _ => (x, x))
                 (λ () x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  palamedes

def genBetween : CGen (λ v => 3 ≤ v ∧ v ≤ 10) := by
  palamedes

def genSortedBetween
    (lo hi : Nat) :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Nat) => do guard (prev ≤ x ∧ x ≤ hi))
                 (λ _ => pure ())
                 v
                 lo = some ()) := by
  palamedes

def isBST (lo hi : Nat) (t : Tree Nat) : Option Unit :=
  Tree.accuM (λ x p => ((p.fst, x - 1), (x + 1, p.snd)))
             (λ () x () => λ (p : Nat × Nat) => do guard (p.fst ≤ x ∧ x ≤ p.snd))
             (λ _ => pure ())
             t
             (lo, hi)

def genBST (lo hi : Nat) : CGen (λ v => isBST lo hi v = some ()) := by
  palamedes

#eval sampleN 10 (genBST 50 100).val
#eval sampleN 10 (.pick (1, 1) (.guardIn False (Decidable.isFalse (by simp)) (λ _ => .ret 2)) (.ret 3))

def main := IO.print =<< sampleN 10 (genSortedBetween 2 10).val
