import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert

/-
Simple examples using palamedes.
-/

#set_up_palamedes_simp

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

@[aesop simp (rule_sets := [palamedes])]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x == 2 && allTwos xs

def genAllTwos : CGen (λ v => allTwos v = true) := by
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
  palamedes

@[aesop simp (rule_sets := [palamedes])]
def evenLength : List α → Bool
  | [] => true
  | _ :: xs => not (evenLength xs)

def genEvenLength [Arbitrary α] :
    CGen (λ (v : List α) => evenLength v = true) := by
  palamedes

def genLengthK {k : Nat} [Arbitrary α] :
    CGen (λ (v : List α) => List.length v = k) := by
  palamedes

def genEvenLengthTwos :
    CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  palamedes

def genLengthKTwos (k : Nat) :
    CGen (λ (v : List Nat) =>
      List.foldr (λ _ l => l + 1) 0 v = k ∧
      List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  palamedes

@[aesop simp (rule_sets := [palamedes])]
def increasingByOne : List Int → Int → Bool := λ xs prev =>
  match xs with
  | [] => true
  | x :: xs => x == prev + 1 && increasingByOne xs x

def genIncreasingByOne : CGen (λ (v : List Int) => increasingByOne v 0) := by
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

@[aesop simp (rule_sets := [palamedes])]
def sortedBetween (hi : Nat) : List Nat → Nat → Bool := λ xs lo =>
  match xs with
  | [] => true
  | x :: xs => lo ≤ x && x ≤ hi && sortedBetween hi xs x

def genSortedBetween
    (lo hi : Nat) :
    CGen (λ v => sortedBetween hi v lo = true) := by
  palamedes
