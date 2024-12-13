import Palamedes
import Palamedes.Free
import Palamedes.Support
import Palamedes.Synth

def genTwoOrThree : Gen Int := do
  let b ← choose 0 1
  if b == 0 then pure 2 else pure 3

example {x : Int} : support genTwoOrThree x ↔ (x = 2 ∨ x = 3) := by
  simp
  apply Iff.intro
  . rintro ⟨v', hv', hsup⟩
    match v' with
    | 0 => simp at hsup; left; simpa
    | 1 => simp at hsup; right; simpa
  . intro hx
    match hx with
    | .inl hx => exists 0
    | .inr hx => exists 1

def genAllTwos : Gen (List Int) :=
  unfoldr (λ () =>
    pick
      (pure .nil)
      (pure (.cons 2 ())))
    ()

example {xs : List Int} : support genAllTwos xs ↔ (∀ x ∈ xs, x = 2) := by
  induction xs with
  | nil => simp; exists 0
  | cons x xs ih =>
    simp at *
    apply Iff.intro
    . rintro ⟨b', ⟨v', hv'⟩, h_unfoldr⟩
      apply And.intro
      . match v' with
        | 0 => simp at hv'
        | 1 => simp at hv'; assumption
      . intro x' hx'
        match v' with
        | 0 => simp at hv'
        | 1 => exact ih.mp h_unfoldr _ hx'
    . simp at *
      intro hx hxs
      exists ()
      apply And.intro
      . exists 1; simpa
      . exact ih.mpr hxs

-- Actual Synthesis Demo

def two : CGen (λ v => v = 2) := by
  aesop

def two' : CGen (2 = .) := by
  aesop

def twoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  aesop

def twoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  aesop

attribute [simp] guard in
attribute [-simp] Prod.forall in -- FIXME: See if we can avoid this
def allTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop (add safe apply synth_match)

def lengthK {k : Nat} :
    @CGen (List Unit) (λ v => List.foldrM (λ _ len_xs => pure (len_xs + 1)) 0 v = Option.some k) := by
  aesop (config := { warnOnNonterminal := false })
  match b with
  | 0 => exists pure .nil; aesop
  | n + 1 => exists pure (.cons () n); aesop

example :
  List.foldrM (λ _ len_xs => pure (len_xs + 1)) 0 xs = Option.some n ↔
  xs.length = n := by
  have always_some :
      List.foldrM (λ _ len_xs => pure (len_xs + 1)) 0 xs = Option.some n
      ↔ List.foldr (λ _ len_xs => len_xs + 1) 0 xs = n := by
    induction xs generalizing n with
    | nil => aesop
    | cons x xs ih =>
      simp [Option.bind, pure]
      have := (@ih (List.foldr (fun x len_xs => len_xs + 1) 0 xs)).mpr (by simp)
      simp [pure] at this
      rw [this]
      simp
  rw [always_some]
  clear always_some
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp_all only [List.foldr_cons, List.length_cons]
    apply Iff.intro
    · intro h
      subst h
      simp_all only [Nat.add_right_cancel_iff]
      have := (@ih xs.length).mpr
      simp at this
      exact (Eq.symm this)
    · intro h
      subst h
      simp_all only [Nat.add_right_cancel_iff]

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
