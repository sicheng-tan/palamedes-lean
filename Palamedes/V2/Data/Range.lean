import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.Data.Arbitrary

namespace Gen

def gt (lo : Nat) : Gen Nat := (lo + 1 + · ) <$> (Arbitrary.arbitrary.val : Gen Nat)

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  if h' : lo = hi then pure lo else pick (pure lo) (choose (lo + 1) hi (by omega))

namespace Gen

@[simp]
theorem support_gt :
    support (gt lo) = fun a => lo < a := by
  simp [gt]
  rw [Arbitrary.arbitrary.property]
  funext a
  simp
  apply Iff.intro
  . omega
  . intro h
    induction h with
    | refl => simp
    | step a ih =>
      have ⟨x, hx⟩ := ih
      exists x + 1
      omega

@[simp]
theorem support_choose :
    support (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  generalize hn : hi - lo = n
  funext v
  induction n generalizing lo hi v with
  | zero =>
    unfold choose
    split <;> simp <;> omega
  | succ n' ih =>
    unfold choose
    split
    . simp
      omega
    . simp
      apply Iff.intro
      . intro hv
        cases hv with
        | inl hv => simp_all
        | inr hv =>
          have h : hi - (lo + 1) = n' := by omega
          rw [ih h] at hv
          omega
      . intro hbw
        by_cases v = lo
        . left; assumption
        . right
          rw [ih _] <;> omega

end Gen

namespace CorrectGen

@[reducible]
def cbetween
    {lo hi : Nat}
    (h : lo ≤ hi) :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (choose lo hi h) <| by
    funext v
    simp

@[reducible]
def cbetween_partial
    {lo hi : Nat} :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (assume (lo ≤ hi) (λ h => choose lo hi (by simp_all only [decide_eq_true_eq]))) <| by
    funext v
    simp
    exact Nat.le_trans

@[reducible]
def cgt
    {lo : Nat} :
    CorrectGen (λ v => lo < v) :=
  Subtype.mk (gt lo) <| by
    simp

end CorrectGen

namespace Total

@[simp]
def total_choose : total (choose lo hi h) := by
  generalize hn : hi - lo = n
  induction n generalizing lo hi h with
  | zero =>
    unfold choose
    have : lo = hi := by omega
    simp [this]
  | succ n' ih =>
    unfold choose
    split
    . simp
    . apply total_pick
      . simp
      . apply ih
        omega

@[simp]
def total_gt : total (gt lo) := by simp [gt]

end Total

end Gen
