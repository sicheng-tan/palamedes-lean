import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

namespace Gen

@[irreducible]
def arbNat : Gen Nat := indexed go
  where
    go : Nat → Gen (Option Nat)
      | 0 => pure none
      | n + 1 => pick (pure (some 0)) (.map (1 + .) <$> go n)

def gt (lo : Nat) : Gen Nat := (lo + 1 + · ) <$> arbNat

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  if h' : lo = hi then pure lo else pick (pure lo) (choose (lo + 1) hi (by omega))

namespace Gen

@[simp]
theorem support_arbNat :
    support arbNat = fun _ => True := by
  simp [arbNat, arbNat.go]
  funext v
  induction v with
  | zero => simp; exists 1; simp [arbNat, arbNat.go]
  | succ n ih =>
    simp_all
    have ⟨n', hn'⟩ := ih
    exists n' + 1
    simp [arbNat, arbNat.go]
    exists some n
    simp +arith [hn']

@[simp]
theorem support_gt :
    support (gt lo) = fun a => lo < a := by
  simp [gt]
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
def s_arbNat : @CorrectGen Nat (λ _ => True) :=
  Subtype.mk arbNat <| by
    funext v
    simp

@[reducible]
def s_caseNat
    (n : Nat)
    (gz : (n = 0) → CorrectGen P)
    (gs : (n' : Nat) → (n = n' + 1) → CorrectGen P) :
    CorrectGen P :=
    Subtype.mk (if h : n = 0 then gz h else gs n.pred (by simp; omega)) <| by
    match n with
    | 0 => exact (gz _).property
    | n' + 1 => exact (gs _ _).property

@[reducible]
def s_between
    {lo hi : Nat}
    (h : lo ≤ hi) :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (choose lo hi h) <| by
    funext v
    simp

@[reducible]
def s_between_partial
    {lo hi : Nat} :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (assume (lo ≤ hi) (λ h => choose lo hi (by simp_all only [decide_eq_true_eq]))) <| by
    funext v
    simp
    exact Nat.le_trans

@[reducible]
def s_gt
    {lo : Nat} :
    CorrectGen (λ v => lo < v) :=
  Subtype.mk (gt lo) <| by
    simp

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbNat : total arbNat := by
  simp [arbNat]
  apply total_indexed
  intro n
  induction n <;> simp [arbNat.go, *]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_choose : total (choose lo hi h) := by
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

@[simp, aesop safe (rule_sets := [totality])]
theorem total_gt : total (gt lo) := by simp [gt]

end Total

end Gen
