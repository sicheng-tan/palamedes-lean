import Palamedes.Free
import Palamedes.Support

def optBind : Gen α → (α → Gen β) → Gen β
  | .ret v, f => f v
  | .bind x g, f => .bind x (λ y => optBind (g y) f)
  | .guardIn P inst g, f => .guardIn P inst (λ h => optBind (g h) f)
  | x, f => .bind x f

@[simp]
def genMeasure : Gen α → Nat
  | .guardIn P _ f => if hp : P then 1 + genMeasure (f hp) else 0
  | _ => 0

def optPick : Gen α → Gen α → Gen α
  | .guardIn P _ f, y => if h : P then optPick (f h) y else y
  | x, .guardIn Q _ g => if h : Q then optPick x (g h) else x
  | x, y => .pick x y
  termination_by x y => genMeasure x + genMeasure y
  decreasing_by
    . by_cases P
      . simp_all [ite]
      . contradiction
    . by_cases Q
      . simp_all [ite]
      . contradiction

def optimize : Gen α → Gen α
  | .bind x f => optBind (optimize x) (λ x => optimize (f x))
  | .pick x y => optPick (optimize x) (optimize y)
  | .sized f => .sized (λ x => optimize (f x))
  | .guardIn P inst f => .guardIn P inst (λ h => optimize (f h))
  | x => x

theorem optPick_pick (x y : Gen α) : support (.pick x y) = support (optPick x y) := by
  generalize hn : genMeasure x + genMeasure y = n
  induction n generalizing x y
  case zero =>
    cases hx : x with
    | guardIn P _ f =>
      by_cases h : P
      . simp_all [optPick]
      . simp_all [optPick]
        funext v
        simp_all only [eq_iff_iff, or_iff_right_iff_imp, forall_exists_index, forall_false]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
        . simp_all [optPick]
        . simp_all [optPick]
          funext x
          rename_i h_1 a_1
          simp_all only [eq_iff_iff, or_iff_left_iff_imp, forall_exists_index, forall_false]
      | _ => simp_all [optPick]
  case succ m ih =>
    cases x with
    | guardIn P _ f =>
      by_cases h : P
      . simp_all [optPick]
        rw [← ih]
        conv at hn =>
          lhs
          rw [Nat.add_assoc]
          rw [Nat.add_comm]
        simp at hn
        exact hn
      . simp_all [optPick]
        funext v
        simp_all only [eq_iff_iff, or_iff_right_iff_imp, forall_exists_index, forall_false]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
        . simp_all [optPick]
          conv at hn => lhs; rw [Nat.add_comm]
          simp_all
          subst hn
          rw [← ih]
          . simp_all [genMeasure]
          . simp_all [genMeasure]
        . simp_all [optPick]
      | _ => simp_all [optPick]

theorem optBind_bind : support (.bind x f) = support (optBind x f) := by
  funext v
  induction x generalizing v <;> simp_all [optBind]
  case bind x g ih1 ih2 =>
    apply Iff.intro
    . intro ⟨v', ⟨a, ha, hv'⟩, h⟩
      apply (ih1 _).mp
      exists a
      apply And.intro ha
      apply (ih2 _ _).mp
      exists v'
    . intro h
      have ⟨a, ha, hv⟩ := (ih1 _).mpr h
      have ⟨v', hv', hfv'⟩ := (ih2 _ _).mpr hv
      exists v'
      apply (And.intro . hfv')
      exists a
  case guardIn P _ g ih =>
    apply Iff.intro
    . intro ⟨v', ⟨a, ha⟩, h⟩
      exists a
      apply (ih _ _).mp
      exists v'
    . intro ⟨a, ha⟩
      have ⟨v', hv', hfv'⟩ := (ih _ _).mpr ha
      exists v'
      simp_all only [exists_const, and_self]
