import Palamedes.Support

/-
Predicate and lemmas for backtracking-free generators.
-/

def total : Gen α → Prop
  | .ret _ => True
  | .pick x y => total x ∧ total y
  | .indexed f => ∀ n, total (f n)
  | .bind x f => total x ∧ ∀ v, v ∈ 〚x〛  → total (f v)
  | .assume b f => (h : b) → total (f h)

theorem total_optBind
    (hx : total x)
    (hf : ∀ {v}, support x v → total (f v)) :
    total (optBind x f) := by
  induction x <;>
    aesop
      (add simp optBind)
      (add simp total)

theorem total_optPick
    (hx : total x)
    (hy : total y) :
    total (optPick x y) := by
  generalize hn : genMeasure x + genMeasure y = n
  induction n generalizing x y
  case zero =>
    cases hx : x with
    | assume b f =>
      by_cases h : b
      . simp_all [optPick]
      . simp_all [optPick]
    | _ =>
      cases hy : y with
      | assume b g =>
        by_cases h' : b
        . simp_all [optPick]
        . simp_all [optPick]
      | _ => aesop (add simp optPick) (add simp total)
  case succ m ih =>
    cases x with
    | assume b f =>
      simp [optPick]
      split
      . simp_all [total]
        apply ih
        . apply hx
          simp
        . apply hy
        . omega
      . simp_all [total]
    | _ =>
      cases hy : y with
      | assume b g =>
        by_cases h' : b
        . subst y
          simp_all [total]
          simp [optPick]
          split
          . try simp [total]
            apply ih
            . simp [total]
              try apply hx
            . apply hy
              simp
            . simp +arith at hn
              subst hn
              simp [genMeasure]
          . contradiction
        . simp_all [optPick]
      | _ => simp_all [optPick]
