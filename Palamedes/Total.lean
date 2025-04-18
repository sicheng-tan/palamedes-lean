import Palamedes.Support

def total : Gen α → Prop
  | .ret _ => True
  | .pick _ x y => total x ∧ total y
  | .sized f => ∀ n, total (f n)
  | .bind x f => total x ∧ ∀ v, v ∈ 〚x〛  → total (f v)
  | .guardIn P _ f => (h : P) → total (f h)

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
    total (optPick w x y) := by
  generalize hn : genMeasure x + genMeasure y = n
  induction n generalizing x y w
  case zero =>
    cases hx : x with
    | guardIn P _ f =>
      by_cases h : P
      . simp_all [optPick]
      . simp_all [optPick]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
        . simp_all [optPick]
        . simp_all [optPick]
      | _ => aesop (add simp optPick) (add simp total)
  case succ m ih =>
    cases x with
    | guardIn P _ f =>
      simp [optPick]
      split
      . simp_all [total]
        apply ih
        . apply hx
          simp
        . apply hy
        . simp_arith at hn
          exact hn
      . simp_all [total]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
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
            . simp_arith at hn
              subst hn
              simp [genMeasure]
          . contradiction
        . simp_all [optPick]
      | _ => simp_all [optPick]
