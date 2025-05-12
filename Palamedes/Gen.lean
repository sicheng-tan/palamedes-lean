import Palamedes.RawGen

/-
Smart constructors to remove unnecessary `assume`s.
-/

/--
Smart constructor for bind.
-/
def optBind : Gen α → (α → Gen β) → Gen β
  | .ret v, f => f v
  | .bind x g, f => .bind x (λ y => optBind (g y) f)
  | .assume b g, f => .assume b (λ h => optBind (g h) f)
  | x, f => .bind x f

/--
Monad instance for generators.
-/
instance : Monad Gen where
  pure := .ret
  bind := optBind

/--
Number of provable assumptions in a generator, for proving termination.
-/
@[simp]
def genMeasure : Gen α → Nat
  | .assume b f => if h : b then 1 + genMeasure (f h) else 0
  | _ => 0

/--
Smart constructor for pick.
-/
def optPick : Gen α → Gen α → Gen α
  | .assume b f, y => if h : b then optPick (f h) y else y
  | x, .assume b g => if h : b then optPick x (g h) else x
  | x, y => .pick x y
  termination_by x y => genMeasure x + genMeasure y
  decreasing_by
    . by_cases b
      . simp_all [ite]
      . contradiction
    . by_cases b
      . simp_all [ite]
      . contradiction

def pick (x y : Gen α) : Gen α := optPick x y
