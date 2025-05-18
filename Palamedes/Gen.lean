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

/--
Optimizes to remove potentially failing assumptions, when possible.
In some cases (e.g., a pick with a top-level assumption in each generator), it
will only remove the topmost assumption in the first generator, leaving the
assumption in the second.
-/
def optimize : Gen α → Gen α
  | .ret v => .ret v
  | .bind x f => match optimize x with
    | .ret v => optimize (f v)
    | .bind x' g  => sorry
      --.bind x' (λ y => .bind (g y) (λ y => optimize (f y)))
    | .assume b g => .assume b (λ h => .bind (g h) (λ y => optimize (f y)))
    | x' => .bind x' (λ y => optimize (f y))
  | .pick x y => match optimize x, optimize y with
    | .assume b f, y' => if h : b then .pick (f h) y' else y'
    | x', .assume b g => if h : b then .pick x' (g h) else x'
    | x', y' => .pick x' y'
  | .indexed f => .indexed (λ n => optimize (f n))
  | .assume b g => .assume b (λ h => optimize (g h))

def optimize' : Gen α → Gen α
  | .ret v => .ret v
  | .bind x f => optBind (optimize' x) (λ a => optimize' (f a))
  | .pick x y => optPick (optimize' x) (optimize' y)
  | .indexed f => .indexed (λ n => optimize' (f n))
  | .assume b g => .assume b (λ h => optimize' (g h))

-- -- an example that we currently cannot handle
-- def ex : Gen Int := optimize (.pick (.bind (.pick (.ret 2) (.ret 3)) (fun _ => .assume False (fun _ => .ret 3))) (.ret 4))
