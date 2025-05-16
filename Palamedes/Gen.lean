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
    | .bind x' g  => .bind x' (λ y => .bind (g y) (λ y => optimize (f y)))
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

-- theorem optimize_bind' (x : Gen α) (y : Gen β) (f : α -> Gen β) :
--   optimize y = x.bind f -> ∃ g : α -> Gen β, f = λ z => optimize (g z) := by
--   induction y generalizing x α <;> try (intros <;> contradiction)
--   case bind γ τ y g IH1 IH2 =>
--     generalize Hy : optimize y = y'
--     cases y' <;> intro H
--     case ret v =>
--       unfold optimize at H
--       rw [Hy] at H
--       simp at H
--       apply IH2 v x f H
--     case bind τ2 y2 g2 =>
--       -- apply IH1
--       sorry
--     case pick =>
--       sorry
--     case indexed =>
--       sorry
--     case assume =>
--       sorry
--   all_goals sorry

-- theorem optimize_bind (v : α1) (x : Gen α1) (y : Gen β) (f : α1 -> Gen β) (g : β -> Gen γ1) :
--   optimize y = x.bind f -> (f v).bind h = optBind (f v) h := by
--   induction y generalizing x <;> try (intros <;> contradiction)
--   case bind γ2 α2 β1 x2 f2 H1 IH2 =>
--     generalize Hx2 : optimize x2 = x2' at *
--     cases x2'
--     case ret v2 =>
--       unfold optimize
--       rw [Hx2]
--       apply (IH2 v2 x f) g
--     case bind α3 x3 f3 =>
--       unfold optimize
--       rw [Hx2]
--       simp
--       intros
--       -- apply IH2
--       sorry
--     case pick y1 y2 =>
--       sorry
--     case indexed fn =>
--       sorry
--     case assume b fb =>
--       sorry
--   case pick γ2 β1 y1 y2 IH1 IH2 =>
--     sorry

-- theorem optimize_assume (b : Bool) (v : b = true) (y : Gen β) (f : b = true -> Gen β) (g : β -> Gen γ) :
--   optimize y = Gen.assume b f -> (f v).bind h = optBind (f v) h := by
--   induction y generalizing b <;> try (intros <;> contradiction)
--   case bind =>
--     sorry
--   case pick =>
--     sorry
--   case assume =>
--     sorry


-- theorem optimize_pickR (b : Bool) (Hb : b = true) (x y : Gen β) (f : b = true -> Gen β) :
--   optimize x = Gen.assume b f -> y.pick (f Hb) = optPick y (f Hb) := by
--   induction y generalizing b Hb
--   case ret =>
--     sorry
--   case bind =>
--     sorry
--   case pick =>
--     sorry
--   case indexed =>
--     sorry
--   case assume =>
--     sorry


-- theorem optimize_pickL (b : Bool) (Hb : b = true) (x y : Gen β) (f : b = true -> Gen β) :
--   optimize x = Gen.assume b f -> (f Hb).pick y = optPick (f Hb) y := by
--   induction y generalizing b Hb
--   case ret =>
--     sorry
--   case bind =>
--     sorry
--   case pick =>
--     sorry
--   case indexed =>
--     sorry
--   case assume =>
--     sorry

-- theorem optimize_optimize' (g : Gen α) : optimize g = optimize' g := by
--   induction g <;> simp_all [optBind, optPick, optimize, optimize']
--   . case bind β γ x f IHx IHf =>
--     generalize IHx' : optimize' x = xOpt at *
--     cases xOpt <;> unfold optBind <;> simp
--     case bind α x' g =>
--       funext v1
--       apply (optimize_bind v1 x' x g (fun v => optimize' (f v))) <;> simp_all
--     case assume b g =>
--       funext Hb
--       apply (optimize_assume b Hb x g (fun v => optimize' (f v))) <;> simp_all
--   . case pick β x y IHx IHy =>
--       generalize Hx : optimize' x = xOpt at *
--       generalize Hy : optimize' y = yOpt at *
--       cases xOpt <;> cases yOpt <;> unfold optPick <;> simp
--       case ret.assume v b f =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickR b Hb y (Gen.ret v) f <;> simp_all
--       case bind.assume γ g' f b fb =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickR b Hb y (g'.bind f) fb <;> simp_all
--       case pick.assume g1 g2 b f =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickR b Hb y (g1.pick g2) f <;> simp_all
--       case indexed.assume f b fb =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickR b Hb y (Gen.indexed f) fb <;> simp_all
--       case assume.ret b f v =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickL b Hb x (Gen.ret v) f <;> simp_all
--       case assume.bind b fb γ g' f =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickL b Hb x (g'.bind f) fb <;> simp_all
--       case assume.pick b f g1 g2 =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickL b Hb x (g1.pick g2) f <;> simp_all
--       case assume.indexed b fb f =>
--         by_cases Hb : b = true <;> simp_all
--         apply optimize_pickL b Hb x (Gen.indexed f) fb <;> simp_all
--       case assume.assume b1 fb1 b2 fb2 =>
--         by_cases Hb : b1 = true <;> simp_all
--         apply optimize_pickL b1 Hb x (Gen.assume b2 fb2) fb1 <;> simp_all

-- -- an example that we currently cannot handle
-- def ex : Gen Int := optimize (.pick (.bind (.pick (.ret 2) (.ret 3)) (fun _ => .assume False (fun _ => .ret 3))) (.ret 4))
