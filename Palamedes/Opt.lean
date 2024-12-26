import Palamedes.Free
import Palamedes.Support

partial def optimize : Gen α → Gen α
  | .bind x f =>
    match optimize x, λ x => optimize (f x) with
    | .ret v, f => f v
    | .bind x g, f => .bind x (λ y => optimize (.bind (g y) f))
    | .guardIn P inst g, f => .guardIn P inst (λ h => optimize (.bind (g h) f))
    | x, f => .bind x f
  | .pick x y =>
    match optimize x, optimize y with
    | .guardIn P _ f, y => if h : P then optimize (.pick (f h) y) else y
    | x, .guardIn P _ f => if h : P then optimize (.pick x (f h)) else x
    | x, y => .pick x y
  | .sized f => .sized (λ x => optimize (f x))
  | .guardIn P inst f => .guardIn P inst (λ h => optimize (f h))
  | x => x

-- def optimize_cgen
--     (g : CGen P) :
--     CGen P := by
--   have ⟨g_val, g_prop⟩ := g
--   exists optimize g_val
--   intro v
--   induction g_val <;> simp_all
--   case sized f ih =>
--     apply Iff.intro
--     . intro ⟨n, h⟩
--       apply (g_prop v).mp
--       exists n

--   case bind => sorry
--   case pick => sorry
