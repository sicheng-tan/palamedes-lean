import Palamedes.Free
import Palamedes.Support

def optBind : Gen α → (α → Gen β) → Gen β
  | .ret v, f => f v
  | .bind x g, f => .bind x (λ y => optBind (g y) f)
  | .guardIn P inst g, f => .guardIn P inst (λ h => optBind (g h) f)
  | x, f => .bind x f

partial def optPick : Gen α → Gen α → Gen α
  | .guardIn P _ f, y => if h : P then optPick (f h) y else y
  | x, .guardIn P _ f => if h : P then optPick x (f h) else x
  | x, y => .pick x y

partial def optimize : Gen α → Gen α
  | .bind x f => optBind (optimize x) (λ x => optimize (f x))
  | .pick x y => optPick (optimize x) (optimize y)
  | .sized f => .sized (λ x => optimize (f x))
  | .guardIn P inst f => .guardIn P inst (λ h => optimize (f h))
  | x => x

-- TODO: Prove that this terminates and that `optimize` maintains correctness
