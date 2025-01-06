import Palamedes.Support

@[simp]
def guardFree : Gen α → Prop
  | .ret _ => True
  | .choose _ _ _ => True
  | .guardIn _ _ _ => False
  | .sized f => ∀ n, guardFree (f n)
  | .pick x y => guardFree x ∧ guardFree y
  | .bind x f => guardFree x ∧ ∀ a, guardFree (f a)
