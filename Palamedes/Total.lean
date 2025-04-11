import Palamedes.Support

def total : Gen α → Prop
  | .ret _ => True
  | .gt _ => True
  | .pick _ x y => total x ∧ total y
  | .choose _ _ _ => True
  | .sized f => ∀ n, total (f n)
  | .bind x f => total x ∧ ∀ v, v ∈ 〚x〛  → total (f v)
  | .guardIn P _ f => ∃ h : P, total (f h)

theorem total_optBind
    (hx : total x)
    (hf : ∀ {v}, support x v → total (f v)) :
    total (optBind x f) := by
  induction x <;>
    aesop
      (add simp optBind)
      (add simp total)
