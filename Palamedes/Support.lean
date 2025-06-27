import Palamedes.Synthesizer -- TODO: Don't just import everything

open Gen

theorem support_assume_pick :
    support (if h : b then pick (x h) y else y) = support (pick (assume b x) y) := by
  aesop

theorem support_pick_assume :
    support (if h : b then pick x (y h) else x) = support (pick x (assume b y)) := by
  aesop

theorem support_assume_bind :
    support (assume b (fun h => x h >>= f)) = support (assume b x >>= f) := by
  aesop

theorem support_pick_bind :
    support (pick (x >>= f) (y >>= f)) = support (pick x y >>= f) := by
  aesop

theorem support_pure_bind :
    support (pure a >>= f) = support (f a) := by
  aesop

theorem support_bind_bind :
    support ((x >>= f) >>= g) = support (x >>= (fun a => f a >>= g)) := by
  aesop

theorem support_bind_congr
    (hx : support x = support x')
    (hf : ∀ {a}, support (f a) = support (f' a)) :
    support (x >>= f) = support (x' >>= f') := by
  aesop

theorem support_pick_congr
    (hx : support x = support x')
    (hy : support y = support y') :
    support (pick x y) = support (pick x' y') := by
  aesop

theorem Term.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Term.unfold f b) = support (Term.unfold f' b) := by
  aesop

theorem Term.support_caseTy_congr
    {unitCase : (τ = .unit) → Gen α}
    {h_unitCase : ∀ {h}, support (unitCase h) = support (unitCase' h)}
    {h_arrowCase : ∀ {τ₁ τ₂ h}, support (arrowCase τ₁ τ₂ h) = support (arrowCase' τ₁ τ₂ h)} :
    support (caseTy τ unitCase arrowCase) = support (caseTy τ unitCase' arrowCase') := by
  aesop

theorem Tree.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Tree.unfold f b) = support (Tree.unfold f' b) := by
  aesop
