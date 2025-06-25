import Palamedes.CorrectGen

namespace Gen

def total : Gen α → Prop
  | .ret _ => True
  | .pick x y => total x ∧ total y
  | .indexed f => ∀ n, total (f n)
  | .bind x f => total x ∧ ∀ v, v ∈ 〚x〛  → total (f v)
  | .assume b f => ∃ (h : b), total (f h)

namespace Total

@[simp]
theorem total_pure :
    total (pure a) := by
  simp [pure, total]

@[simp]
theorem total_bind
    (hx : total x)
    (hf : ∀ {v}, v ∈ 〚x〛 → total (f v)) :
    total (x >>= f) := by
  simp_all [bind, total]

@[simp]
theorem total_pick
    (hx : total x)
    (hy : total y) :
    total (pick x y) := by
  simp_all [pick, total]

@[simp]
theorem total_assume
    {b : Bool}
    {f : b → Gen α}
    (hf : ∃ h, total (f h)) :
    total (assume b f) := by
  simp_all [assume, total]

@[simp]
theorem total_indexed
    (hf : ∀ n, total (f n)) :
    total (indexed f) := by
  simp_all [indexed, total]

@[simp]
theorem total_map
    (hx : total x) :
    total (f <$> x) := by
  simp_all [total]

@[simp]
theorem total_internalizeProofs (h : total g) : total (internalizeProofs g):= by
  induction g <;> simp_all [internalizeProofs, total]
  case assume b f ihf =>
    have ⟨h, ht⟩ := h
    simp_all [internalizeProofs, total]

@[simp]
theorem total_dite
    {g₁ : b = true → Gen α}
    {g₂ : ¬ (b = true) → Gen α}
    (h₁ : (h : b = true) → total (g₁ h))
    (h₂ : (h : ¬(b = true)) → total (g₂ h))
    : total (if h : b then g₁ h else g₂ h) := by
  sorry

end Total

end Gen
