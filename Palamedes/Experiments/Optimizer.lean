import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Total

abbrev OptGen (g : Gen α) : Type 1 := {g' // support g = support g'}

abbrev optimized_ret : OptGen (.ret v) :=
  Subtype.mk (.ret v) <| by rfl

abbrev optimized_ret_bind (h : OptGen (f v)) : OptGen (.bind (.ret v) f) :=
  Subtype.mk h.val <| by
    simp [h.property]

abbrev optimized_pick_congr
    (hx : OptGen x)
    (hy : OptGen y) :
    OptGen (.pick x y) :=
  Subtype.mk (.pick hx.val hy.val) <| by
    simp [hx.property, hy.property, total]

abbrev optimized_pick_assume
    {b : Bool}
    {y : Gen α}
    {f : b → Gen α}
    (hf : ∀ (h : b), OptGen (f h))
    (hy : OptGen y) :
    OptGen (.pick (.assume b f) y) :=
  Subtype.mk (if h : b then .pick (hf h).val hy.val else hy.val) <| by
    split
    . rename_i hb
      subst hb
      simp [hy.property, (hf rfl).property, true_and, total]
    . aesop

abbrev optimized_assume_pick
    {b : Bool}
    {x : Gen α}
    {f : b → Gen α}
    (hf : ∀ (h : b), OptGen (f h))
    (hx : OptGen x) :
    OptGen (.pick x (.assume b f)) :=
  Subtype.mk (if h : b then .pick hx.val (hf h).val else hx.val) <| by
    split
    . rename_i hb
      subst hb
      simp [hx.property, (hf rfl).property, true_and, total]
    . aesop

abbrev optimized_assume_bind
    (h : OptGen (.assume b (λ h => .bind (f h) g))) :
    OptGen (.bind (.assume b f) g) :=
  Subtype.mk h.val <| by
    rw [← h.property]
    funext v
    aesop

abbrev optimized_bind_assume
    {f : b = true → α → Gen β}
    (h : OptGen (.assume b (λ h => .bind x (f h)))) :
    OptGen (.bind x (λ a => .assume b (f · a))) :=
  Subtype.mk h.val <| by
    rw [← h.property]
    funext v
    aesop
