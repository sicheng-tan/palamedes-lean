import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Total

abbrev optimized_ret : {g // support (.ret v) = support g ∧ total g} :=
  Subtype.mk (.ret v) <| by exact ⟨rfl, by simp [total]⟩

abbrev optimized_ret_bind
    (h : {g // support (f v) = support g ∧ total g}) :
    {g // support (.bind (.ret v) f) = support g ∧ total g} :=
  Subtype.mk h.val <| by
    simp [h.property]

abbrev optimized_pick_assume
    {b : Bool}
    {y : Gen α}
    {f : b → Gen α}
    (hf : ∀ (h : b), {g' // support (f h) = support g' ∧ total g'})
    (hy : {y' // support y = support y' ∧ total y'}) :
    {g // support (.pick (.assume b f) y) = support g ∧ total g} :=
  Subtype.mk (if h : b then .pick (hf h).val hy.val else hy.val) <| by
    split
    . rename_i hb
      subst hb
      simp [hy.property, (hf rfl).property, true_and, total]
    . aesop

abbrev optimized_pick_congr
    (hx : {x' // support x = support x' ∧ total x'})
    (hy : {y' // support y = support y' ∧ total y'}) :
    {g // support (.pick x y) = support g ∧ total g} :=
  Subtype.mk (.pick hx.val hy.val) <| by
    simp [hx.property, hy.property, total]
