import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.CasesM

@[reducible]
def OptGen (g : Gen α) := {g' : Gen α // g.support = g'.support}

namespace Gen

namespace OptGen

@[reducible]
def opt_pure_self : OptGen (pure a) :=
  Subtype.mk (pure a) (by rfl)

@[reducible]
def opt_bind_congr
    (x' : OptGen x)
    (f' : ∀ a, OptGen (f a)) :
    OptGen (x >>= f) :=
  Subtype.mk (x'.val >>= fun a => (f' a).val) <| by
    simp [x'.property, (f' _).property]

@[reducible]
def opt_pick_congr
    (x' : OptGen x)
    (y' : OptGen y) :
    OptGen (pick x y) :=
  Subtype.mk (pick x'.val y'.val) <| by
    simp [x'.property, y'.property]

@[reducible]
def opt_indexed_congr
    (f' : ∀ n, OptGen (f n)) :
    OptGen (indexed f) :=
  Subtype.mk (indexed (fun n => (f' n).val)) <| by
    simp [(f' _).property]

@[reducible]
def opt_assume_congr
    (f' : ∀ (h : b = true), OptGen (f h)) :
    OptGen (assume b f) :=
  Subtype.mk (assume b (fun h => (f' h).val)) <| by
    simp [(f' _).property]

@[reducible]
def opt_map_congr
    (x' : OptGen x) :
    OptGen (f <$> x) :=
  Subtype.mk (f <$> x'.val) <| by
    simp [x'.property]

@[reducible]
def opt_pick_assume
    {b : Bool}
    {f : b = true → Gen α}
    (x' : OptGen x)
    (y' : ∀ h : b = true, OptGen (pick x (f h))) :
    OptGen (pick x (assume b f)) :=
  Subtype.mk (if h : b then (y' h).val else x'.val) <| by
    split
    . rename_i h
      have := (y' h).property
      aesop
    . funext a
      simp [x'.property]
      intro h
      contradiction

@[reducible]
def opt_assume_pick
    {b : Bool}
    {f : b = true → Gen α}
    (x' : ∀ h : b = true, OptGen (pick (f h) y))
    (y' : OptGen y) :
    OptGen (pick (assume b f) y) :=
  Subtype.mk (if h : b then (x' h).val else y'.val) <| by
    split
    . rename_i h
      have := (x' h).property
      aesop
    . funext a
      simp [y'.property]
      intro h
      contradiction

@[reducible]
def opt_assume_bind
    {b : Bool}
    {f : b = true → Gen α}
    (g' : ∀ (h : b = true), OptGen (f h >>= g)) :
    OptGen (assume b f >>= g) :=
  Subtype.mk (assume b (fun h => (g' h).val)) <| by
    by_cases h : b = true
    . have := (g' h).property
      aesop
    . simp
      funext a
      simp
      apply Iff.intro <;> (intro; casesm* _ ∧ _, ∃ _, _; contradiction)

@[reducible]
def opt_bind_assume
    {f : α → b = true → Gen β}
    (g' : ∀ h, OptGen (x >>= fun a => f a h)) :
    OptGen (x >>= fun a => assume b (f a)) :=
  Subtype.mk (assume b (fun h => (g' h).val)) <| by
    by_cases h : b = true
    . have := (g' h).property
      aesop
    . simp
      funext b
      simp
      apply Iff.intro <;> (intro; casesm* _ ∧ _, ∃ _, _; contradiction)

@[reducible]
def opt_pure_bind
    (f' : OptGen (f a)) :
    OptGen (pure a >>= f) :=
  Subtype.mk f'.val <| by
    simp [f'.property]

@[reducible]
def opt_bind_bind
    (g' : ∀ a, OptGen (f a >>= g)) :
    OptGen ((x >>= f) >>= g) :=
  Subtype.mk (x >>= (fun a => (g' a).val)) <| by
    simp
    funext a
    simp
    apply Iff.intro
    . intro
      casesm* _ ∧ _, ∃ _, _
      rename_i a' _ _
      exists a'
      have := (g' a').property
      rw [← this]
      aesop
    . intro
      casesm* _ ∧ _, ∃ _, _
      rename_i a' _ right
      have := (g' a').property
      simp_all
      rw [← this] at right
      casesm* _ ∧ _, ∃ _, _
      aesop

end OptGen

end Gen

add_aesop_rules safe (rule_sets := [optimization]) [
  (by fail_if_no_progress intros),

  (by apply Gen.OptGen.opt_pure_bind),
  (by apply Gen.OptGen.opt_bind_bind),
  (by apply Gen.OptGen.opt_pick_assume),
  (by apply Gen.OptGen.opt_assume_pick),
  (by apply Gen.OptGen.opt_bind_assume),
  (by apply Gen.OptGen.opt_assume_bind),
]

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by apply Gen.OptGen.opt_pure_self),
  (by apply Gen.OptGen.opt_bind_congr),
  (by apply Gen.OptGen.opt_pick_congr),
  (by apply Gen.OptGen.opt_indexed_congr),
  (by apply Gen.OptGen.opt_assume_congr),
  (by apply Gen.OptGen.opt_map_congr),
]
