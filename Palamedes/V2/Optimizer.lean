import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Mathlib.Tactic.FailIfNoProgress

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
def opt_pick_assume : OptGen (pick x (assume b f)) :=
  Subtype.mk (if h : b then pick x (f h) else x) <| by
    split <;> aesop

@[reducible]
def opt_assume_pick : OptGen (pick (assume b f) y) :=
  Subtype.mk (if h : b then pick (f h) y else y) <| by
    split <;> aesop

@[reducible]
def opt_assume_bind : OptGen (assume b f >>= g) :=
  Subtype.mk (assume b (fun h => f h >>= g)) <| by
    aesop

@[reducible]
def opt_bind_assume {f : α → b = true → Gen β} : OptGen (x >>= fun a => assume b (f a)) :=
  Subtype.mk (assume b (fun h => x >>= fun a => f a h)) <| by
    aesop

@[reducible]
def opt_pure_bind : OptGen (pure a >>= f) :=
  Subtype.mk (f a) <| by
    simp

@[reducible]
def opt_bind_bind : OptGen ((x >>= f) >>= g) :=
  Subtype.mk (x >>= (fun a => f a >>= g)) <| by
    aesop

end OptGen

end Gen

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by fail_if_no_progress intros),

  (by apply Gen.OptGen.opt_pure_bind),
  (by apply Gen.OptGen.opt_bind_bind),
  (by apply Gen.OptGen.opt_pick_assume),
  (by apply Gen.OptGen.opt_assume_pick),
  (by apply Gen.OptGen.opt_bind_assume),
  (by apply Gen.OptGen.opt_assume_bind),

  (by apply Gen.OptGen.opt_pure_self),
  (by apply Gen.OptGen.opt_bind_congr),
  (by apply Gen.OptGen.opt_pick_congr),
  (by apply Gen.OptGen.opt_indexed_congr),
  (by apply Gen.OptGen.opt_assume_congr),
  (by apply Gen.OptGen.opt_map_congr),
]
