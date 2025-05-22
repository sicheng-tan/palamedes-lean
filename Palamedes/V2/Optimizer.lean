import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets

@[reducible]
def OptGen (g : Gen α) := {g' : Gen α // g.support = g'.support}

namespace Gen

namespace OptGen

@[reducible]
def opt_pure_self : OptGen (pure a) :=
  Subtype.mk (pure a) (by rfl)

@[reducible]
def opt_bind_self : OptGen (x >>= f) :=
  Subtype.mk (x >>= f) (by rfl)

@[reducible]
def opt_pick_self : OptGen (pick x y) :=
  Subtype.mk (pick x y) (by rfl)

@[reducible]
def opt_indexed_self : OptGen (indexed f) :=
  Subtype.mk (indexed f) (by rfl)

@[reducible]
def opt_assume_self : OptGen (assume b f) :=
  Subtype.mk (assume b f) (by rfl)

@[reducible]
def opt_map_self : OptGen (f <$> x) :=
  Subtype.mk (f <$> x) (by rfl)

@[reducible]
def opt_pick_assume : OptGen (pick x (assume b f)) :=
  Subtype.mk (if h : b then pick x (f h) else x) <| by
    split <;> aesop

end OptGen

end Gen

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by apply Gen.OptGen.opt_pick_assume),

  (by apply Gen.OptGen.opt_pure_self),
  (by apply Gen.OptGen.opt_bind_self),
  (by apply Gen.OptGen.opt_pick_self),
  (by apply Gen.OptGen.opt_indexed_self),
  (by apply Gen.OptGen.opt_assume_self),
  (by apply Gen.OptGen.opt_map_self),
]
