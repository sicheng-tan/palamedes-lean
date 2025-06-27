import Aesop

macro "totality" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, totality])
      (config := {enableSimp := false})
      (add safe (by intro))
      (add 5% (by split))
      (add 5% (by simp)))
