import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Palamedes.V2.Total
import Palamedes.V2.Tactics
import Palamedes.V2.Data.List
import Mathlib.Tactic.FailIfNoProgress

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by fail_if_no_progress intros),
  (by apply Gen.CorrectGen.cpure),
  (by apply Gen.CorrectGen.cpick),
  (by apply Gen.CorrectGen.cbind),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cpure _)),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cpick _ _)),
  -- FIXME: Make this more general
  (by apply convert (by funext a; congr; funext b; rw [true_and]) (Gen.CorrectGen.cbind _ _)),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cbind _ _)),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.List.cunfold _)),
]

add_aesop_rules unsafe (rule_sets := [totality]) [
  Gen.Total.total_pick,
  Gen.Total.total_bind,
  Gen.Total.total_assume,
  Gen.Total.total_indexed,
  Gen.Total.total_internalizeProofs,
  Gen.Total.total_map,
  Gen.Total.total_pure,
]
