import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Palamedes.V2.Total
import Palamedes.V2.Tactics
import Mathlib.Tactic.FailIfNoProgress

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by fail_if_no_progress intros),
  (by apply Gen.CorrectGen.cpure),
  (by apply Gen.CorrectGen.cpick),
  (by apply Gen.CorrectGen.cbind),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cpure _)),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cpick _ _)),
  (by apply Gen.CorrectGen.convert (by simp_predicate) (Gen.CorrectGen.cbind _ _)),
]
