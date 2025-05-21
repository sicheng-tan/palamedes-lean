import Palamedes.Total
import Palamedes.Experiments.Optimizer
import Palamedes.Experiments.TotalExperiment
import Mathlib.Tactic.FailIfNoProgress

namespace OptMacro

add_aesop_rules unsafe (rule_sets := [palamedes_optimize]) [
  (by apply optimized_ret),
  (by apply optimized_pick_assume),
  (by apply optimized_ret_bind),
  (by apply optimized_pick_congr),
  (by fail_if_no_progress intro),
]

macro "optimized" : tactic =>
  `(tactic|
    aesop
      (config := {enableSimp := false})
      (rule_sets := [-builtin, -default, palamedes_optimize]))

@[reducible]
def g' (b : Bool) : OptGen (.pick (.assume b (λ _ =>.ret 10)) (.bind (.ret 4) λ x => .ret (x + 1))) := by
  optimized

example {b : Bool} : total (g' b).val := by
  totality

open Lean Elab Term Meta in
def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

#eval traceConstWithTransparency .reducible ``g'
