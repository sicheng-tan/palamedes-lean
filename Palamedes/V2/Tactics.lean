import Aesop
import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Optimizer
import Palamedes.V2.Total

macro "simp_predicate" : tactic =>
  `(tactic|
    aesop (rule_sets := [simplification]))

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

macro "totality" : tactic =>
  `(tactic|
    aesop (rule_sets := [totality]))

macro "optimize_generator" : tactic =>
  `(tactic|
    aesop (rule_sets := [optimization]))

open Lean Tactic Elab Meta Tactic in
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let .mvar m ← mkFreshExprMVar goalType
    | throwError "impossible"
  let [] ← evalTacticAt tactic m
    | throwError "generator search left goals unsolved"
  instantiateMVars (.mvar m)

open Lean Tactic Elab Meta Tactic in
elab "generator_search " t:term p:"allow_partial"? : tactic => withMainContext do
  let g ← getMainGoal
  let .app (.const ``Gen []) α ← g.getType | throwError "goal type must be Gen α for some α"

  let cgen ←
    try
      solveGoalWithTactic
        (← do
          let ty := .forallE `α α (.sort 0) .default
          let mpred ← elabTerm t (some ty)
          return mkAppN (.const ``CorrectGen []) #[α, mpred])
        (← `(tactic| cgenerator_search))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"

  let gen ← mkAppM ``Subtype.val #[cgen]
  let gen ← withReducible (reduce gen)

  let ogen ←
    solveGoalWithTactic
      (← mkAppM ``OptGen #[gen])
      (← `(tactic| optimize_generator))

  let gen ← mkAppM ``Subtype.val #[ogen]
  let gen ← withReducible (reduce gen)

  unless p.isSome do
    let _ ←
      try
        solveGoalWithTactic
          (← mkAppM ``Gen.total #[gen])
          (← `(tactic| totality))
      catch e =>
        throwError m!"Failed during totality checking.\n{e.toMessageData}\nYou can use `generator_search {t} allow_partial to turn off this check."

  closeMainGoal `generator_search gen
