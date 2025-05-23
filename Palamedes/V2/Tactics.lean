import Aesop
import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Optimizer
import Palamedes.V2.Total

macro "simp_predicate" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [simplification]))

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

macro "totality" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [totality]))

macro "optimize_generator" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, optimization])
      (config := {enableSimp := false}))

-- Borrowed from Aesop
def printAsMillis (n : Nat) : String :=
  let str := toString (n.toFloat / 1000000)
  match str.split λ c => c == '.' with
  | [beforePoint] => beforePoint ++ "ms"
  | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 1 ++ "ms"
  | _ => unreachable!

open Lean Tactic Elab Meta Tactic in
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let .mvar m ← mkFreshExprMVar goalType | throwError "impossible"
  let [] ← evalTacticAt tactic m | throwError "goals left unsolved"
  instantiateMVars (.mvar m)

open Lean Tactic Elab Meta Tactic in
def generatorSearchElab (t : Term) (checkTotal : Bool) (verbose : Bool) : TacticM Unit := do
  let startTime ← IO.monoNanosNow

  let g ← getMainGoal
  let .app (.const ``Gen []) α ← g.getType | throwError "goal type must be Gen α for some α"
  let ty := .forallE `α α (.sort 0) .default
  let mpred ← elabTerm t (some ty)

  let cgen ←
    try
      solveGoalWithTactic (mkAppN (.const ``CorrectGen []) #[α, mpred]) (← `(tactic| cgenerator_search))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Synthesized CorrectGen:\n{(← ppExpr cgen)}"

  let gen ← mkAppM ``Subtype.val #[cgen]
  let gen ← withReducible (reduce gen)
  if verbose then do
    logInfo m!"Reduced Gen:\n{(← ppExpr gen)}"

  let ogen ←
    try
      solveGoalWithTactic (← mkAppM ``OptGen #[gen]) (← `(tactic| optimize_generator))
    catch e =>
      throwError m!"Failed during optimization.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Optimized OptGen:\n{(← ppExpr ogen)}"

  let gen ← mkAppM ``Subtype.val #[ogen]
  let gen ← withReducible (reduce gen)
  if verbose then do
    logInfo m!"Reduced Gen:\n{(← ppExpr gen)}"

  if checkTotal then do
    try
      let _ ← solveGoalWithTactic (← mkAppM ``Gen.total #[gen]) (← `(tactic| totality))
    catch e =>
      logWarning m!"Failed during totality checking.\n\n{e.toMessageData}\n\n{gen}\nis not total.\n\nYou can use `generator_search {t} allow_partial to turn off this check."

  let endTime ← IO.monoNanosNow

  let elapsed := endTime - startTime
  if verbose then do
    logInfo m!"Synthesis for {← ppExpr mpred} took {printAsMillis elapsed}"

  closeMainGoal `generator_search gen

elab "generator_search " t:term p:"allow_partial"? : tactic =>
  generatorSearchElab t p.isNone false

elab "generator_search? " t:term p:"allow_partial"? : tactic =>
  generatorSearchElab t p.isNone true
