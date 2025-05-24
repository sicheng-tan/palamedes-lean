import Aesop
import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Optimizer
import Palamedes.V2.Total

open Lean Tactic Elab Meta Tactic

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

register_option palamedes.debug : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable debug messages from palamedes"
}

register_option palamedes.timing : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable timing messages from palamedes"
}

def generatorSearchElab (stx : Syntax) (t : Term) (checkTotal : Bool) (tryThis : Bool) : TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts
  let printTiming := palamedes.timing.get opts

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
    TryThis.addSuggestion stx
      <| String.intercalate "\n"
      [s!"let cg : CorrectGen {← ppExpr mpred} := by cgenerator_search",
        "  let og : OptGen cg.val := by optimize_generator",
        "  let _ : Gen.total og.val := by totality",
        "  exact og.val"]

  if printTiming then do
    logInfo m!"Synthesis for {← ppExpr mpred} took {printAsMillis elapsed}"

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx gen

  closeMainGoal `generator_search gen

syntax (name := generatorSearch) "generator_search " term " allow_partial"? : tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search $t allow_partial) =>
    generatorSearchElab stx t false false
  | `(tactic| generator_search $t) =>
    generatorSearchElab stx t true false
  | _ => throwError "invalid syntax"

syntax (name := generatorSearch?) "generator_search? " term " allow_partial"? : tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search? $t allow_partial) =>
    generatorSearchElab stx t false true
  | `(tactic| generator_search? $t) =>
    generatorSearchElab stx t true true
  | _ => throwError "invalid syntax"
