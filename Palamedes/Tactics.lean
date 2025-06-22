import Aesop
import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.Total
import Palamedes.Data.List

open Lean Tactic Elab Meta Tactic

initialize
  registerTraceClass `palamedes.synthesis

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

macro "totality" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [totality]))

-- TODO: This is probably not good enough. If the optimizer fails to prove goals we care about, we
-- probably want to revisit this.
macro "optimality" : tactic =>
  `(tactic|
    aesop
      (add safe (by omega))
      (add unsafe congrFun)
      (add unsafe congrArg))

elab "optimize_gen " t:term : tactic =>
  withMainContext do
    let g ← getMainGoal
    let m ← mkFreshExprMVar none
    let gen ← elabTerm t (some (.app (.const ``Gen []) m))
    let gen' ← withReducible (reduce gen)
    let gen'' ← optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    g.assign gen'''

open Lean Tactic Elab Meta Tactic in
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← evalTacticAt tactic m.mvarId!
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

register_option palamedes.debug : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable debug messages from palamedes"
}

def generatorSearchElab
    (stx : Syntax)
    (t : Term)
    (checkTotal : Bool)
    (tryThis : Bool) :
    TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts

  let g ← getMainGoal
  let .app (.const ``Gen []) α ← g.getType
    | throwError "goal type must be Gen α for some α"
  let ty := .forallE `α α (.sort 0) .default
  let mpred ← elabTerm t (some ty)

  if verbose then do
    TryThis.addSuggestion stx
      s!"-- generator_search ({← ppExpr mpred})
  let cg : CorrectGen ({← ppExpr mpred}) := by
    cgenerator_search
  let g : Gen ({← ppExpr α}) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g"

  let prettyPred ←
    try
      lambdaBoundedTelescope mpred 1 fun fvs body =>
        let a := fvs[0]!
        let subst := FVarSubst.empty
        let tgt := Expr.fvar (FVarId.mk `TARGET)
        return (subst.insert a.fvarId! tgt).apply body
    catch _ =>
      pure mpred

  withTraceNode `palamedes.trace (fun _ => pure m!"⟪{prettyPred}⟫") do

  -- Synthesize a correct generator by solving `CorrectGen P` and projecting the `.val`.
  let gen ← do
    try
      let cgen ← solveGoalWithTactic
        (mkAppN (.const ``CorrectGen []) #[α, mpred])
        (← `(tactic| cgenerator_search))
      withReducible (reduce (← mkAppM ``Subtype.val #[cgen]))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Synthesized generator:\n{(← ppExpr gen)}"

  -- Optimize the generator and prove that the optimized version is correct.
  let gen' ←
    try
      let gen' ← optimizeGen gen
      let gen' ← withReducible (reduce gen')
      let _ ← solveGoalWithTactic
        (← mkEq (← mkAppM ``Gen.support #[gen]) (← mkAppM ``Gen.support #[gen']))
        (← `(tactic| optimality))
      pure gen'
    catch e =>
      throwError m!"Failed during optimization.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Optimized generator:\n{(← ppExpr gen')}"

  -- Optionally: Check that the generator is "total," i.e., that it does not backtrack internally.
  if checkTotal then do
    try
      let _ ← solveGoalWithTactic
        (← mkAppM ``Gen.total #[gen'])
        (← `(tactic| totality))
    catch e =>
      logWarning m!"Failed during totality checking.
      {e.toMessageData}
      {gen'}
      could not be proved total.

      You can use `generator_search {t} allow_partial to turn off this check."

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx gen'

  closeMainGoal `generator_search gen'

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

-- From Kyle Miller

def ensureLHSIsMVar (g : MVarId) : MetaM (Expr × Expr × MVarId) :=
  g.withContext do
    let gty ← g.getType'
    let some (_, lhs, rhs) := gty.eq? | throwError "goal must be eq"
    let lhs ← whnfCore lhs
    if lhs.getAppFn.isMVar then
      return (lhs, rhs, g)
    let rhs ← whnfCore rhs
    if rhs.getAppFn.isMVar then
      let [g] ← g.applyConst ``Eq.symm | throwError "failure to apply Eq.symm"
      return (rhs, lhs, g)
    throwError "neither the LHS nor the RHS is a metavariable application"

/--
Replace each expr in `exprs` with the corresponding fvar in `fvars` by using `kabstract`,
and then creates a lambda that closes the fvars.
Throws an error if the result is not type correct.
Returns a lambda, like `mkLambdaFVars fvars e`.
-/
def mkLambdaGeneralizeFVars (exprs : Array Expr) (fvars : Array Expr) (e : Expr) : MetaM Expr := do
  let e ← (exprs.zip fvars).foldrM (init := e) fun (expr, fvar) e => do
    let e' ← kabstract e expr
    pure <| e'.instantiate1 fvar
  unless ← isTypeCorrect e do
    throwError "failed to generalize expression"
  return (← getLCtx).mkBinding (isLambda := true) fvars e

elab "rflm" : tactic => do
  let g ← popMainGoal
  let (lhs, rhs, g) ← ensureLHSIsMVar g
  g.withContext do
    let m := lhs.getAppFn.mvarId!
    if ← m.isDelayedAssigned then
      -- We could probably try to handle these, but an error for now.
      throwError "metavariable is delayed assigned"
    let args ← lhs.getAppArgs.mapM instantiateMVars
    -- Enter a telescope for the mvar type.
    -- We will replace each `arg` with the corresponding `fvar` while using `kabstract`.
    -- This makes sure that when we do `mkLambdaFVars` that we get a function with
    -- the right type.
    forallBoundedTelescope (← m.getType) args.size fun fvars _ => do
      let rhs ← instantiateMVars rhs
      let rhs' ← mkLambdaGeneralizeFVars args fvars rhs
      unless ← m.checkedAssign rhs' do
        throwError "failed to assign metavariable (due to occurs check or local context mismatches)\n\n\
          Metavariable:{m}\n\
          Value:{indentExpr rhs'}"
    -- Given that that succeeded, now both sides are unified, so Eq.refl must work.
    g.assign (← mkEqRefl rhs)
