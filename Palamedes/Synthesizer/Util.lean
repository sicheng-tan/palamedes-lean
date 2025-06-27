import Lean

open Lean Tactic Elab Meta Tactic

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
