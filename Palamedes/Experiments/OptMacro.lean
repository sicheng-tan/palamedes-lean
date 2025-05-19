import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Total
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FailIfNoProgress

open Lean Elab Term Meta

syntax (name := optimizeMacro) "optimize! " term : term

-- NOTE: May not need to be in `TermElabM`
def optExpr (e : Expr) : TermElabM Expr := do
  match e with
  | .app f a =>
    match ← optExpr f, ← optExpr a with
    | .app (.app (.app (.const ``Gen.bind _) _) _) (.app (.app (.const ``Gen.ret _) _) v), a =>
      return (e.updateApp! a v).headBeta
    -- TODO: Add more optimizations
    | f, a => return e.updateApp! f a
  | .mdata _ b => return e.updateMData! (← optExpr b)
  | .proj _ _ b => return e.updateProj! (← optExpr b)
  | .letE _ t v b _ => return e.updateLet! (← optExpr t) (← optExpr v) (← optExpr b)
  | .lam _ d b _ => return e.updateLambdaE! (← optExpr d) (← optExpr b)
  | .forallE _ d b _ => return e.updateForallE! (← optExpr d) (← optExpr b)
  | e => return e

@[term_elab optimizeMacro]
def expandOptimizeMacro : TermElab := λ stx ty =>
  match stx with
  | `(optimize! $t) => do
    let e ← elabTerm t ty
    let e ← instantiateMVars e
    optExpr e
  | _ => throwError "invalid syntax"

def g : Gen Nat :=
  optimize!
    .pick
      (.ret 10)
      (.bind (.ret 4) λ x => .ret (x + 1))

#print g
