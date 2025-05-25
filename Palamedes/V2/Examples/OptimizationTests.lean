import Lean
import Palamedes.V2.Tactics
import Palamedes.V2.Gen

open Lean Elab Command Term Meta Gen

syntax (name := assertOptimizes) "#assert_optimizes! " term " goes_to " term : command

def mkOptBind (x f : Expr) : MetaM (Option Expr) :=
  match_expr x with
  -- pure_bind : pure a >>= f ~~> f a
  | pure _ _ _ a => return some (.app f a)
  -- bind_bind : (x >>= f) >>= g ~~> x >>= (fun x -> f x >>= g)
  | bind _ _ _ _ x' g => do
    let .forallE _ argTy _ _ ← inferType g | return none
    let f' ← withLocalDecl `a .default argTy fun a => do
      mkLambdaFVars #[a] (← mkAppM ``bind #[.app g a, f])
    mkAppM ``bind #[x', f']
  -- assume_bind : assume b g >>= f ~~> assume b (fun h => g h >>= f)
  | assume _ b g => do
    let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app g h, f])
    mkAppM ``assume #[b, f']
  | _ => do
    lambdaBoundedTelescope f 1 fun args body => do
      -- bind_assume : x >>= fun a => assume b g ~~> assume b (fun h => (x >>= fun a => g h))
      --               (where a is not free in b)
      let #[a] := args | return none
      let_expr assume _ b g := body | return none

      -- NOTE: This check ensures that we're allowed to lift `b` out of the lambda that binds `a`,
      -- but it doesn't always behave as expected. In particular, if `b` has metavariables that
      -- might depend on `a`, this will fail. I wonder if we could detect if `b` MUST depend on `a`,
      -- and otherwise just assert that it doesn't and try pulling it out, but that might not be
      -- sound.
      if b.containsFVar a.fvarId! then return none

      let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
        mkLambdaFVars #[h] (← mkAppM ``bind #[x, ← mkLambdaFVars #[a] (.app g h)])
      return some (← mkAppM ``assume #[b, f'])

def mkOptPick (x y : Expr) : MetaM (Option Expr) :=
  match_expr x with
  -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
  | assume _ b f => do
    let c ← mkEq b (.const ``true [])
    let fPos ← withLocalDecl `h .default c fun h => do
      mkLambdaFVars #[h] (← mkAppM ``pick #[.app f (.bvar 0), y])
    let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
      mkLambdaFVars #[h] y
    return (some (← mkAppM ``dite #[c, fPos, fNeg]))
  | _ =>
    match_expr y with
    -- pick_assume : pick x (assume b f) ~~> if h : b then pick x (f h) else x
    | assume _ b f => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[x, .app f (.bvar 0)])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] x
      return (some (← mkAppM ``dite #[c, fPos, fNeg]))
    | _ => return none

def optimizeGen (e : Expr) : MetaM Expr := do
  let post (e : Expr) : MetaM TransformStep := do
    match_expr ← withReducible (reduce e) with
    | bind _ _ _ _ x f => if let some e' ← mkOptBind x f then return .visit e' else return .continue
    | pick _ x y => if let some e' ← mkOptPick x y then return .visit e' else return .continue
    | _ => return .continue
  transform (post := post) e

@[command_elab assertOptimizes]
def expandAssertOptimizes : CommandElab := fun stx =>
  match stx with
  | `(#assert_optimizes! $t1:term goes_to $t2:term) => do
    liftTermElabM do
      let mα ← mkFreshExprMVar none
      let e1 ← elabTerm t1 (some (.app (.const ``Gen []) mα))
      let e2 ← elabTerm t2 (some (.app (.const ``Gen []) mα))
      let e1' ← optimizeGen e1
      unless ← isDefEq e1' e2 do
        throwError "{e1}\n~~>\n{e1'}\n!=\n{e2}"
  | _ => throwError "invalid syntax {stx}"

private axiom g : Gen α
private axiom f : α → Gen β

#assert_optimizes!
  pure 5 >>= fun x => pure (x + 1)
  goes_to
  (fun x => pure (x + 1)) 5

#assert_optimizes!
  (g >>= fun x => pure (x + 1)) >>= fun x => pure (x + 2)
  goes_to
  g >>= (fun x => pure ((x + 1) + 2))

#assert_optimizes!
  pick (assume (2 == 2) (fun _ => pure 3)) (pure 4)
  goes_to
  if _ : (2 == 2) then pick (pure 3) (pure 4) else pure 4

-- TODO: Can we do better? Ideally we could apply a heuristic here to try to figure out which one is
-- easier to satisfy...
#assert_optimizes!
  pick (assume (2 == 2) (fun _ => pure 2)) (assume (3 == 3) (fun _ => pure 3))
  goes_to
  if (2 == 2) then if (3 == 3) then pick (pure 2) (pure 3) else pure 2 else assume (3 == 3) (fun _ => pure 3)

#assert_optimizes!
  (assume (2 == 2) (fun _ => pure 3)) >>= f
  goes_to
  assume (2 == 2) (fun _ => f 3)

#assert_optimizes!
  g >>= (fun x => assume ((2 : Nat) == 2) (fun _ => pure (x + 1)))
  goes_to
  assume ((2 : Nat) == 2) (fun h => g >>= fun x => (fun _ => pure (x + 1)) h)

#assert_optimizes!
  pick (pure 4) (assume (2 == 2) (fun _ => pure 3))
  goes_to
  if _ : (2 == 2) then pick (pure 4) (pure 3) else pure 4
