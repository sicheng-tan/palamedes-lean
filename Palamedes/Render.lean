import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Examples.BST
import Mathlib.Tactic.Convert

/-
Simplifications to improve readability of synthesized generators.
-/

@[simp]
theorem simp_CGen_cast
    {x : Gen α}
    {P : α → Prop}
    {Q : α → Prop}
    {p : ∀ v, v ∈ 〚x〛 ↔ P v}
    {h : Q = P} :
    (cast (Eq.symm (congrArg CGen h)) ⟨x, p⟩).val = x := by
  have {P Q : α → Prop} (h : P = Q) : (∀ v, v ∈ 〚x〛 ↔ P v) = (∀ v, v ∈ 〚x〛 ↔ Q v) := by
    simp_all
  have : (cast (Eq.symm (congrArg CGen h)) ⟨x, p⟩).1 = (⟨x, cast (Eq.symm (this h)) p⟩ : CGen Q).1 := by
    apply congr_heq
    . simp
    . simp [cast]
      subst h
      simp_all only
  rw [this]

@[simp]
theorem simp_CGen_cast'
    {x : Gen α}
    {P : α → Prop}
    {Q : α → Prop}
    {p : ∀ v, v ∈ 〚x〛 ↔ P v}
    {h : P = Q} :
    (h ▸ (⟨x, p⟩ : CGen P)).val = x := by
  have : (h ▸ (⟨x, p⟩ : CGen P)).1 = (⟨x, h ▸ p⟩ : CGen Q).1 := by
    apply congr_heq
    . simp
    . simp [cast]
      subst h
      simp_all only
  rw [this]

@[simp]
theorem simp_And_rec
    {a : A ∧ B}
    {g : CGen P} :
    (@And.rec _ _ (λ _ => CGen P) (λ _ _ => g) a).val = g.val := by
  obtain ⟨left, right⟩ := a
  obtain ⟨val, property⟩ := g
  simp_all only

syntax (name := extractGeneratorCmd) "#extract_generator " term " as " ident : command

open Lean Elab Command Meta Tactic in
@[command_elab extractGeneratorCmd]
partial def elabExtractGeneratorCmd : CommandElab := fun
  | stx@`(#extract_generator $t as $name) => do
    liftTermElabM do
      let e ← Term.elabTerm t none
      let ctx ← Simp.Context.ofNames []
      let e ← (·.1.expr) <$> simp e ctx
      let simprocs ← Simp.getSimprocs
      let hs ← getPropHyps
      let mut simpTheorems := ctx.simpTheorems
      for h in hs do
        unless simpTheorems.isErased (.fvar h) do
          simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
      let e ← (·.1.expr) <$> simp e {ctx with simpTheorems} (simprocs := #[simprocs])
      let t ← TryThis.delabToRefinableSyntax e
      TryThis.addSuggestion stx (← `(def $name := $t)) (header := "Try this generator:\n") --
  | stx => throwError "Unexpected syntax {stx}."

syntax (name := exactGenerator) "generator? " term : tactic

open Lean Elab Command Meta Tactic in
@[tactic exactGenerator]
def elabExactGenerator : Tactic := fun
  | stx@`(tactic|generator? $t) => do
    let (_, goal) ← (← getMainGoal).intros
    goal.withContext do
      let e ← elabTerm t none
      let ctx ← Simp.Context.ofNames []
      let e ← (·.1.expr) <$> simp e ctx
      let simprocs ← Simp.getSimprocs
      let hs ← getPropHyps
      let mut simpTheorems := ctx.simpTheorems
      for h in hs do
        unless simpTheorems.isErased (.fvar h) do
          simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
      let e ← (·.1.expr) <$> simp e {ctx with simpTheorems} (simprocs := #[simprocs])
      TryThis.addSuggestion stx (← TryThis.delabToRefinableSyntax e)
      admitGoal goal
  | stx => throwError "Unexpected syntax {stx}."

macro "generator_for? " t:term : term =>
  `(let go : CGen $t := by palamedes
    by generator? go.val)

#set_up_palamedes_simp

@[simp]
def cgenBST (lo hi : Nat) : CGen (λ v => isBST lo hi v = some ()) := by
  palamedes

#extract_generator (λ lo hi => (cgenBST lo hi).val) as genBST'

theorem bind_ret : (pure x : Gen α) >>= f = f x := by simp [bind, optBind]
theorem bind_assume : Gen.assume b x >>= f = Gen.assume b (λ h => (x h >>= f)) := by simp [bind, optBind]
axiom bind_assoc'
  {α β γ : Type}
  {x : Gen α}
  {f : α → Gen β}
  {g : β → Gen γ}
  : (x >>= f) >>= g = x >>= (f >=> g)
theorem pick_assume_r : pick x (Gen.assume b f) = if h : b then pick x (f h) else x :=
  sorry

theorem bind_optBind : optBind f x = bind f x := by simp [bind, optBind]

attribute [local simp]
  bind_optBind
  bind_ret
  bind_assume
  bind_assoc'
  pick_assume_r
  CGen.internalizeProofs
  Gen.internalizeProofs
  Functor.map
in
def genBST' (lo hi : Nat) : Gen (Tree Nat) :=
  generator_for? (λ v => isBST lo hi v = some ())

def genOneToTen' : Gen Nat :=
  generator_for? (λ v => 1 ≤ v ∧ v ≤ 10)

def genFourOrFive' : Gen Nat :=
  generator_for? (λ v => v = 4 ∨ v = 5)

open Lean Elab Tactic Command Meta Lean.Meta.Tactic.TryThis

syntax (name := showGenTactic) "show_gen " tacticSeq : tactic

@[tactic showGenTactic]
def expandShowGen : Tactic := λ stx =>
  withMainContext do
    let g ← getMainGoal
    match stx with
    | `(tactic| show_gen%$tk $t) =>
        evalTactic t
        let e ← instantiateMVars (mkMVar g)
        let { ctx, simprocs, dischargeWrapper := _ } ← mkSimpContext stx (eraseLocal := false)
        let ({expr := e, ..}, _) ← simp e ctx (simprocs := simprocs) (discharge? := none)
        addExactSuggestion tk e (origSpan? := ← getRef)
    | _ => Lean.Meta.throwTacticEx `show_gen g m!"invalid syntax"
