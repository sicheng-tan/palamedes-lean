import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Mathlib.Tactic.Convert

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

syntax (name := exactGenerator) "exact_generator " term : tactic

open Lean Elab Command Meta Tactic in
@[tactic exactGenerator]
def elabExactGenerator : Tactic := fun
  | stx@`(tactic|exact_generator $t) => do
  withMainContext do
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
    TryThis.addExactSuggestion stx e
  | stx => throwError "Unexpected syntax {stx}."

-- @[simp]
-- def genBST' (lo hi : Nat) : Gen (Tree Nat) := by
--   let go : CGen (λ v => isBST lo hi v = some ()) := by
--     aesop
--   exact_generator go.val
