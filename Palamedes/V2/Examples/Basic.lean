import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Palamedes.V2.Total
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.FailIfNoProgress

section Tactics

macro "simp_predicate" : tactic =>
  `(tactic|
    simp)

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by apply Gen.CorrectGen.cpure),
  (by apply Gen.CorrectGen.cpick),
  (by apply Gen.CorrectGen.cbind),
  (by fail_if_no_progress intros),
  -- (by first
  --   | apply synth_or
  --   | apply synth_conv (by simp_predicate; exact rfl) (synth_or _ _)),
  -- (by first
  --   | apply synth_bind
  --   | apply synth_conv (by ext; congr!; rw [true_and]) (synth_bind _ _)
  --   | apply synth_conv (by ext; conv => rhs; congr; intro; rw [and_comm]) (synth_bind _ _)
  --   | apply synth_conv (by simp_predicate; exact rfl) (synth_bind _ _)),
  -- (by apply synth_true),
  -- (by apply synth_between),
]

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

add_aesop_rules unsafe (rule_sets := [totality]) [
  Gen.Total.total_pure
]

macro "totality" : tactic => `(tactic|
  next =>
    aesop (rule_sets := [totality]))

open Lean Tactic Elab Meta Tactic in
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let .mvar m ← mkFreshExprMVar goalType
    | throwError "impossible"
  let [] ← evalTacticAt tactic m
    | throwError "generator search left goals unsolved"
  instantiateMVars (.mvar m)

open Lean Tactic Elab Meta Tactic in
elab "generator_search " t:term : tactic => withMainContext do
  let cgen ←
    solveGoalWithTactic
      (← do
        let ty := .forallE `α (← mkFreshExprMVar none) (.sort 0) .default
        let mpred ← elabTerm t (some ty)
        mkAppM ``CorrectGen #[mpred])
      (← `(tactic| cgenerator_search))

  let gen ← mkAppM ``Subtype.val #[cgen]
  let gen ← withReducible (reduce gen)

  let _ ←
    solveGoalWithTactic
      (← mkAppM ``Gen.total #[gen])
      (← `(tactic| totality))

  closeMainGoal `generator_search gen

def genEq2 : Gen Nat := by
  show_term
  generator_search (· = 2)

def genEq2Or5 : Gen Nat := by
  show_term
  generator_search (fun a => a = 2 ∨ a = 5)

def genThreePlusOne : Gen Nat := by
  show_term
  generator_search (fun b => ∃ a, a = 2 ∧ b = a + 1)
