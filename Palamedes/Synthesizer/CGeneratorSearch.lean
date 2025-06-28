import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.RuleSets
import Palamedes.Total
import Palamedes.Data.List
import Palamedes.Data.Stack
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Context
import Palamedes.Data.Tree
import Palamedes.Data.Unit
import Palamedes.Data.Nat
import Palamedes.Data.Bool
import Palamedes.Synthesizer.Util
import Mathlib.Tactic.FailIfNoProgress

open Gen CorrectGen

macro "simp_list_predicate" : tactic =>
  `(tactic|
  -- todo: the bool lemma below is overfitting to the evenLen example
    (first
      | conv => rhs; lhs; apply (List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm))
      | conv => rhs; lhs; apply congrFun; apply (List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm))
      | skip
     first
      | rw [← List.fold_accu_Option_true] <;> (try aesop); done
      | rw [← List.fold_accu_Option_function]; (try aesop); done
      | rw [← List.fold_accu_Option_function_true] <;>
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]) <;> (try aesop); done
      | rw [← List.fold_accu_Option_basic]; (try aesop); done))

macro "simp_tree_predicate" : tactic =>
  `(tactic|
    (first
      | conv => rhs; lhs; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
      | conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
      | skip
     first
      | rw [← Tree.fold_accu_Option_true]; (try aesop); done
      | rw [← Tree.fold_accu_Option_function]; (try aesop); done
      | rw [← Tree.fold_accu_Option_function_true];
        (try intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Tree.fold_accu_Option_basic]; (try aesop); done))

macro "simp_stack_predicate" : tactic =>
  `(tactic|
    (try (conv => rhs; lhs; apply congrFun; apply (Stack.coerce_to_fold (by aesop) (by intros; simp_all; rflm)));
     first
      | rw [← Stack.fold_accu_Option_true]; (try aesop); done
      | rw [← Stack.fold_accu_Option_function]; (try aesop); done
      | rw [← Stack.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Stack.fold_accu_Option_basic]; (try aesop); done))

macro "simp_ty_predicate" : tactic =>
  `(tactic|
    (try (conv => rhs; lhs; apply (Ty.coerce_to_fold (by aesop) (by intros; simp_all; rflm)));
     first
      | rw [← Ty.fold_accu_Option_true] <;> (try aesop); done
      | rw [← Ty.fold_accu_Option_function]; (try aesop); done
      | rw [← Ty.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Ty.fold_accu_Option_basic]; (try aesop); done))

macro "simp_term_predicate" : tactic =>
  `(tactic|
    (try (conv => rhs; lhs; apply congrFun; apply (Term.coerce_to_fold (by aesop) (by intros; simp_all; rflm)));
     first
      | rw [← Term.fold_accu_Option_true]; (try aesop); done
      | rw [← Term.fold_accu_Option_function]; (try aesop); done
      | rw [← Term.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Term.fold_accu_Option_function_Option] <;> (try aesop); done
      | rw [← Term.fold_accu_Option_basic]; (try aesop); done))

macro "simp_predicate" : tactic =>
  `(tactic|
    first
      | funext
        simp [guard, *]
        first
          | exact Eq.comm
          | simp_list_predicate
          | simp_tree_predicate
          | simp_stack_predicate
          | simp_ty_predicate
          | simp_term_predicate
          | apply exists_congr; intro; rw [true_and]
          | rfl
      | rfl)

macro "gapply " t:term : tactic =>
  `(tactic| apply convert (by simp_predicate) $t)

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by fail_if_no_progress intros),
  (by gapply (s_pure _)),
  (by gapply (s_pick _ _)),
  (by gapply (s_bind _ _)),
  (by apply (s_bind _ _)), -- TODO
  (by gapply (List.s_unfold _)),
  (by gapply (Tree.s_unfold _)),
  (by gapply (Stack.s_unfold _)),
  (by gapply (Ty.s_unfold _)),
  (by gapply (Term.s_unfold _)),
  (by gapply s_arbUnit),
  (by gapply s_arbBool),
  (by gapply s_arbNat),
  (by gapply s_arbTy),
  (by gapply s_arbAtom),
  (by gapply s_gt),
  (by gapply s_between_partial),
  (by gapply (s_between (by first | aesop | omega))),
  (by assumption),
]

add_aesop_rules 5% (rule_sets := [synthesis]) [
  (by apply caseBool (by assumption)),
  (by apply caseNat (by assumption))
]

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

macro "cgenerator_search?" : tactic =>
  `(tactic|
    aesop?
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))
