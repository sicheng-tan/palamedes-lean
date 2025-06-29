import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.RuleSets
import Palamedes.Total
import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Context
import Palamedes.Data.Tree
import Palamedes.Data.Unit
import Palamedes.Data.Nat
import Palamedes.Data.Bool
import Palamedes.Synthesizer.Util

open Gen CorrectGen

macro "simp_predicate" : tactic => `(tactic| try simp [guard, Option.bind_eq_some_iff, *])

macro "norm_for_List_unfold" : tactic =>
  `(tactic|
  -- todo: the bool lemma below is overfitting to the evenLen example
    (funext
     simp_predicate
     repeat'
      (first
        | rw [← List.merge_accuM]; apply and_congr
        | (first
            | conv => rhs; lhs; apply (List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm))
            | conv => rhs; lhs; apply congrFun; apply (List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm))
            | skip
           first
            | rw [← List.fold_accu_Option_true] <;> (try aesop); done
            | rw [← List.fold_accu_Option_function]; (try aesop); done
            | rw [← List.fold_accu_Option_function_true] <;>
              (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]) <;> (try aesop); done
            | rw [← List.fold_accu_Option_basic]; (try aesop); done))))

macro "norm_for_Tree_unfold" : tactic =>
  `(tactic|
    (funext
     simp_predicate
     repeat'
      (first
        | rw [← Tree.merge_accuM]; apply and_congr
        | (first
            | conv => rhs; lhs; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
            | conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
            | skip
           first
            | rw [← Tree.fold_accu_Option_true]; (try aesop); done
            | rw [← Tree.fold_accu_Option_function]; (try aesop); done
            | rw [← Tree.fold_accu_Option_function_true];
              (try intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
            | rw [← Tree.fold_accu_Option_basic]; (try aesop); done))))

macro "norm_for_Stack_unfold" : tactic =>
  `(tactic|
    (funext
     simp_predicate
     try (conv => rhs; lhs; apply congrFun; apply (Stack.coerce_to_fold (by aesop) (by intros; simp_all; rflm) (by intros; simp_all; rflm)));
     first
      | rw [← Stack.fold_accu_Option_true]; (try aesop); done
      | rw [← Stack.fold_accu_Option_function]; (try aesop); done
      | rw [← Stack.fold_accu_Option_function_true] <;>
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Stack.fold_accu_Option_basic]; (try aesop); done))

macro "norm_for_Ty_unfold" : tactic =>
  `(tactic|
    (funext
     simp_predicate
     try (conv => rhs; lhs; apply (Ty.coerce_to_fold (by aesop) (by intros; simp_all; rflm)));
     first
      | rw [← Ty.fold_accu_Option_true] <;> (try aesop); done
      | rw [← Ty.fold_accu_Option_function]; (try aesop); done
      | rw [← Ty.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Ty.fold_accu_Option_basic]; (try aesop); done))

macro "norm_for_Term_unfold" : tactic =>
  `(tactic|
    (funext
     simp_predicate
     try (conv => rhs; lhs; apply congrFun; apply (Term.coerce_to_fold (by aesop) (by aesop) (by intros; simp_all; rflm) (by intros; simp_all; rflm)));
     first
      | rw [← Term.fold_accu_Option_true]; (try aesop); done
      | rw [← Term.fold_accu_Option_function]; (try aesop); done
      | rw [← Term.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Term.fold_accu_Option_function_Option] <;> (try aesop); done
      | rw [← Term.fold_accu_Option_basic]; (try aesop); done))

macro "norm_for_pure" : tactic =>
  `(tactic| (
    funext
    unfold_matches
    simp_predicate
    first
      | rfl
      | exact Eq.comm))

macro "norm_for_pick" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    try simp [← Decidable.or_iff_not_imp_left]
    rfl))

macro "norm_for_bind" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

macro "norm_for_bind'" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    rw [exists_comm]
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

add_aesop_rules safe (rule_sets := [synthesis]) [
  (by (repeat apply duncurry); intro),
  (by apply convert (by norm_for_pure) (s_pure _)),
]

macro "goal_is_eq_or_and" : tactic =>
  `(tactic|
    first
      | guard_target = CorrectGen (fun _ => _ = _)
      | guard_target = CorrectGen (fun _ => _ ∧ _))

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by assumption),
  (by apply convert (by norm_for_pick) (s_pick _ _)),
  (by apply convert (by norm_for_bind) (s_bind _ _)),
  (by apply convert (by norm_for_bind') (s_bind _ _)), -- TODO Fix this
  (by goal_is_eq_or_and; apply convert (by norm_for_List_unfold) (List.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Stack_unfold) (Stack.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Term_unfold) (Term.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Ty_unfold) (Ty.s_unfold _)),
  (by apply s_arbUnit),
  (by apply s_arbBool),
  (by apply s_arbNat),
  (by apply s_arbTy),
  (by apply s_arbLabel),
  (by apply s_arbAtom _),
  (by apply s_gt),
  (by apply s_between_partial),
  (by apply (s_between (by first | aesop | omega))),
  (by apply (s_indicesOf _ _)), -- TODO Fix this
]

macro "goal_is_or" : tactic =>
  `(tactic| guard_target = CorrectGen (fun _ => _ ∨ _))

add_aesop_rules 5% (rule_sets := [synthesis]) [
  (by apply caseBool (by assumption)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 1) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 1) (by intros; rflm)),
]

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))

macro "cgenerator_search?" : tactic =>
  `(tactic|
    aesop?
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))
