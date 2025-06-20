import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.RuleSets
import Palamedes.Total
import Palamedes.Tactics
import Palamedes.Data.List
import Palamedes.Data.Tree
import Palamedes.Data.Unit
import Palamedes.Data.Nat
import Palamedes.Data.Bool
import Mathlib.Tactic.FailIfNoProgress

open Gen CorrectGen

macro "simp_list_predicate" : tactic =>
  `(tactic|
    first
      | rw [← List.fold_accu_Option_true]; (try aesop); done
      | rw [← List.fold_accu_Option_function]; (try aesop); done
      | rw [← List.fold_accu_Option_function_true];
        (try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← List.fold_accu_Option_basic]; (try aesop); done)

macro "simp_tree_predicate" : tactic =>
  `(tactic|
    first
      | rw [← Tree.fold_accu_Option_true]; (try aesop); done
      | rw [← Tree.fold_accu_Option_function]; (try aesop); done
      | rw [← Tree.fold_accu_Option_function_true];
        (try intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
      | rw [← Tree.fold_accu_Option_basic]; (try aesop); done)

macro "simp_predicate" : tactic =>
  `(tactic|
    first
      | funext
        simp [guard, *]
        first
          | exact Eq.comm
          | simp_list_predicate
          | simp_tree_predicate
          | apply exists_congr; intro; rw [true_and]
          | rfl
      | rfl)

macro "gapply " t:term : tactic =>
  `(tactic| apply convert (by simp_predicate) $t)

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by fail_if_no_progress intros),
  (by assumption),
  (by gapply (s_pure _)),
  (by gapply (s_pick _ _)),
  (by gapply (s_bind _ _)),
  (by apply (s_bind _ _)), -- TODO
  (by gapply (List.s_unfold _)),
  (by gapply (Tree.s_unfold _)),
  (by gapply s_arbUnit),
  (by gapply s_arbBool),
  (by gapply s_arbNat),
  (by gapply s_gt),
  (by gapply s_between_partial),
  (by gapply (s_between (by first | aesop | omega))),
]

add_aesop_rules 5% (rule_sets := [synthesis]) [
  (by apply caseBool (by assumption)),
  (by apply caseNat (by assumption))
]

add_aesop_rules unsafe (rule_sets := [totality]) [
  Total.total_pick,
  Total.total_bind,
  Total.total_assume,
  Total.total_indexed,
  Total.total_internalizeProofs,
  Total.total_map,
  Total.total_pure,
  Total.List.total_unfold,
  Total.Tree.total_unfold,
  Total.total_Bool_rec,
  Total.total_Nat_rec
]
