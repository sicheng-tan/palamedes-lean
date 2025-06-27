import Palamedes.Data.List
import Palamedes.Data.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Support

macro "optimality" : tactic =>
  `(tactic|
    repeat'
      first
        | rfl
        | (intro)
        | try simp only
          rw [support_assume_pick]
        | try simp only
          rw [support_pick_assume]
        | try simp only
          rw [support_assume_bind]
        | try simp only
          rw [support_pure_bind]
        | try simp only
          rw [support_bind_bind]
        | try simp only
          rw [← support_pick_bind]
        | try simp only
          rw [← support_if_bind]
        | apply Term.support_unfold_congr
        | apply Tree.support_unfold_congr
        | apply List.support_unfold_congr
        | apply Stack.support_unfold_congr
        | apply Ty.support_unfold_congr
        | apply Gen.support_caseTy_congr
        | apply Gen.Gen.support_Nat_rec_congr
        | apply support_bind_congr
        | apply support_pick_congr
        | apply support_if_congr)
