import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert

namespace Recursion

#set_up_palamedes_simp

theorem List_rec_lemma
    {α β : Type}
    {b : β}
    {v : List α}
    {P_nil : Prop}
    {P_cons : α → Prop} :
    (List.rec
      (motive :=
        fun t =>
          Prop ×'
            List.rec
              (motive := fun _ => Type)
              β
              (fun _ _ tail_ih => Prop ×' tail_ih)
              t)
      ⟨P_nil, b⟩
      (fun head _ tail_ih => ⟨P_cons head ∧ tail_ih.1, tail_ih⟩)
      v).1 =
    List.rec
      P_nil
      (fun head _ tail_ih => P_cons head ∧ tail_ih)
      v := by
  induction v with
  | nil => simp
  | cons x xs ih =>
    aesop

abbrev synth_List_rec
    {α : Type}
    {f : α → Prop}
    (g : CGen (ListF.rec True (λ a () => f a))) :
    CGen (λ v => List.rec (motive := λ _ => Prop) True (λ h _ t => f h ∧ t) v) :=
  Subtype.mk (List.unfoldr (λ b => g.val) ()) <| by
    rw [support_unfoldr]
    intro v
    induction v with
    | nil =>
      have := g.property .nil
      simp_all [Eq.comm]
    | cons x xs ih =>
      have := g.property
      simp_all

add_aesop_rules unsafe (rule_sets := [palamedes]) [
  apply synth_List_rec
]

def allTwos : List Nat → Prop
  | [] => True
  | x :: xs => x = 2 ∧ allTwos xs

def genAllTwos : CGen (λ v => allTwos v) := by
  delta allTwos
  simp
  conv =>
    congr
    intro v
    apply List_rec_lemma
  palamedes

def lengthK : List Nat → Nat → Prop
  | [], 0 => True
  | _ :: xs, n + 1 => lengthK xs n
  | _, _ => False

def genLengthK {k : Nat} : CGen (λ v => lengthK v k) := by
  delta lengthK
  sorry

end Recursion
