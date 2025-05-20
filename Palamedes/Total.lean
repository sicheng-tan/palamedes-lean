import Palamedes.Support
import Palamedes.InternalizeProofs
import Palamedes.Data.Tree

/-
Predicate and lemmas for backtracking-free generators.
-/

def total : Gen α → Prop
  | .ret _ => True
  | .pick x y => total x ∧ total y
  | .indexed f => ∀ n, total (f n)
  | .bind x f => total x ∧ ∀ v, v ∈ 〚x〛  → total (f v)
  | .assume b f => ∃ (h : b), total (f h)

theorem total_optBind
    (hx : total x)
    (hf : ∀ {v}, support x v → total (f v)) :
    total (optBind x f) := by
  induction x <;>
    aesop
      (add simp optBind)
      (add simp total)

theorem total_optPick
    (hx : total x)
    (hy : total y) :
    total (optPick x y) := by
  generalize hn : genMeasure x + genMeasure y = n
  induction n generalizing x y
  case zero =>
    cases hx : x with
    | assume b f =>
      by_cases h : b
      . simp_all [optPick]
      . simp_all [optPick]
    | _ =>
      cases hy : y with
      | assume b g =>
        by_cases h' : b
        . simp_all [optPick]
        . simp_all [optPick]
      | _ => aesop (add simp optPick) (add simp total)
  case succ m ih =>
    cases x with
    | assume b f =>
      simp [optPick]
      split
      . simp_all [total]
        apply ih
        . apply hx
        . apply hy
        . omega
      . simp_all [total]
    | _ =>
      cases hy : y with
      | assume b g =>
        by_cases h' : b
        . subst y
          simp_all [total]
          simp [optPick]
          split
          . try simp [total]
            apply ih
            . simp [total]
              try apply hx
            . apply hy
            . simp +arith at hn
              subst hn
              simp [genMeasure]
          . contradiction
        . simp_all [optPick]
      | _ => simp_all [optPick]

theorem total_choose : total (choose lo hi h) := by
  induction hdiff : hi - lo generalizing lo hi with
  | zero =>
    have heq : lo = hi := by omega
    simp [heq, total, choose]
  | succ diff' ih =>
    unfold choose
    split
    . simp [total]
    . apply total_optPick
      . simp [total]
      . exact ih (by omega)

theorem total_internalizeProofs (h : total g) : total g.internalizeProofs := by
  induction g with
  | ret v => simp [Gen.internalizeProofs, total]
  | pick x y ihx ihy =>
    simp [Gen.internalizeProofs, total]
    simp [total] at h
    obtain ⟨hx, hy⟩ := h
    apply And.intro
    . simp [Functor.map]
      apply total_optBind
      . exact ihx hx
      . exact fun {v} a => trivial
    . simp [Functor.map]
      apply total_optBind
      . exact ihy hy
      . simp [total]
  | bind x f ihx ihf =>
    simp [Gen.internalizeProofs, total]
    simp [total] at h
    obtain ⟨hx, hf⟩ := h
    apply And.intro
    . simp [*]
    . intro a b h
      simp [Functor.map]
      apply total_optBind <;> simp_all [forall_const, total]
  | indexed f ihf =>
    simp [Gen.internalizeProofs, total]
    intro n
    simp [Functor.map]
    apply total_optBind
    . exact ihf n (h n)
    . intro v hv
      simp [total]
  | assume b f ihf =>
    simp [Gen.internalizeProofs, total]
    simp [Functor.map]
    simp [total] at h
    obtain ⟨h, htot⟩ := h
    exists h
    apply total_optBind
    . exact ihf ((Iff.of_eq (Eq.refl (b = true))).mpr ((Iff.of_eq (Eq.refl (b = true))).mpr h)) htot
    . simp [total]

theorem total_unfoldTree
    (h : ∀ {b'}, total (f b')) :
    total (unfoldTree n f b) := by
  induction n generalizing b with
  | zero => simp [unfoldTree, total]
  | succ n' ih =>
    simp [unfoldTree, total, bind]
    apply total_optBind
    . simp [h]
    . intro v hv
      match v with
      | .leaf => simp [total]
      | .node _ _ _ => simp [total_optBind, ih, total]
