import Aesop
inductive Gen' : (α : Type) → (P: α → Prop) → Type 1 where
| ret (r : α) (p : ∀ v, P v ↔ v = r) : Gen' α P
| gt (lo : Int) (p : ∀ v, P v ↔ v > lo) : Gen' Int P
| lt (hi : Int) (p : ∀ v, P v ↔ v < hi) : Gen' Int P
| pick (g1 : Gen' α P₁) (g2 : Gen' α P₂) (p: ∀ v, P v ↔ P₁ v ∨ P₂ v) : Gen' α P
| bind {α β : Type} {P : α → Prop} {Q : α → β → Prop} :
  (x : Gen' α P) →
  (f : (v : α) → P v → Gen' β (Q v)) →
  Gen' β (λ v => ∃ v', P v' ∧ Q v' v)

--{P₁} {P₂} (g1 : Gen' α P₁) (f : α → Gen' β P₂)
--       (p: ∀ v, ∃ v', P₁ v' ∧ P₂ v ) : Gen' β P₂


def range : Gen' (Int × Int) (fun v => ∃ v', v' > 0 ∧ v = (0,v')) :=
  Gen'.bind (Gen'.gt 0 (by simp)) (λ (x: Int) p =>  Gen'.ret (0, x) (by simp) )



#check Gen'.ret 2

#reduce (Gen'.ret 2 )


abbrev synth_pure'
  (v' : α) :
  Gen' α (λ v => v = v') := by
  apply Gen'.ret v'
  simp

abbrev synth_gt'
  {lo : Int} :
  Gen' Int (λ v => lo < v) := by
  apply Gen'.gt lo
  intro v
  simp

abbrev synth_lt'
  {hi : Int} :
  Gen' Int (λ v => v < hi) := by
  apply Gen'.lt hi
  simp

abbrev synth_or'
  (g₁ : Gen' α P₁)
  (g₂ : Gen' α P₂) :
  Gen' α (λ v => P₁ v ∨ P₂ v) := by
  apply Gen'.pick g₁ g₂
  simp

abbrev synth_bind'
  {α β : Type}
  {P : α → Prop}
  {Q : α → β → Prop}
  (x : Gen' α P)
  (f : (v : α) → P v → Gen' β (Q v)) :
  Gen' β (λ v => ∃ v', P v' ∧ Q v' v) := by
  apply Gen'.bind x f

theorem exists_eq_fst_snd (P1: α → Prop) (P2: β → Prop) :
  ∀ t: α × β, (∃ v1: α, P1 v1 ∧ ∃ v2 : β, P2 v2 ∧ (v1,v2) = t) ↔ (P1 t.fst ∧ P2 t.snd) :=
  by
    aesop

theorem exists_eq_fst_snd2 (P1: α → Prop) (P2: α → β → Prop) :
  ∀ t: α × β, (∃ v1: α, P1 v1 ∧ ∃ v2 : β, P2 v1 v2 ∧ (v1,v2) = t) ↔ (P1 t.fst ∧ P2 t.fst t.snd) :=
  by
    aesop

theorem other_helper (t: α × β) :
  ∃ v1 : α , ∃ v2 : β, (v1,v2) = t → v1 = t.fst := by
  aesop


abbrev synth_tuple'
  {P : α → Prop}
  {Q : α → β → Prop}
  (gx : Gen' α P)
  (gy : (x : α) → Gen' β (Q x)) :
  Gen' (α × β) (λ (v: α × β) => P v.1 ∧ (Q v.1) v.2) := by
    have gen_tup := gx.bind fun (x: α) (hx: P x) =>
      (gy x).bind fun (y: β) (hy: (Q x) y) =>
        Gen'.ret (x,y) (by aesop)
    simp at gen_tup
    conv at gen_tup => (
      congr;
      intro v;
      rw [exists_eq_fst_snd2];
    )
    trivial


abbrev synth_tuple_second'
  {P : α → Prop}
  {Q : α → β → Prop}
  -- {R : α × β → Prop}
  -- {h2 : ∀ v, P v.1 ∧ Q v.1 v.2 ↔ R v}
  (x: α)
  (gy : (x : α) → Gen' β (Q x))
  (h: P x) :
  Gen' (α × β) (λ (v: α × β) => v.1 = x ∧ (Q v.1) v.2) := by
    have gen_y := (gy x)
    have gen_tup := gen_y.bind fun (v : β) (h2: (Q x) v) =>
      Gen'.ret (x,v) (by
        intro v_1;
        apply Iff.intro
        on_goal 2 => {
          intro a
          subst a
          rfl
        }
        · intro a
          simp_all only [heq_eq_eq]
      )
    simp at gen_tup

    sorry

add_aesop_rules unsafe [
  synth_pure',
  synth_gt',
  synth_lt',
  synth_or',
  synth_bind',
  synth_tuple',
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind'),
  (by (conv => congr; intro v; simp; rw[eq_comm];))
]


def genTwo: (Gen' Nat (λ v => v = 3)) := by
  --apply synth_pure'
  aesop?

#print genTwo

def genTwoAlso: (Gen' Nat (2 = .)) := by
  aesop

def getMoreThanThree : Gen' Int (λ v => v > 3) := by
  aesop

#reduce getMoreThanThree

def getLessThanThree : Gen' Int (3 > .) := by
  aesop

#reduce getLessThanThree

def getLessThanThreeAlso : Gen' Int (λ v => v < 3) := by
  aesop

#reduce getLessThanThreeAlso


def genTwoOrThreeOrFour : Gen' Nat (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
 aesop

#reduce genTwoOrThreeOrFour

def genRange: Gen' (Int × Int) (λ v => ∃ v', v' > 0 ∧ v = (0,v')) := by
  aesop?


def genRange2: Gen' (Int × Int) (λ v => v.fst = 0 ∧ v.snd > v.fst) := by
  aesop
  -- conv => congr; intro v; simp; rw[eq_comm]
  -- apply synth_tuple'
  -- on_goal 1 => {
  --   conv => congr; intro x; simp; rw[eq_comm]
  --   apply synth_pure'
  -- }
  -- intro x
  -- apply synth_gt'

  -- apply synth_tuple' (synth_pure' _) (by
  --   intro x
  --   apply synth_gt'
  -- )

#reduce genRange2

def genRange3: Gen' (Int × Int) (λ (v1,v2) => v1 = 0 ∧ v2 > v1) := by
  aesop

--def genXYOrdered : Gen' (λ (v : ℕ  × ℕ) => 0 ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ 200) := by
