import Aesop
inductive Gen' : (α : Type) → (P: α → Prop) → Type 1 where
| ret (r : α) (p : ∀ v, P v ↔ v = r) : Gen' α P
| gt (lo : Int) (p : ∀ v, P v ↔ v > lo) : Gen' Int P
| lt (hi : Int) (p : ∀ v, P v ↔ v < hi) : Gen' Int P
| pick (g1 : Gen' α P₁) (g2 : Gen' α P₂) (p: ∀ v, P v ↔ P₁ v ∨ P₂ v) : Gen' α P
| bind {P₁} {P₂} (g1 : Gen' α P₁) (f : α → Gen' β P₂)
       (p: ∀ v, ∃ v', P₁ v' ∧ P₂ v ) : Gen' β P₂


def range : Gen' (Int × Int) (fun (v1,v2) => v1 = 0 ∧ v2 > v1) :=
  -- Gen'.bind
  --   (Gen'.gt 0 _)
  --   (λ v => (Gen'.ret (0,v) _))
  --   _
  Gen'.bind (Gen'.gt 0 _) (λ x => (Gen'.ret (0, x) _)) _

-- instance : Monad Gen' where
--   pure := .ret
--   bind := .bind

#check Gen'.ret 2 --(λ v => v = 2)


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

add_aesop_rules unsafe [
  synth_pure',
  synth_gt',
  synth_lt',
  synth_or'
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
