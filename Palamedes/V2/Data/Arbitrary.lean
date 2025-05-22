import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.RuleSets
import Palamedes.V2.Optimizer

namespace Gen

class Arbitrary (α : Type) where
  arbitrary : @CorrectGen α (fun _ => True)

instance : Arbitrary Unit where
  arbitrary := Subtype.mk (pure ()) <| by
    simp

instance : Arbitrary Bool where
  arbitrary := Subtype.mk (pick (pure true) (pure false)) <| by
    simp

private def arbNat : Nat → Gen (Option Nat)
  | 0 => pure none
  | n + 1 => pick (pure (some 0)) (.map (1 + .) <$> arbNat n)

instance : Arbitrary Nat where
  arbitrary :=
    Subtype.mk (indexed arbNat) <| by
      simp
      funext v
      induction v with
      | zero => simp; exists 1; simp [arbNat]
      | succ n ih =>
        simp_all
        have ⟨n', hn'⟩ := ih
        exists n' + 1
        simp [arbNat]
        exists some n
        simp +arith [hn']

namespace CorrectGen

@[reducible]
def caribtrary [Arbitrary α] : @CorrectGen α (fun _ => True) :=
  Arbitrary.arbitrary

end CorrectGen

namespace Total

@[simp]
def total_arb_Unit : total (Arbitrary.arbitrary.val : Gen Unit) := by
  simp [instArbitraryUnit]

@[simp]
def total_arb_Bool : total (Arbitrary.arbitrary.val : Gen Bool) := by
  simp [instArbitraryBool]

@[simp]
def total_arb_Nat : total (Arbitrary.arbitrary.val : Gen Nat) := by
  simp [instArbitraryNat]
  apply total_indexed
  intro n
  induction n <;> simp_all [arbNat]

end Total

namespace OptGen

@[simp]
def opt_arb_Unit_self : OptGen (Arbitrary.arbitrary.val : Gen Unit) :=
  Subtype.mk (Arbitrary.arbitrary.val : Gen Unit) rfl

@[simp]
def opt_arb_Bool_self : OptGen (Arbitrary.arbitrary.val : Gen Bool) :=
  Subtype.mk (Arbitrary.arbitrary.val : Gen Bool) rfl

@[simp]
def opt_arb_Nat_self : OptGen (Arbitrary.arbitrary.val : Gen Nat) :=
  Subtype.mk (Arbitrary.arbitrary.val : Gen Nat) rfl

end OptGen

end Gen

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by apply Gen.CorrectGen.caribtrary),
]

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by apply Gen.Gen.OptGen.opt_arb_Unit_self),
  (by apply Gen.Gen.OptGen.opt_arb_Bool_self),
  (by apply Gen.Gen.OptGen.opt_arb_Nat_self),
]
