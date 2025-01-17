import Palamedes.Synth

@[aesop unsafe [constructors, cases]]
inductive OneOrTwo : Nat → Prop where
  | one : OneOrTwo 1
  | two : OneOrTwo 2

def synth_OneOrTwo_one : CGen (λ v => v = 1 ∧ OneOrTwo v) := by
  exists pure 1
  aesop

def synth_OneOrTwo_two : CGen (λ v => v = 2 ∧ OneOrTwo v) := by
  exists pure 2
  aesop
