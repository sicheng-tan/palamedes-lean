import Palamedes.Free
import Palamedes.Support
import Palamedes.Synth
import Palamedes.Util

attribute [simp] guard
attribute [-simp] Prod.forall
attribute [aesop safe apply] synth_match

#print CGen

example : CGen (λ v => v = 1 ∨ v = 2) := by
  apply synth_or
  . apply synth_pure
  . apply synth_pure

#print synth_or

@[simp]
abbrev genOneOrTwo : CGen (λ v => v = 1 ∨ v = 2) := by
  aesop

#eval traceConstWithTransparency .reducible ``genOneOrTwo

def isAllTwos (v : List Nat) : Option Unit :=
  List.foldrM
    (λ x () => guard (x == 2))
    ()
    v

abbrev genAllTwos : CGen (λ v => isAllTwos v = Option.some ()) := by
  delta isAllTwos
  aesop

#eval traceConstWithTransparency .reducible ``genAllTwos
