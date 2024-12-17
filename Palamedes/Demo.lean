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

@[simp]
abbrev genOneOrTwo : CGen (λ v => v = 1 ∨ v = 2) := by
  aesop

#eval traceConstWithTransparency .reducible ``genOneOrTwo

def isAllTwos (v : List Int) :  Prop :=
  List.foldrM
    (λ x () => guard (x == 2))
    ()
    v = Option.some ()

abbrev genAllTwos : CGen isAllTwos := by
  aesop

#eval traceConstWithTransparency .reducible ``genAllTwos
