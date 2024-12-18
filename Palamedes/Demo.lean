import Palamedes.Free
import Palamedes.Support
import Palamedes.Synth
import Palamedes.Util

attribute [simp] guard
attribute [-simp] Prod.forall
attribute [aesop safe apply] synth_match

#print CGen

example : CGen (λ x => x = 1 ∨ x = 2) := by
  apply synth_or
  . apply synth_pure
  . apply synth_pure

#print synth_or

abbrev genOneOrTwo : CGen (λ x => x = 1 ∨ x = 2) := by
  aesop

#eval traceConstWithTransparency .reducible ``genOneOrTwo

def isAllTwos (xs : List Nat) : Option Unit :=
  List.foldrM
    (λ x () => guard (x == 2))
    ()
    xs

abbrev genAllTwos : CGen (λ xs => isAllTwos xs = Option.some ()) := by
  aesop

#eval traceConstWithTransparency .reducible ``genAllTwos
