import Palamedes.Synth

#print Gen

#print support

#print CGen

#print synth_pure
#print synth_or

def genOneOrTwo : CGen (λ v => v = 1 ∨ v = 2) := by
  apply synth_or
  . apply synth_pure
  . apply synth_pure

def genOne'_fails : CGen (λ v => 1 = v) := by
  try apply synth_pure -- Fails!
  sorry

#print synth_cut

def genOne' : CGen (λ v => 1 = v) := by
  apply synth_cut eq_comm
  apply synth_pure
