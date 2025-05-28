import Palamedes.V2.Data.List
import Palamedes.V2.Data.Nat
import Palamedes.V2.Data.Unit
import Palamedes.V2.Synthesizer
import Palamedes.V2.Tactics
import Palamedes.V2.RuleSets

open Gen CorrectGen

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => x == 2 && b) true xs = true)
