import Palamedes.V2.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genAllTwosFold : Gen (List Nat) := by
  generator_search fun xs =>
    List.fold (fun x b => x == 2 && b) true xs = true

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => (fun _ => true) x && b) true xs = true)
