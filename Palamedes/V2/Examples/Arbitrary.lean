import Palamedes.V2.Synthesizer
import Palamedes.V2.Data.Unit
import Palamedes.V2.Data.Nat
import Palamedes.V2.Data.Bool

def genUnit : Gen Unit := by
  show_term
  generator_search (fun _ => True)

def genBool : Gen Bool := by
  show_term
  generator_search (fun _ => True)

def genNat : Gen Nat := by
  show_term
  generator_search (fun _ => True)
