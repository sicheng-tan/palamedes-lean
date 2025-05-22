import Palamedes.V2.Synthesizer
import Palamedes.V2.Data.Arbitrary

def genUnit : Gen Unit := by
  generator_search (fun _ => True)

def genBool : Gen Bool := by
  generator_search (fun _ => True)

def genNat : Gen Nat := by
  generator_search (fun _ => True)
