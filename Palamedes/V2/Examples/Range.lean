import Palamedes.V2.Data.Nat
import Palamedes.V2.Synthesizer

def genGt5 : Gen Nat := by
  show_term
  generator_search (fun n => n > 5)

def genBetween5And10 : Gen Nat := by
  show_term
  generator_search (fun n => 5 ≤ n ∧ n ≤ 10)

def genBetweenLoAndHi (lo hi : Nat) : Gen Nat := by
  show_term
  generator_search (fun n => lo ≤ n ∧ n ≤ hi) allow_partial

def genOneOrInRange (lo hi : Nat) : Gen Nat := by
  show_term
  generator_search (fun n => n = 0 ∨ lo ≤ n ∧ n ≤ hi)
