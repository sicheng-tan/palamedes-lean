import Palamedes.V2.Synthesizer

def genEq2 : Gen Nat := by
  show_term
  generator_search (· = 2)

def genEq2' : Gen Nat := by
  show_term
  generator_search (2 = ·)

def genEq2Or5 : Gen Nat := by
  show_term
  generator_search (fun a => a = 2 ∨ a = 5)

def genEq2Or5' : Gen Nat := by
  show_term
  generator_search (fun a => a = 2 ∨ a = 5 ∧ True)

def genThreePlusOne : Gen Nat := by
  show_term
  generator_search (fun b => ∃ a, a = 3 ∧ b = a + 1) allow_partial
