import Palamedes.Basic
import Palamedes.Examples.Inductive
import Palamedes.Examples.STLC
import Palamedes.Examples.BST

#eval sampleN 10 (genBST 50 100).val
#eval sampleN 10 (.pick (.assume false (λ _ => .ret 2)) (.ret 3))

def main := IO.print =<< sampleN 10 (genSortedBetween 2 10).val
