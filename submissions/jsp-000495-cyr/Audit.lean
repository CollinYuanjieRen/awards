import Proof

open Erdos609

#print axioms Erdos609.exists_colouring_no_oddCycle
#print axioms Erdos609.exists_mono_oddCycle
#print axioms Erdos609.oddCycleThreshold_le
#print axioms Erdos609.oddCycleThreshold_mem

example : ∀ n : ℕ, ∃ c : Sym2 (Fin (2 ^ (n + 1))) → Fin (n + 1), ∀ i, ¬ HasOddCycle (colourClass c i) :=
  Erdos609.exists_colouring_no_oddCycle
example : ∀ (n : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n), ∃ i, HasOddCycle (colourClass c i) :=
  Erdos609.exists_mono_oddCycle
example : ∀ n : ℕ, oddCycleThreshold n ≤ 2 ^ n + 1 := Erdos609.oddCycleThreshold_le
example : ∀ n : ℕ, ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n,
    ∃ i, HasOddCycleLe (colourClass c i) (oddCycleThreshold n) :=
  Erdos609.oddCycleThreshold_mem

#print Erdos609.colourClass
#print Erdos609.HasOddCycle
#print Erdos609.HasOddCycleLe
#print Erdos609.oddCycleThreshold
