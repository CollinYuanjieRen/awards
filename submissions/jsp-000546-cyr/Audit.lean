import Erdos672Fuhrer

#print axioms erdos_672_fuhrer_example
#print axioms erdos_672_exists_int_ap_cube

/-- Erdős #672: Führer's integer example. -/
example : Int.gcd (-6) 5 = 1 ∧ (∏ i ∈ Finset.range 4, ((-6 : ℤ) + (i : ℤ) * 5)) = 6 ^ 3 :=
  erdos_672_fuhrer_example
