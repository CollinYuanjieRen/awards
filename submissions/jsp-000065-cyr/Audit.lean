import Erdos36MinimumOverlap

open Filter

#print axioms minimum_overlap_upper_erdos_1955
#print axioms two_mul_M_le
#print axioms overlap_erdosInterval_le

/-- Erdős #36, Erdős's 1955 example, in the formal-conjectures shape
`minimum_overlap.variants.upper.erdos_1955`. -/
example : atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 := minimum_overlap_upper_erdos_1955

/-- The explicit bound behind it. -/
example (N : ℕ) : 2 * M N ≤ N + 1 := two_mul_M_le N

/-- The definitions are the formal-conjectures ones. -/
example (N : ℕ) : MinOverlapQuotient N = (M N : ℝ) / N := rfl
example (A B : Finset ℤ) : MaxOverlap A B = iSup (Overlap A B) := rfl
