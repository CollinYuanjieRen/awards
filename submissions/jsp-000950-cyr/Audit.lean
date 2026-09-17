import Erdos1145EvenOdd

open Set AdditiveCombinatorics

#print axioms erdos_1145_evenOdd_sumConv

/-- Erdős #1145: the even/odd binary-digit sets have `1_A ∗ 1_B(n) = 1` for all `n`. -/
example (n : ℕ) : ((𝟙_evenBitSet ∗ 𝟙_oddBitSet : ℕ → ℕ) n) = 1 := erdos_1145_evenOdd_sumConv n

/-- The definitions are the formal-conjectures ones. -/
example {R : Type*} [Semiring R] (f g : ℕ → R) (n : ℕ) :
    sumConv f g n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2 := rfl
example {α R : Type*} [One R] [Zero R] (A : Set α) : (indicatorOne A : α → R) = indicator A (fun _ ↦ 1) := rfl
