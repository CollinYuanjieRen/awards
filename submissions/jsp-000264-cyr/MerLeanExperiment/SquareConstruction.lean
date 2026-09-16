import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace ReciprocalSquares

/-- Smoothness uses primes at most `N`, hence the library parameter `N + 1`. -/
def smoothRoots (N : ℕ) : Finset ℕ :=
  (Finset.range (N ^ 3)).filter (fun a => a ∈ Nat.smoothNumbers (N + 1))

def largePrimes (N : ℕ) : Finset ℕ :=
  (Nat.primesBelow (N ^ 3)).filter (fun p => N < p)

def rootProduct (aS : ℕ × Finset ℕ) : ℕ := aS.1 * aS.2.prod id

/-- Large prime factors occur at most once in a root, keeping the resulting
denominators products of prime squares, rather than arbitrary divisors. -/
def rootsZ (N : ℕ) : Finset ℕ :=
  ((smoothRoots N).product (largePrimes N).powerset).image rootProduct

def squareB (N : ℕ) : Finset ℕ := (smoothRoots N).image (fun a => a ^ 2)
def squareQ (N : ℕ) : Finset ℕ := (largePrimes N).image (fun p => p ^ 2)
def squareZ (N : ℕ) : Finset ℕ := (rootsZ N).image (fun a => a ^ 2)

/-- The erased prefix is exact and includes one. -/
def prefixRoots (N : ℕ) : Finset ℕ :=
  (Finset.range (N ^ 2)).filter (fun a => a ∈ Nat.smoothNumbers (N + 1))

def squareE (N : ℕ) : Finset ℕ := (prefixRoots N).image (fun a => a ^ 2)
def squareD (N : ℕ) : Finset ℕ := squareZ N \ squareE N

theorem largePrimes_prime {N p : ℕ} (hp : p ∈ largePrimes N) : p.Prime :=
  Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1

theorem rootsZ_pos {N a : ℕ} (ha : a ∈ rootsZ N) : 0 < a := by
  obtain ⟨⟨b, S⟩, hpair, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hb, hS⟩ := Finset.mem_product.mp hpair
  have hbpos : 0 < b := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (Finset.mem_filter.mp hb).2)
  unfold rootProduct
  apply Nat.mul_pos hbpos
  apply Finset.prod_pos
  intro p hp
  exact (largePrimes_prime (Finset.mem_powerset.mp hS hp)).pos

theorem smoothRoots_subset_rootsZ (N : ℕ) : smoothRoots N ⊆ rootsZ N := by
  intro a ha
  apply Finset.mem_image.mpr
  refine ⟨(a, ∅), Finset.mem_product.mpr ⟨ha, by simp⟩, ?_⟩
  simp [rootProduct]

theorem prefixRoots_subset_smoothRoots (N : ℕ) (hN : 1 ≤ N) :
    prefixRoots N ⊆ smoothRoots N := by
  have hpow : N ^ 2 ≤ N ^ 3 := by
    calc
      N ^ 2 = N ^ 2 * 1 := by omega
      _ ≤ N ^ 2 * N := Nat.mul_le_mul_left _ hN
      _ = N ^ 3 := by ring
  intro a ha
  obtain ⟨ha, hsmooth⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ((Finset.mem_range.mp ha).trans_le hpow), hsmooth⟩

theorem squareE_subset_squareZ (N : ℕ) (hN : 1 ≤ N) :
    squareE N ⊆ squareZ N := by
  apply Finset.image_subset_image
  exact (prefixRoots_subset_smoothRoots N hN).trans (smoothRoots_subset_rootsZ N)

theorem one_mem_squareE (N : ℕ) (hN : 2 ≤ N) : 1 ∈ squareE N := by
  apply Finset.mem_image.mpr
  refine ⟨1, ?_, by norm_num⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    nlinarith
  · simp only [Nat.mem_smoothNumbers]
    exact ⟨by decide, by simp⟩

theorem squareD_members (N : ℕ) (hN : 2 ≤ N) :
    ∀ n ∈ squareD N, 1 < n ∧ IsSquare n := by
  intro n hn
  obtain ⟨hnZ, hnE⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnZ
  have hapos := rootsZ_pos ha
  have hne : a ^ 2 ≠ 1 := by
    intro heq
    exact hnE (heq.symm ▸ one_mem_squareE N hN)
  constructor
  · have hsqpos : 0 < a ^ 2 := pow_pos hapos _
    omega
  · exact ⟨a, pow_two a⟩

end ReciprocalSquares
