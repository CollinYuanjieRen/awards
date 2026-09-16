import MerLeanExperiment.FiniteAvoidance
import MerLeanExperiment.LinearResidues
import MerLeanExperiment.SieveLength

namespace Erdos441

open scoped BigOperators

theorem chen_uniform_linear_avoidance (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x → ∀ c1 c2 : ℝ, c0 ≤ c1 →
      ∀ t : ℕ, 2 * t ≤ M → ∀ A B : Fin t → ℤ,
      (∀ i, IsCoprime (A i) (B i)) →
      (∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
        ¬ (p : ℤ) ∣ ∏ i, (A i * n + B i)) →
      ∃ k : ℤ, c1 * x ^ (1 / 2 : ℝ) + c2 < (k : ℝ) ∧
        (k : ℝ) < c1 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ)) + c2 ∧
        ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ∏ i, (A i * k + B i) →
          Real.log x / (8 * Real.log M) < (p : ℝ) := by
  classical
  obtain ⟨X, hX⟩ := (Filter.eventually_atTop.1 (eventually_sieve_length M hM c0 hc0))
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx c1 c2 hc1 t ht A B hprim hsmall
  have hx1 : 1 ≤ x := le_trans (le_max_left 1 X) hx
  have hxX : X ≤ x := le_trans (le_max_right 1 X) hx
  have hlen0 := hX x hxX
  let q : ℝ := Real.log x / (8 * Real.log M)
  let Z : ℕ := ⌊q⌋₊
  let L : ℝ := c1 * x ^ (1 / 2 : ℝ) + c2
  let U : ℝ := c1 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ)) + c2
  let a : ℤ := ⌊L⌋
  let b : ℤ := ⌈U⌉ - 1
  have hc1pos : 0 < c1 := lt_of_lt_of_le hc0 hc1
  have hLU : U - L = c1 * x ^ (1 / 4 : ℝ) := by
    dsimp [L, U]
    ring
  have hpowlen : (((2 * M) ^ Z : ℕ) : ℝ) < U - L - 1 := by
    dsimp [Z, q]
    rw [hLU]
    exact hlen0.trans_le (by gcongr)
  have hbaReal : U - L - 1 ≤ ((b - a : ℤ) : ℝ) := by
    have hfl : (a : ℝ) ≤ L := by exact Int.floor_le L
    have hce : U - 1 ≤ (b : ℝ) := by
      dsimp [b]
      push_cast
      have := Int.le_ceil U
      linarith
    push_cast
    linarith
  have hab : a ≤ b := by
    have : (0 : ℝ) < ((b - a : ℤ) : ℝ) := lt_of_lt_of_le
      (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (((2 * M) ^ Z : ℕ) : ℝ)) hpowlen) hbaReal
    exact sub_nonneg.mp (by exact_mod_cast this.le)
  have hlength : (((2 * M) ^ Z : ℕ) : ℤ) < b - a := by
    exact_mod_cast hpowlen.trans_le hbaReal
  have hprime (p : SievePrime Z) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  let R : (p : SievePrime Z) → Finset (ZMod p.val) := fun p =>
    @linearBadResidues p.val ⟨hprime p⟩ (Fin t) inferInstance A B
  have hRsmall : ∀ p, p.val ≤ M → R p = ∅ := by
    intro p hpM
    exact @linear_bad_residues_empty p.val ⟨hprime p⟩ (Fin t) inferInstance A B
      hprim (hsmall p.val (hprime p) hpM)
  have hRcard : ∀ p, 2 * (R p).card ≤ M := by
    intro p
    exact (Nat.mul_le_mul_left 2
      (@linear_bad_residue_spec p.val ⟨hprime p⟩ (Fin t) inferInstance A B hprim).1).trans
      (by simpa using ht)
  obtain ⟨k, hkIoc, hkavoid⟩ := exists_interval_avoiding M Z hM a b hab R hRsmall hRcard hlength
  have hkLower : L < (k : ℝ) := by
    have hLfloor : L < (a : ℝ) + 1 := by exact Int.lt_floor_add_one L
    have hak : a < k := (Finset.mem_Ioc.mp hkIoc).1
    exact hLfloor.trans_le (by exact_mod_cast hak)
  have hkUpper : (k : ℝ) < U := by
    have hkb : k ≤ b := (Finset.mem_Ioc.mp hkIoc).2
    have hbU : (b : ℝ) < U := by
      dsimp [b]
      push_cast
      have := Int.ceil_lt_add_one U
      linarith
    have hkb' : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb
    exact hkb'.trans_lt hbU
  refine ⟨k, ?_, ?_, ?_⟩
  · exact hkLower
  · exact hkUpper
  intro p hp hdiv
  by_contra hpq
  have hpqle : (p : ℝ) ≤ q := le_of_not_gt hpq
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Real.log_nonneg hx1) (by
      have : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
      positivity)
  have hpZ : p ≤ Z := by
    dsimp [Z]
    exact Nat.le_floor hpqle
  have hp1 : 1 ≤ p := hp.one_le
  let sp : SievePrime Z := ⟨p, by simp [sievePrimes, hp1, hpZ, hp]⟩
  have hmem : (k : ZMod p) ∈ R sp := by
    exact ((@linear_bad_residue_spec p ⟨hp⟩ (Fin t) inferInstance A B hprim).2 k).mpr hdiv
  exact hkavoid sp hmem

end Erdos441
