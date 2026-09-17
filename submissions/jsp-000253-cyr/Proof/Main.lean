import Proof.Defs

/-!
# Erdős problem #301 — the lower bound `f(N) ≥ ⌈N/2⌉` and the repeated-denominator threshold

This module formalizes the two elementary remarks recorded on the problem page for Erdős
problem #301.

* The example `A = (N/2, N] ∩ ℕ` admits no relation `1/a = 1/b₁ + ⋯ + 1/b_k` in distinct
  elements (`not_hasUnitSolution_upperHalf`), and has `(N + 1) / 2` elements
  (`Erdos301.card_upperHalf`), whence `f(N) ≥ ⌈N/2⌉` (`half_le_f`).  The problem page writes this
  bound as `N/2`, while the exact count of `(N/2, N] ∩ ℕ` is `⌈N/2⌉ = (N + 1) / 2` (the two agree
  for even `N` and differ by `1/2` for odd `N`), so the bound is stated here in the sharper form
  `(N + 1) / 2 ≤ f N` with natural-number division.
* The repeated-denominator remark of Stijn Cambie and Wouter van Doorn — if the `b_i` are allowed
  to repeat, the maximal set has size at most `N/2` — is formalized as the classical primitive-set
  threshold: a relation `1/a = k · (1/b)` with `a ≠ b` is exactly `a ∣ b` with `a ≠ b`, any
  `A ⊆ {1, …, N}` with more than `⌈N/2⌉` elements contains such a pair
  (`exists_dvd_of_half_lt_card`, by mapping each element to its odd part), hence a set free of
  repeated-denominator relations has at most `⌈N/2⌉ = (N + 1) / 2` elements
  (`card_le_half_of_not_hasRepeatedUnitSolution`), and the upper half attains the threshold
  (`not_hasRepeatedUnitSolution_upperHalf`).

Not claimed here: van Doorn's upper bound `f(N) ≤ (25/28 + o(1)) N` and the question of Erdős problem #301 whether `f(N) = (1/2 + o(1)) N`.
-/

namespace Erdos301

open Finset

/-- **T2.** The upper half `(N/2, N]` carries no relation `1/a = 1/b₁ + ⋯ + 1/b_k` in distinct
elements: each `1/bᵢ` is at least `1/N` while `1/a < 2/N`, so there can be at most one term, and
a single term forces `b₁ = a`. -/
theorem not_hasUnitSolution_upperHalf (N : ℕ) : ¬ HasUnitSolution (upperHalf N) := by
  rintro ⟨a, ha, B, hB, haB, hne, hsum⟩
  obtain ⟨haN, hNa⟩ := mem_upperHalf.1 ha
  have hN0 : 0 < N := by omega
  have ha0 : 0 < a := by omega
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN0
  have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha0
  -- Every term of the sum is at least `1/N`.
  have hterm : ∀ b ∈ B, (N : ℚ)⁻¹ ≤ (b : ℚ)⁻¹ := by
    intro b hb
    obtain ⟨hbN, hNb⟩ := mem_upperHalf.1 (hB hb)
    have hb0 : 0 < b := by omega
    have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb0
    have hbN' : (b : ℚ) ≤ (N : ℚ) := by exact_mod_cast hbN
    have := one_div_le_one_div_of_le hbQ hbN'
    simpa [one_div] using this
  -- Hence the sum is at least `|B| / N`.
  have hsum_ge : (B.card : ℚ) * (N : ℚ)⁻¹ ≤ ∑ b ∈ B, (b : ℚ)⁻¹ := by
    calc (B.card : ℚ) * (N : ℚ)⁻¹ = ∑ _b ∈ B, (N : ℚ)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ B, (b : ℚ)⁻¹ := Finset.sum_le_sum hterm
  -- While `1/a < 2/N`, because `N < 2a`.
  have hupper : (a : ℚ)⁻¹ < 2 * (N : ℚ)⁻¹ := by
    have h2 : (N : ℚ) < 2 * (a : ℚ) := by exact_mod_cast hNa
    have hrw : (2 : ℚ) * (N : ℚ)⁻¹ = 2 / (N : ℚ) := by rw [div_eq_mul_inv]
    rw [hrw, inv_eq_one_div, div_lt_div_iff₀ haQ hNQ]
    linarith
  -- Therefore `|B| < 2`.
  have hNinv : (0 : ℚ) < (N : ℚ)⁻¹ := inv_pos.2 hNQ
  have hlt : (B.card : ℚ) * (N : ℚ)⁻¹ < 2 * (N : ℚ)⁻¹ := by
    calc (B.card : ℚ) * (N : ℚ)⁻¹ ≤ ∑ b ∈ B, (b : ℚ)⁻¹ := hsum_ge
      _ = (a : ℚ)⁻¹ := hsum.symm
      _ < 2 * (N : ℚ)⁻¹ := hupper
  have hcardQ : (B.card : ℚ) < 2 := lt_of_mul_lt_mul_right hlt (le_of_lt hNinv)
  have hcard2 : B.card < 2 := by exact_mod_cast hcardQ
  have hcard1 : B.card = 1 := by
    have := Finset.card_pos.2 hne
    omega
  -- A single term forces `a = b`, contradicting `a ∉ B`.
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hcard1
  rw [Finset.sum_singleton] at hsum
  have hab : a = b := by
    have h := congrArg (fun x : ℚ => x⁻¹) hsum
    simp only [inv_inv] at h
    exact_mod_cast h
  exact haB (Finset.mem_singleton.2 hab)

/-- **T1.** The lower bound of Erdős problem #301: `f(N) ≥ ⌈N/2⌉`, witnessed by the upper half
`(N/2, N]`. -/
theorem half_le_f (N : ℕ) : (N + 1) / 2 ≤ f N := by
  classical
  rw [← card_upperHalf N]
  unfold f
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), not_hasUnitSolution_upperHalf N⟩)

/-- **T4.** The classical primitive-set threshold: any `A ⊆ {1, …, N}` with more than `⌈N/2⌉`
elements contains distinct `a, b` with `a ∣ b`.  Map each element to its odd part; there are only
`⌈N/2⌉ = (N + 1) / 2` odd numbers in `{1, …, N}`, so two elements share an odd part, and then the
one with the smaller `2`-adic valuation divides the other. -/
theorem exists_dvd_of_half_lt_card (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : (N + 1) / 2 < A.card) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∣ b := by
  classical
  set T : Finset ℕ := (Finset.Icc 1 N).filter (fun m => ¬ 2 ∣ m) with hT
  -- `T` is the set of odd numbers in `{1, …, N}`; it has `(N + 1) / 2` elements.
  have hTcard : T.card = (N + 1) / 2 := by
    have himg : T = (Finset.range ((N + 1) / 2)).image (fun i => 2 * i + 1) := by
      ext m
      simp only [hT, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨hm1, hm2⟩, hodd⟩
        exact ⟨m / 2, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hinj : Function.Injective (fun i : ℕ => 2 * i + 1) := by
      intro x y hxy
      simp only at hxy
      omega
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range]
  -- The odd part of an element of `A` lies in `T`.
  have hmaps : ∀ n ∈ A, ordCompl[2] n ∈ T := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 (hA hn)
    have hn0 : n ≠ 0 := by omega
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.ordCompl_pos 2 hn0, le_trans (Nat.ordCompl_le n 2) hn2⟩,
      Nat.not_dvd_ordCompl Nat.prime_two hn0⟩
  obtain ⟨x, hx, y, hy, hxy, hval⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hTcard]; exact h) hmaps
  have hxe : ordProj[2] x * ordCompl[2] x = x := Nat.ordProj_mul_ordCompl_eq_self x 2
  have hye : ordProj[2] y * ordCompl[2] y = y := Nat.ordProj_mul_ordCompl_eq_self y 2
  rcases le_total (x.factorization 2) (y.factorization 2) with hle | hle
  · refine ⟨x, hx, y, hy, hxy, ?_⟩
    have h1 : ordProj[2] x * ordCompl[2] x ∣ ordProj[2] y * ordCompl[2] y :=
      mul_dvd_mul (pow_dvd_pow 2 hle) hval.dvd
    rwa [hxe, hye] at h1
  · refine ⟨y, hy, x, hx, hxy.symm, ?_⟩
    have h1 : ordProj[2] y * ordCompl[2] y ∣ ordProj[2] x * ordCompl[2] x :=
      mul_dvd_mul (pow_dvd_pow 2 hle) hval.symm.dvd
    rwa [hxe, hye] at h1

/-- **T5.** The Cambie–van Doorn remark: if repeated denominators are allowed, a relation-free
subset of `{1, …, N}` has at most `⌈N/2⌉ = (N + 1) / 2` elements.  Indeed `a ∣ b` with `a ≠ b`
gives `1/a = k · (1/b)` with `b = k a`, so this is the contrapositive of the primitive-set
threshold. -/
theorem card_le_half_of_not_hasRepeatedUnitSolution (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : ¬ HasRepeatedUnitSolution A) : A.card ≤ (N + 1) / 2 := by
  by_contra hc
  obtain ⟨a, ha, b, hb, hab, k, hk⟩ := exists_dvd_of_half_lt_card N A hA (not_le.1 hc)
  have ha1 : 1 ≤ a := (Finset.mem_Icc.1 (hA ha)).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.1 (hA hb)).1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.mul_zero] at hk
      omega
    · exact h0
  refine h ⟨a, ha, b, hb, hab, k, hk0, ?_⟩
  have haQ : (a : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha1
    exact ne_of_gt this
  have hkQ : (k : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk0
    exact ne_of_gt this
  have hbQ : (b : ℚ) = (a : ℚ) * (k : ℚ) := by exact_mod_cast hk
  rw [hbQ, mul_inv, ← mul_assoc, mul_comm (k : ℚ) (a : ℚ)⁻¹, mul_assoc,
    mul_inv_cancel₀ hkQ, mul_one]

/-- **T6.** The upper half attains the threshold of `card_le_half_of_not_hasRepeatedUnitSolution`:
it carries no repeated-denominator relation either, since `a ∣ b` with `a ≠ b` in `(N/2, N]` would
force `b ≥ 2a > N`. -/
theorem not_hasRepeatedUnitSolution_upperHalf (N : ℕ) : ¬ HasRepeatedUnitSolution (upperHalf N) := by
  rintro ⟨a, ha, b, hb, hab, k, hk, heq⟩
  obtain ⟨haN, hNa⟩ := mem_upperHalf.1 ha
  obtain ⟨hbN, hNb⟩ := mem_upperHalf.1 hb
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have haQ : (a : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha0
    exact ne_of_gt this
  have hbQ : (b : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb0
    exact ne_of_gt this
  -- Clearing denominators in `1/a = k/b` gives `b = k a`.
  have hEq : (b : ℚ) = (k : ℚ) * (a : ℚ) := by
    field_simp at heq
    linarith
  have hbk : b = k * a := by exact_mod_cast hEq
  have hk2 : 2 ≤ k := by
    by_contra hcon
    have hk1 : k = 1 := by omega
    rw [hk1, one_mul] at hbk
    exact hab hbk.symm
  have hb2 : 2 * a ≤ b := by
    rw [hbk]
    exact Nat.mul_le_mul hk2 (le_refl a)
  omega

end Erdos301
