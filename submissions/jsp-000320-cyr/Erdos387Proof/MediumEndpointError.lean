import Erdos387Proof.MediumSignedMainTerm

/-! Finite arithmetic envelopes for the harmonic endpoint errors.  The signed
main terms remain in `MediumSignedMainTerm`; only their errors are enlarged. -/

namespace Erdos387Proof.MediumEndpointError

open scoped BigOperators
open MediumZeroMode

/-- Divisor counting is submultiplicative, without a coprimality hypothesis. -/
theorem card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have hsub : (m * n).divisors ⊆
      (m.divisors ×ˢ n.divisors).image (fun ab => ab.1 * ab.2) := by
    intro d hd
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hd)
    exact Finset.mem_image.mpr ⟨(a, b),
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨ha, hm⟩,
        Nat.mem_divisors.mpr ⟨hb, hn⟩⟩, hab.symm⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans_eq (Finset.card_product _ _))

theorem card_divisors_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hn,
    Finset.card_image_of_injOn (Erdos387.prod_primeFactorSubsets_injOn n),
    Finset.card_powerset]

/-- Uniform error for one squarefree Brun modulus.  No coprimality is needed
for this error estimate. -/
theorem endpointError_le {g M D k A W L : ℕ} (hg : Squarefree g)
    (hD : Squarefree D) (hgL : g.primeFactors.card ≤ L)
    (hDW : D.primeFactors.card ≤ W) (hk : 1 ≤ k) (hA : 0 < A)
    {mass : ℝ} (hmass : 0 ≤ mass) :
    endpointError g (M * D) k A mass ≤
      4 * mass / ((M : ℝ) * D * A) * M.divisors.card * 2 ^ W *
        (4 * (k : ℝ)) ^ L := by
  classical
  by_cases hM : M = 0
  · simp [endpointError, hM]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero hg.ne_zero
  have hD0 : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD.ne_zero
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgcard : (g.divisors.card : ℝ) ≤ 2 ^ L := by
    rw [card_divisors_squarefree hg]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hgL)
  have hDcard : D.divisors.card ≤ 2 ^ W := by
    rw [card_divisors_squarefree hD]
    exact Nat.pow_le_pow_right (by omega) hDW
  let C : ℝ := (k : ℝ) ^ L * mass / ((M : ℝ) * D * g) *
    (4 * M.divisors.card * 2 ^ W * 2 ^ L * g / A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ u ∈ g.divisors,
      (k : ℝ) ^ (g / u).primeFactors.card * mass / (M * D * g : ℕ) *
        (4 * (M * D * (g / u)).divisors.card * u / A) ≤ C := by
    intro u hu
    have hv : g / u ∣ g := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hu)
    have hvL : (g / u).primeFactors.card ≤ L :=
      (Finset.card_le_card (Nat.primeFactors_mono hv hg.ne_zero)).trans hgL
    have hvcard : (g / u).divisors.card ≤ 2 ^ L := by
      rw [card_divisors_squarefree (hg.squarefree_of_dvd hv)]
      exact Nat.pow_le_pow_right (by omega) hvL
    have hcount : (M * D * (g / u)).divisors.card ≤
        M.divisors.card * 2 ^ W * 2 ^ L := by
      exact (card_divisors_mul_le (M * D) (g / u)).trans
        (Nat.mul_le_mul
          ((card_divisors_mul_le M D).trans (Nat.mul_le_mul_left _ hDcard)) hvcard)
    have hcountR : ((M * D * (g / u)).divisors.card : ℝ) ≤
        M.divisors.card * 2 ^ W * 2 ^ L := by exact_mod_cast hcount
    have huR : (u : ℝ) ≤ g := by exact_mod_cast Nat.divisor_le hu
    dsimp [C]
    push_cast
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk1 hvL) hmass) (by positivity)
    · apply div_le_div_of_nonneg_right _ (le_of_lt hA0)
      calc
        4 * ((M * D * (g / u)).divisors.card : ℝ) * u ≤
            4 * (M.divisors.card * 2 ^ W * 2 ^ L) * g :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcountR (by norm_num)) huR
            (by positivity) (by positivity)
        _ = 4 * M.divisors.card * 2 ^ W * 2 ^ L * g := by ring
    · positivity
    · positivity
  calc
    endpointError g (M * D) k A mass ≤ ∑ _u ∈ g.divisors, C :=
      Finset.sum_le_sum hterm
    _ = (g.divisors.card : ℝ) * C := by simp
    _ ≤ 2 ^ L * C := mul_le_mul_of_nonneg_right hgcard hC
    _ = 4 * mass / ((M : ℝ) * D * A) * M.divisors.card * 2 ^ W *
        (4 * (k : ℝ)) ^ L := by
      dsimp [C]
      rw [mul_pow]
      have hfour : (4 : ℝ) ^ L = 2 ^ L * 2 ^ L := by rw [← mul_pow]; norm_num
      rw [hfour]
      field_simp

/-- A deliberately loose count for all subsets up to a fixed size. -/
theorem card_truncated_powerset_le {P : Finset ℕ} {z L : ℕ}
    (hP : P ⊆ Finset.range z) (hz : 1 ≤ z) :
    (P.powerset.filter (fun T => T.card ≤ L)).card ≤ (L + 1) * z ^ L := by
  classical
  have hsub : P.powerset.filter (fun T => T.card ≤ L) ⊆
      (Finset.range (L + 1)).biUnion (fun j => P.powersetCard j) := by
    intro T hT
    obtain ⟨hTP, hTL⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_biUnion.mpr ⟨T.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hTP, rfl⟩⟩
  have hcard : P.card ≤ z := by simpa using Finset.card_le_card hP
  calc
    _ ≤ ((Finset.range (L + 1)).biUnion (fun j => P.powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (L + 1), (P.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (L + 1), z ^ L := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left hcard j).trans (Nat.pow_le_pow_right hz (by have := Finset.mem_range.mp hj; omega)))
    _ = (L + 1) * z ^ L := by simp

/-- Sum of the endpoint errors over the actual truncated prime-subset family. -/
theorem sum_endpointError_le {P : Finset ℕ} {M D k A W L z : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hPz : P ⊆ Finset.range z) (hz : 1 ≤ z)
    (hD : Squarefree D) (hDW : D.primeFactors.card ≤ W)
    (hk : 1 ≤ k) (hA : 0 < A) {mass : ℝ} (hmass : 0 ≤ mass) :
    (∑ T ∈ P.powerset, if T.card ≤ L then
        endpointError (∏ p ∈ T, p) (M * D) k A mass else 0) ≤
      ((L + 1 : ℕ) : ℝ) * z ^ L *
        (4 * mass / ((M : ℝ) * D * A) * M.divisors.card * 2 ^ W *
          (4 * (k : ℝ)) ^ L) := by
  classical
  rw [← Finset.sum_filter]
  let C : ℝ := 4 * mass / ((M : ℝ) * D * A) * M.divisors.card * 2 ^ W *
    (4 * (k : ℝ)) ^ L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ _T ∈ P.powerset.filter (fun T => T.card ≤ L), C := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hTP, hTL⟩ := Finset.mem_filter.mp hT
      have hsub := Finset.mem_powerset.mp hTP
      apply endpointError_le (MediumSignedMainTerm.primeSubsetProduct_squarefree hP hsub)
        hD _ hDW hk hA hmass
      simpa [Nat.primeFactors_prod (fun p hp => hP p (hsub hp))] using hTL
    _ = ((P.powerset.filter (fun T => T.card ≤ L)).card : ℝ) * C := by simp
    _ ≤ ((L + 1 : ℕ) : ℝ) * z ^ L * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast card_truncated_powerset_le hPz hz

/-- The signed zero-mode sum has the actual Brun main term and the explicit
finite endpoint envelope.  No absolute values are applied to main coefficients. -/
theorem abs_signed_zeroMode_sub_brun_le {P : Finset ℕ} {M D k A B W L z : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hPz : P ⊆ Finset.range z) (hz : 1 ≤ z)
    (hM : 0 < M) (hD : Squarefree D) (hDW : D.primeFactors.card ≤ W)
    (hcop : ∀ p ∈ P, Nat.Coprime (M * D) p)
    (hk : 1 ≤ k) (hA : 0 < A) (hAB : A ≤ B) {mass : ℝ} (hmass : 0 ≤ mass) :
    |(∑ T ∈ P.powerset, MediumSignedMainTerm.coefficient L T *
        zeroMode (∏ p ∈ T, p) (M * D) k A B mass) -
      MediumSignedMainTerm.prefactor (M * D) A B mass *
        Erdos387.brunSubsetSum P (MediumSieveEuler.alpha k) L| ≤
      ((L + 1 : ℕ) : ℝ) * z ^ L *
        (4 * mass / ((M : ℝ) * D * A) * M.divisors.card * 2 ^ W *
          (4 * (k : ℝ)) ^ L) := by
  exact (MediumSignedMainTerm.abs_sum_zeroMode_sub_brun_le P k L (M * D) A B
    mass hmass (Nat.mul_pos hM (Nat.pos_of_ne_zero hD.ne_zero)) hA hAB hP hcop).trans
      (sum_endpointError_le hP hPz hz hD hDW hk hA hmass)

end Erdos387Proof.MediumEndpointError
