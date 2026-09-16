import ErdosProblems.Erdos387.InversePhaseOrthogonality

/-!
The complete Fourier modulus may contain factors at which the phase coefficient
is not a unit. It suffices to cancel the coefficient after projecting to a
divisor of that modulus. This is the precise distinction needed in BNPZ, Lemma 9.2.

The denominator-clearing algebra follows the pinned plby InversePhaseOrthogonality
module; the projection and the weaker, use-site-correct coprimality are new here.
-/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators

theorem modEq_div_gcd_of_phase_eq_projected
    {q D h a r₁ r₂ : ℕ} (hD : 0 < D) (hDq : D ∣ q)
    (ha : a.Coprime D) (hr₁ : r₁.Coprime q) (hr₂ : r₂.Coprime q)
    (hphase : InversePhase.phase q h a r₁ = InversePhase.phase q h a r₂) :
    Nat.ModEq (D / Nat.gcd D h) r₁ r₂ := by
  have hcast : ((h * a * r₂ : ℕ) : ZMod q) = ((h * a * r₁ : ℕ) : ZMod q) := by
    have hc := congrArg (fun t : ZMod q => t * (r₁ : ZMod q) * (r₂ : ZMod q)) hphase
    have hi₁ : (r₁ : ZMod q)⁻¹ * (r₁ : ZMod q) = 1 := by
      simpa [mul_comm] using ZMod.coe_mul_inv_eq_one r₁ hr₁
    have hi₂ : (r₂ : ZMod q)⁻¹ * (r₂ : ZMod q) = 1 := by
      simpa [mul_comm] using ZMod.coe_mul_inv_eq_one r₂ hr₂
    have left : InversePhase.phase q h a r₁ * (r₁ : ZMod q) * (r₂ : ZMod q) =
        (h : ZMod q) * a * r₂ := by
      unfold InversePhase.phase
      calc
        _ = (h : ZMod q) * a * ((r₁ : ZMod q)⁻¹ * r₁) * r₂ := by ring
        _ = _ := by rw [hi₁]; ring
    have right : InversePhase.phase q h a r₂ * (r₁ : ZMod q) * (r₂ : ZMod q) =
        (h : ZMod q) * a * r₁ := by
      unfold InversePhase.phase
      calc
        _ = (h : ZMod q) * a * r₁ * ((r₂ : ZMod q)⁻¹ * r₂) := by ring
        _ = _ := by rw [hi₂]; ring
    simpa only [left, right, Nat.cast_mul] using hc
  have hmod : Nat.ModEq q (h * (a * r₂)) (h * (a * r₁)) := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_mul, mul_assoc] using hcast
  have hprojected := hmod.of_dvd hDq
  have hcancel : Nat.ModEq (D / Nat.gcd D h) (a * r₂) (a * r₁) :=
    hprojected.cancel_left_div_gcd hD
  have hcop : Nat.Coprime (D / Nat.gcd D h) a :=
    Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left D h)) ha.symm
  exact (hcancel.cancel_left_of_coprime hcop.gcd_eq_one).symm

theorem eq_of_phase_eq_projected_short_box
    {q D h a r₁ r₂ R : ℕ} (hD : 0 < D) (hDq : D ∣ q)
    (ha : a.Coprime D) (hr₁ : r₁.Coprime q) (hr₂ : r₂.Coprime q)
    (hr₁R : r₁ ≤ R) (hr₂R : r₂ ≤ R) (hR : R < D / Nat.gcd D h)
    (hphase : InversePhase.phase q h a r₁ = InversePhase.phase q h a r₂) :
    r₁ = r₂ :=
  (modEq_div_gcd_of_phase_eq_projected hD hDq ha hr₁ hr₂ hphase).eq_of_lt_of_lt
    (hr₁R.trans_lt hR) (hr₂R.trans_lt hR)

theorem equalPhasePairs_card_le_projected_short_box
    {q D h a R : ℕ} (hD : 0 < D) (hDq : D ∣ q) (ha : a.Coprime D)
    (U : Finset ℕ) (hUcop : ∀ r ∈ U, r.Coprime q)
    (hUle : ∀ r ∈ U, r ≤ R) (hR : R < D / Nat.gcd D h) :
    (AdditiveOrthogonality.equalPhasePairs U (InversePhase.phase q h a)).card ≤ U.card := by
  classical
  have hdiag : ∀ rs ∈ AdditiveOrthogonality.equalPhasePairs U (InversePhase.phase q h a),
      rs.1 = rs.2 := by
    intro rs hrs
    simp only [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
      Finset.mem_product] at hrs
    exact eq_of_phase_eq_projected_short_box hD hDq ha
      (hUcop rs.1 hrs.1.1) (hUcop rs.2 hrs.1.2)
      (hUle rs.1 hrs.1.1) (hUle rs.2 hrs.1.2) hR hrs.2
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro rs hrs
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).1
  · intro rs hrs tu htu heq
    exact Prod.ext heq ((hdiag rs hrs).symm.trans (heq.trans (hdiag tu htu)))

theorem sum_norm_characterSum_sq_le_projected_short_box
    {q D h a R : ℕ} [NeZero q] (hD : 0 < D) (hDq : D ∣ q) (ha : a.Coprime D)
    (U : Finset ℕ) (weight : ℕ → ℂ)
    (hweight : ∀ r ∈ U, ‖weight r‖ ≤ 1)
    (hUcop : ∀ r ∈ U, r.Coprime q)
    (hUle : ∀ r ∈ U, r ≤ R) (hR : R < D / Nat.gcd D h) :
    (∑ u : ZMod q, ‖AdditiveOrthogonality.characterSum U
      (InversePhase.phase q h a) weight u‖ ^ 2) ≤ (q * U.card : ℕ) := by
  exact (AdditiveOrthogonality.sum_norm_characterSum_sq_le
    U (InversePhase.phase q h a) weight hweight).trans (by
      exact_mod_cast Nat.mul_le_mul_left q
        (equalPhasePairs_card_le_projected_short_box hD hDq ha U hUcop hUle hR))

/-- The permitted short-variable set may depend on the actual modulus. -/
theorem sum_family_norm_characterSum_sq_le_projected_short_box
    {I : Type*} (S : Finset I) (modulus divisor frequency scale bound : I → ℕ)
    [∀ i, NeZero (modulus i)] (U : I → Finset ℕ) (weight : I → ℕ → ℂ)
    (hD : ∀ i ∈ S, 0 < divisor i)
    (hDq : ∀ i ∈ S, divisor i ∣ modulus i)
    (hscale : ∀ i ∈ S, (scale i).Coprime (divisor i))
    (hweight : ∀ i ∈ S, ∀ r ∈ U i, ‖weight i r‖ ≤ 1)
    (hcop : ∀ i ∈ S, ∀ r ∈ U i, r.Coprime (modulus i))
    (hle : ∀ i ∈ S, ∀ r ∈ U i, r ≤ bound i)
    (hshort : ∀ i ∈ S, bound i < divisor i / Nat.gcd (divisor i) (frequency i)) :
    (∑ i ∈ S, ∑ u : ZMod (modulus i),
      ‖AdditiveOrthogonality.characterSum (U i)
        (InversePhase.phase (modulus i) (frequency i) (scale i)) (weight i) u‖ ^ 2) ≤
      (∑ i ∈ S, (modulus i * (U i).card : ℕ) : ℝ) := by
  apply Finset.sum_le_sum
  intro i hi
  exact sum_norm_characterSum_sq_le_projected_short_box
    (hD i hi) (hDq i hi) (hscale i hi) (U i) (weight i)
    (hweight i hi) (hcop i hi) (hle i hi) (hshort i hi)

end Erdos387Proof
