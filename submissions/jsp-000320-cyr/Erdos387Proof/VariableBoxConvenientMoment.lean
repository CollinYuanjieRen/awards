/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Erdos387Proof.InversePhaseProjection
import Erdos387Proof.VariableBoxReciprocalEnergy

/-!
# Convenient moments with modulus-dependent boxes

This is the finite Hölder--Cauchy reduction used when both reciprocal
variables are filtered separately for each outer divisor.  Its first moment
uses the common ambient `S`-box only for off-diagonal numerator counting;
all modular coprimality hypotheses concern the actual box at that modulus.
The second moment projects phase equality to the rough divisor, so the phase
scale needs to be a unit only modulo that divisor.
-/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators

namespace VariableBoxConvenientMoment

/-- Exact high-moment expansion, allowing both finite boxes to depend on the
outer modulus parameter. -/
theorem sum_family_norm_reciprocalCharacter_pow_eq_bilinear
    (ell : ℕ) (Q : Finset ℕ)
    (modulus frequency scale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox Rbox : ℕ → Finset ℕ) (beta : ℕ → ℕ → ℂ) :
    (((∑ d ∈ Q, ∑ r ∈ Rbox d,
        ‖∑ s ∈ Sbox d,
          beta d s * ZMod.stdAddChar
            ((frequency d : ZMod (modulus d)) *
              (scale d : ZMod (modulus d)) *
              (r : ZMod (modulus d))⁻¹ *
              (s : ZMod (modulus d))⁻¹)‖ ^ ell : ℝ)) : ℂ) =
      ∑ d ∈ Q, ∑ u : ZMod (modulus d),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell (Sbox d))
            (ReciprocalMoment.halfPhase (modulus d))
            (fun t => ∏ j, beta d (t j)) u *
          AdditiveOrthogonality.characterSum (Rbox d)
            (InversePhase.phase (modulus d) (frequency d) (scale d))
            (Erdos387.ConvenientMoment.inversePhaseEta
              (modulus d) (frequency d) (scale d)
              ell (Sbox d) (beta d)) u := by
  classical
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Complex.ofReal_sum]
  exact Erdos387.ConvenientMoment.sum_norm_reciprocalCharacter_pow_eq_bilinear
    (modulus d) (frequency d) (scale d) ell (Sbox d) (Rbox d) (beta d)

/-- The weighted complete-frequency first moment for variable `S`-boxes.
The common ambient set controls only the off-diagonal numerator family. -/
theorem sum_halfPhase_fibre_secondMoment_le_variable_mul_base
    {ell N k T : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ) [∀ d, NeZero (modulus d)]
    (Sbox : ℕ → Finset ℕ) (U : Finset ℕ)
    (weight : ℕ → (Fin ell → ℕ) → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hbox : ∀ d ∈ Q, Sbox d ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hcop : ∀ d ∈ Q, ∀ u ∈ Sbox d, u.Coprime (modulus d))
    (hweight : ∀ d ∈ Q,
      ∀ s ∈ ReciprocalMoment.halfTuples ell (Sbox d), ‖weight d s‖ ≤ 1) :
    (∑ d ∈ Q, ∑ a : ZMod (modulus d),
        ‖AdditiveOrthogonality.residueFiberSum
          (ReciprocalMoment.halfTuples ell (Sbox d))
          (ReciprocalMoment.halfPhase (modulus d)) (weight d) a‖ ^ 2) ≤
      (((Q.card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k : ℕ) : ℝ) := by
  calc
    (∑ d ∈ Q, ∑ a : ZMod (modulus d),
        ‖AdditiveOrthogonality.residueFiberSum
          (ReciprocalMoment.halfTuples ell (Sbox d))
          (ReciprocalMoment.halfPhase (modulus d)) (weight d) a‖ ^ 2) ≤
        ∑ d ∈ Q,
          ((modularReciprocalEnergyTuples (modulus d)
            (ReciprocalMoment.leftHalf ell) (Sbox d)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact ReciprocalMoment.halfPhase_fibre_secondMoment_le_modularEnergy
        (modulus d) ell (Sbox d) (weight d) (hweight d hd)
    _ = ((∑ d ∈ Q,
          (modularReciprocalEnergyTuples (modulus d)
            (ReciprocalMoment.leftHalf ell) (Sbox d)).card : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ (((Q.card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k : ℕ) : ℝ) := by
      exact_mod_cast
        Erdos387.VariableBoxReciprocalEnergy.sum_modularReciprocalEnergy_card_le_variable_mul_base
          hk Q modulus Sbox U hN hTle hDmod hQrough hbox hUpos hUle
            hUrough hcop

/-- Cauchy--Schwarz with the variable-box reciprocal-energy bound and the
projected short-box inverse-phase bound. -/
theorem subpower_bilinear_character_cauchy
    {ell N k T : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus frequency phaseScale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox Rbox : ℕ → Finset ℕ) (U : Finset ℕ)
    (Rbound : ℕ → ℕ)
    (weightS : ℕ → (Fin ell → ℕ) → ℂ)
    (weightR : ℕ → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDpos : ∀ d ∈ Q, 0 < d)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hbox : ∀ d ∈ Q, Sbox d ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ d ∈ Q, ∀ s ∈ Sbox d, s.Coprime (modulus d))
    (hweightS : ∀ d ∈ Q,
      ∀ s ∈ ReciprocalMoment.halfTuples ell (Sbox d), ‖weightS d s‖ ≤ 1)
    (hscale : ∀ d ∈ Q, (phaseScale d).Coprime d)
    (hweightR : ∀ d ∈ Q, ∀ r ∈ Rbox d, ‖weightR d r‖ ≤ 1)
    (hRcop : ∀ d ∈ Q, ∀ r ∈ Rbox d, r.Coprime (modulus d))
    (hRle : ∀ d ∈ Q, ∀ r ∈ Rbox d, r ≤ Rbound d)
    (hshort : ∀ d ∈ Q,
      Rbound d < d / Nat.gcd d (frequency d)) :
    ‖∑ d ∈ Q, ∑ u : ZMod (modulus d),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell (Sbox d))
            (ReciprocalMoment.halfPhase (modulus d)) (weightS d) u *
          AdditiveOrthogonality.characterSum (Rbox d)
            (InversePhase.phase (modulus d) (frequency d) (phaseScale d))
            (weightR d) u‖ ^ 2 ≤
      (((Q.card * T ^ ell + U.card ^ (2 * ell)) *
          SubpowerScale.base N k) *
        (∑ d ∈ Q, modulus d * (Rbox d).card) : ℕ) := by
  let nu : (d : ℕ) → ZMod (modulus d) → ℂ := fun d =>
    AdditiveOrthogonality.residueFiberSum
      (ReciprocalMoment.halfTuples ell (Sbox d))
      (ReciprocalMoment.halfPhase (modulus d)) (weightS d)
  let rho : (d : ℕ) → ZMod (modulus d) → ℂ := fun d =>
    AdditiveOrthogonality.characterSum (Rbox d)
      (InversePhase.phase (modulus d) (frequency d) (phaseScale d))
      (weightR d)
  let A : ℝ := ((Q.card * T ^ ell + U.card ^ (2 * ell)) *
    SubpowerScale.base N k : ℕ)
  let B : ℝ := (∑ d ∈ Q, modulus d * (Rbox d).card : ℕ)
  have hnu :
      (∑ d ∈ Q, ∑ u : ZMod (modulus d), ‖nu d u‖ ^ 2) ≤ A := by
    simpa [nu, A] using
      sum_halfPhase_fibre_secondMoment_le_variable_mul_base
        hk Q modulus Sbox U weightS hN hTle hDmod hQrough hbox hUpos
          hUle hUrough hScop hweightS
  have hrho :
      (∑ d ∈ Q, ∑ u : ZMod (modulus d), ‖rho d u‖ ^ 2) ≤ B := by
    simpa [rho, B] using
      sum_family_norm_characterSum_sq_le_projected_short_box
        Q modulus (fun d => d) frequency phaseScale Rbound Rbox weightR
          hDpos hDmod hscale hweightR hRcop hRle hshort
  have h := BilinearMoment.norm_sum_mul_sq_le_of_moment_bounds
    Q modulus nu rho hnu hrho
  simpa [nu, rho, A, B, Nat.cast_mul] using h

/-- Complete variable-box convenient-moment estimate.  The diagonal scale
is `T^ell`, the reciprocal and short-variable boxes may both depend on the
outer divisor, and the phase scale is required to be a unit only modulo
that divisor. -/
theorem subpower_sum_norm_reciprocalCharacter_pow_sq_le
    {ell N k T : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus frequency scale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox Rbox : ℕ → Finset ℕ) (U : Finset ℕ)
    (Rbound : ℕ → ℕ) (beta : ℕ → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDpos : ∀ d ∈ Q, 0 < d)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hbox : ∀ d ∈ Q, Sbox d ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ d ∈ Q, ∀ s ∈ Sbox d, s.Coprime (modulus d))
    (hbeta : ∀ d ∈ Q, ∀ s ∈ Sbox d, ‖beta d s‖ ≤ 1)
    (hscale : ∀ d ∈ Q, (scale d).Coprime d)
    (hRcop : ∀ d ∈ Q, ∀ r ∈ Rbox d, r.Coprime (modulus d))
    (hRle : ∀ d ∈ Q, ∀ r ∈ Rbox d, r ≤ Rbound d)
    (hshort : ∀ d ∈ Q,
      Rbound d < d / Nat.gcd d (frequency d)) :
    (∑ d ∈ Q, ∑ r ∈ Rbox d,
        ‖∑ s ∈ Sbox d,
          beta d s * ZMod.stdAddChar
            ((frequency d : ZMod (modulus d)) *
              (scale d : ZMod (modulus d)) *
              (r : ZMod (modulus d))⁻¹ *
              (s : ZMod (modulus d))⁻¹)‖ ^ ell) ^ 2 ≤
      (((Q.card * T ^ ell + U.card ^ (2 * ell)) *
          SubpowerScale.base N k) *
        (∑ d ∈ Q, modulus d * (Rbox d).card) : ℕ) := by
  classical
  let moment : ℝ := ∑ d ∈ Q, ∑ r ∈ Rbox d,
    ‖∑ s ∈ Sbox d,
      beta d s * ZMod.stdAddChar
        ((frequency d : ZMod (modulus d)) *
          (scale d : ZMod (modulus d)) *
          (r : ZMod (modulus d))⁻¹ *
          (s : ZMod (modulus d))⁻¹)‖ ^ ell
  let bilinear : ℂ := ∑ d ∈ Q, ∑ u : ZMod (modulus d),
    AdditiveOrthogonality.residueFiberSum
        (ReciprocalMoment.halfTuples ell (Sbox d))
        (ReciprocalMoment.halfPhase (modulus d))
        (fun t => ∏ j, beta d (t j)) u *
      AdditiveOrthogonality.characterSum (Rbox d)
        (InversePhase.phase (modulus d) (frequency d) (scale d))
        (Erdos387.ConvenientMoment.inversePhaseEta
          (modulus d) (frequency d) (scale d) ell (Sbox d) (beta d)) u
  have heq : (moment : ℂ) = bilinear := by
    simpa [moment, bilinear] using
      sum_family_norm_reciprocalCharacter_pow_eq_bilinear
        ell Q modulus frequency scale Sbox Rbox beta
  have hmomentNonneg : 0 ≤ moment := by
    dsimp [moment]
    positivity
  have hnorm : moment = ‖bilinear‖ := by
    calc
      moment = ‖(moment : ℂ)‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hmomentNonneg]
      _ = ‖bilinear‖ := congrArg norm heq
  have hweightS : ∀ d ∈ Q,
      ∀ t ∈ ReciprocalMoment.halfTuples ell (Sbox d),
        ‖∏ j, beta d (t j)‖ ≤ 1 := by
    intro d hd t ht
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro j _hj
      positivity
    · intro j _hj
      exact hbeta d hd (t j) (Fintype.mem_piFinset.mp ht j)
  have hweightR : ∀ d ∈ Q, ∀ r ∈ Rbox d,
      ‖Erdos387.ConvenientMoment.inversePhaseEta
        (modulus d) (frequency d) (scale d)
        ell (Sbox d) (beta d) r‖ ≤ 1 := by
    intro d _hd r _hr
    rw [Erdos387.ConvenientMoment.norm_inversePhaseEta]
  have hbilinear := subpower_bilinear_character_cauchy
    hk Q modulus frequency scale Sbox Rbox U Rbound
      (fun d t => ∏ j, beta d (t j))
      (fun d r => Erdos387.ConvenientMoment.inversePhaseEta
        (modulus d) (frequency d) (scale d) ell (Sbox d) (beta d) r)
      hN hTle hDpos hDmod hQrough hbox hUpos hUle hUrough hScop
      hweightS hscale hweightR hRcop hRle hshort
  change moment ^ 2 ≤ _
  rw [hnorm]
  simpa [bilinear] using hbilinear

end VariableBoxConvenientMoment

end Erdos387Proof
