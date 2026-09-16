/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Erdos387Proof.VariableBoxConvenientMoment

/-!
# Convenient moments indexed by divisor certificates

Distinct outer certificates may have the same product divisor while carrying
different CRT residues and phase data.  This file retains the full certificate
index in the exact expansion and in `T₂`.  Only the nonnegative `T₁` cardinal
sum is grouped by product divisor, where a supplied fixed-product fibre bound
accounts for the multiplicity.
-/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators

namespace IndexedConvenientMoment

/-- Modular reciprocal-energy tuples are monotone in their coordinate box. -/
theorem modularReciprocalEnergyTuples_mono
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) {V W : Finset ℕ} (hVW : V ⊆ W) :
    modularReciprocalEnergyTuples q A V ⊆
      modularReciprocalEnergyTuples q A W := by
  classical
  intro s hs
  rw [modularReciprocalEnergyTuples, Finset.mem_filter] at hs ⊢
  exact ⟨Fintype.mem_piFinset.mpr
    (fun i => hVW (Fintype.mem_piFinset.mp hs.1 i)), hs.2⟩

/-- Grouping a nonnegative indexed sum by a finite-valued map costs at most
the maximum cardinality of a fibre. -/
theorem sum_comp_le_maxFiber_mul_sum_image
    {J : Type*} [DecidableEq J]
    (I : Finset J) (D : J → ℕ) (f : ℕ → ℕ) (m : ℕ)
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m) :
    ∑ j ∈ I, f (D j) ≤ m * ∑ d ∈ I.image D, f d := by
  classical
  have hmaps : ((I : Finset J) : Set J).MapsTo D
      ((I.image D : Finset ℕ) : Set ℕ) := by
    intro j hj
    exact Finset.mem_image_of_mem D hj
  calc
    ∑ j ∈ I, f (D j) =
        ∑ d ∈ I.image D, ∑ j ∈ I with D j = d, f (D j) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ d ∈ I.image D,
        (I.filter fun j => D j = d).card * f d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        ∑ j ∈ I with D j = d, f (D j) =
            ∑ _j ∈ I.filter (fun j => D j = d), f d := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
        _ = (I.filter fun j => D j = d).card * f d := by simp
    _ ≤ ∑ _d ∈ I.image D, m * f _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.mul_le_mul_right (f d) (hfibre d hd)
    _ = m * ∑ d ∈ I.image D, f d := by
      rw [Finset.mul_sum]

/-- The indexed modular-energy cardinal sum.  Each actual box is enlarged to
the common ambient box filtered by coprimality for its product divisor; after
grouping by that divisor, the fixed-fibre multiplicity is charged once. -/
theorem sum_modularReciprocalEnergy_card_le_indexed_mul_base
    {J : Type*} [DecidableEq J]
    {ell N k T m : ℕ} (hk : 0 < k)
    (I : Finset J) (D : J → ℕ) (modulus : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox : J → Finset ℕ) (U : Finset ℕ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDmod : ∀ j ∈ I, D j ∣ modulus (D j))
    (hDrough : ∀ j ∈ I, IsZRough (SubpowerScale.z N k) (D j))
    (hbox : ∀ j ∈ I, Sbox j ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ j ∈ I, ∀ s ∈ Sbox j, s.Coprime (modulus (D j)))
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m) :
    ∑ j ∈ I,
        (modularReciprocalEnergyTuples (modulus (D j))
          (ReciprocalMoment.leftHalf ell) (Sbox j)).card ≤
      m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k := by
  classical
  let Q := I.image D
  let ambient : ℕ → Finset ℕ := fun d =>
    U.filter fun u => u.Coprime (modulus d)
  let energy : ℕ → ℕ := fun d =>
    (modularReciprocalEnergyTuples (modulus d)
      (ReciprocalMoment.leftHalf ell) (ambient d)).card
  have hboxAmbient : ∀ j ∈ I, Sbox j ⊆ ambient (D j) := by
    intro j hj s hs
    exact Finset.mem_filter.mpr ⟨hbox j hj hs, hScop j hj s hs⟩
  have hmono : ∀ j ∈ I,
      (modularReciprocalEnergyTuples (modulus (D j))
        (ReciprocalMoment.leftHalf ell) (Sbox j)).card ≤ energy (D j) := by
    intro j hj
    exact Finset.card_le_card
      (modularReciprocalEnergyTuples_mono
        (ReciprocalMoment.leftHalf ell) (hboxAmbient j hj))
  have hgroup : ∑ j ∈ I, energy (D j) ≤
      m * ∑ d ∈ Q, energy d := by
    exact sum_comp_le_maxFiber_mul_sum_image I D energy m hfibre
  have hDmodQ : ∀ d ∈ Q, d ∣ modulus d := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact hDmod j hj
  have hDroughQ : ∀ d ∈ Q,
      IsZRough (SubpowerScale.z N k) d := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact hDrough j hj
  have hambientSub : ∀ d ∈ Q, ambient d ⊆ U := by
    intro d hd u hu
    exact (Finset.mem_filter.mp hu).1
  have hambientCop : ∀ d ∈ Q, ∀ u ∈ ambient d,
      u.Coprime (modulus d) := by
    intro d hd u hu
    exact (Finset.mem_filter.mp hu).2
  have henergy :=
    Erdos387.VariableBoxReciprocalEnergy.sum_modularReciprocalEnergy_card_le_variable_mul_base
      hk Q modulus ambient U hN hTle hDmodQ hDroughQ hambientSub
        hUpos hUle hUrough hambientCop
  calc
    ∑ j ∈ I,
        (modularReciprocalEnergyTuples (modulus (D j))
          (ReciprocalMoment.leftHalf ell) (Sbox j)).card ≤
        ∑ j ∈ I, energy (D j) := Finset.sum_le_sum hmono
    _ ≤ m * ∑ d ∈ Q, energy d := hgroup
    _ ≤ m * (((Q.card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k)) := Nat.mul_le_mul_left m henergy
    _ = m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k := by simp [Q]; ring

/-- Weighted `T₁` estimate for the full indexed family. -/
theorem sum_halfPhase_fibre_secondMoment_le_indexed_mul_base
    {J : Type*} [DecidableEq J]
    {ell N k T m : ℕ} (hk : 0 < k)
    (I : Finset J) (D : J → ℕ) (modulus : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox : J → Finset ℕ) (U : Finset ℕ)
    (weight : J → (Fin ell → ℕ) → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDmod : ∀ j ∈ I, D j ∣ modulus (D j))
    (hDrough : ∀ j ∈ I, IsZRough (SubpowerScale.z N k) (D j))
    (hbox : ∀ j ∈ I, Sbox j ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ j ∈ I, ∀ s ∈ Sbox j, s.Coprime (modulus (D j)))
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m)
    (hweight : ∀ j ∈ I,
      ∀ s ∈ ReciprocalMoment.halfTuples ell (Sbox j), ‖weight j s‖ ≤ 1) :
    (∑ j ∈ I, ∑ a : ZMod (modulus (D j)),
        ‖AdditiveOrthogonality.residueFiberSum
          (ReciprocalMoment.halfTuples ell (Sbox j))
          (ReciprocalMoment.halfPhase (modulus (D j))) (weight j) a‖ ^ 2) ≤
      ((m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k : ℕ) : ℝ) := by
  calc
    (∑ j ∈ I, ∑ a : ZMod (modulus (D j)),
        ‖AdditiveOrthogonality.residueFiberSum
          (ReciprocalMoment.halfTuples ell (Sbox j))
          (ReciprocalMoment.halfPhase (modulus (D j))) (weight j) a‖ ^ 2) ≤
        ∑ j ∈ I,
          ((modularReciprocalEnergyTuples (modulus (D j))
            (ReciprocalMoment.leftHalf ell) (Sbox j)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ReciprocalMoment.halfPhase_fibre_secondMoment_le_modularEnergy
        (modulus (D j)) ell (Sbox j) (weight j) (hweight j hj)
    _ = ((∑ j ∈ I,
          (modularReciprocalEnergyTuples (modulus (D j))
            (ReciprocalMoment.leftHalf ell) (Sbox j)).card : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ ((m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k : ℕ) : ℝ) := by
      exact_mod_cast sum_modularReciprocalEnergy_card_le_indexed_mul_base
        hk I D modulus Sbox U hN hTle hDmod hDrough hbox hUpos hUle
          hUrough hScop hfibre

/-- Exact indexed high-moment expansion. -/
theorem sum_norm_reciprocalCharacter_pow_eq_bilinear
    {J : Type*} [DecidableEq J]
    (ell : ℕ) (I : Finset J) (D : J → ℕ)
    (modulus : ℕ → ℕ) [∀ d, NeZero (modulus d)]
    (frequency scale : J → ℕ)
    (Sbox Rbox : J → Finset ℕ) (beta : J → ℕ → ℂ) :
    (((∑ j ∈ I, ∑ r ∈ Rbox j,
        ‖∑ s ∈ Sbox j,
          beta j s * ZMod.stdAddChar
            ((frequency j : ZMod (modulus (D j))) *
              (scale j : ZMod (modulus (D j))) *
              (r : ZMod (modulus (D j)))⁻¹ *
              (s : ZMod (modulus (D j)))⁻¹)‖ ^ ell : ℝ)) : ℂ) =
      ∑ j ∈ I, ∑ u : ZMod (modulus (D j)),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell (Sbox j))
            (ReciprocalMoment.halfPhase (modulus (D j)))
            (fun t => ∏ a, beta j (t a)) u *
          AdditiveOrthogonality.characterSum (Rbox j)
            (InversePhase.phase (modulus (D j)) (frequency j) (scale j))
            (Erdos387.ConvenientMoment.inversePhaseEta
              (modulus (D j)) (frequency j) (scale j)
              ell (Sbox j) (beta j)) u := by
  classical
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Complex.ofReal_sum]
  exact Erdos387.ConvenientMoment.sum_norm_reciprocalCharacter_pow_eq_bilinear
    (modulus (D j)) (frequency j) (scale j) ell
      (Sbox j) (Rbox j) (beta j)

/-- Indexed Cauchy estimate.  The first factor pays the proven divisor-fibre
multiplicity; the second retains every indexed short box and phase. -/
theorem subpower_bilinear_character_cauchy
    {J : Type*} [DecidableEq J]
    {ell N k T m : ℕ} (hk : 0 < k)
    (I : Finset J) (D : J → ℕ)
    (modulus : ℕ → ℕ) [∀ d, NeZero (modulus d)]
    (frequency phaseScale : J → ℕ)
    (Sbox Rbox : J → Finset ℕ) (U : Finset ℕ)
    (Rbound : J → ℕ)
    (weightS : J → (Fin ell → ℕ) → ℂ)
    (weightR : J → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDpos : ∀ j ∈ I, 0 < D j)
    (hDmod : ∀ j ∈ I, D j ∣ modulus (D j))
    (hDrough : ∀ j ∈ I, IsZRough (SubpowerScale.z N k) (D j))
    (hbox : ∀ j ∈ I, Sbox j ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ j ∈ I, ∀ s ∈ Sbox j, s.Coprime (modulus (D j)))
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m)
    (hweightS : ∀ j ∈ I,
      ∀ s ∈ ReciprocalMoment.halfTuples ell (Sbox j), ‖weightS j s‖ ≤ 1)
    (hscale : ∀ j ∈ I, (phaseScale j).Coprime (D j))
    (hweightR : ∀ j ∈ I, ∀ r ∈ Rbox j, ‖weightR j r‖ ≤ 1)
    (hRcop : ∀ j ∈ I, ∀ r ∈ Rbox j, r.Coprime (modulus (D j)))
    (hRle : ∀ j ∈ I, ∀ r ∈ Rbox j, r ≤ Rbound j)
    (hshort : ∀ j ∈ I,
      Rbound j < D j / Nat.gcd (D j) (frequency j)) :
    ‖∑ j ∈ I, ∑ u : ZMod (modulus (D j)),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell (Sbox j))
            (ReciprocalMoment.halfPhase (modulus (D j))) (weightS j) u *
          AdditiveOrthogonality.characterSum (Rbox j)
            (InversePhase.phase (modulus (D j)) (frequency j) (phaseScale j))
            (weightR j) u‖ ^ 2 ≤
      ((m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
          SubpowerScale.base N k) *
        (∑ j ∈ I, modulus (D j) * (Rbox j).card) : ℕ) := by
  let nu : (j : J) → ZMod (modulus (D j)) → ℂ := fun j =>
    AdditiveOrthogonality.residueFiberSum
      (ReciprocalMoment.halfTuples ell (Sbox j))
      (ReciprocalMoment.halfPhase (modulus (D j))) (weightS j)
  let rho : (j : J) → ZMod (modulus (D j)) → ℂ := fun j =>
    AdditiveOrthogonality.characterSum (Rbox j)
      (InversePhase.phase (modulus (D j)) (frequency j) (phaseScale j))
      (weightR j)
  let A : ℝ := (m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
    SubpowerScale.base N k : ℕ)
  let B : ℝ := (∑ j ∈ I, modulus (D j) * (Rbox j).card : ℕ)
  have hnu :
      (∑ j ∈ I, ∑ u : ZMod (modulus (D j)), ‖nu j u‖ ^ 2) ≤ A := by
    simpa [nu, A] using sum_halfPhase_fibre_secondMoment_le_indexed_mul_base
      hk I D modulus Sbox U weightS hN hTle hDmod hDrough hbox hUpos
        hUle hUrough hScop hfibre hweightS
  have hrho :
      (∑ j ∈ I, ∑ u : ZMod (modulus (D j)), ‖rho j u‖ ^ 2) ≤ B := by
    simpa [rho, B] using
      sum_family_norm_characterSum_sq_le_projected_short_box
        I (fun j => modulus (D j)) D frequency phaseScale Rbound Rbox weightR
          hDpos hDmod hscale hweightR hRcop hRle hshort
  have h := BilinearMoment.norm_sum_mul_sq_le_of_moment_bounds
    I (fun j => modulus (D j)) nu rho hnu hrho
  simpa [nu, rho, A, B, Nat.cast_mul] using h

/-- Full indexed convenient-moment estimate. -/
theorem subpower_sum_norm_reciprocalCharacter_pow_sq_le
    {J : Type*} [DecidableEq J]
    {ell N k T m : ℕ} (hk : 0 < k)
    (I : Finset J) (D : J → ℕ)
    (modulus : ℕ → ℕ) [∀ d, NeZero (modulus d)]
    (frequency scale : J → ℕ)
    (Sbox Rbox : J → Finset ℕ) (U : Finset ℕ)
    (Rbound : J → ℕ) (beta : J → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDpos : ∀ j ∈ I, 0 < D j)
    (hDmod : ∀ j ∈ I, D j ∣ modulus (D j))
    (hDrough : ∀ j ∈ I, IsZRough (SubpowerScale.z N k) (D j))
    (hbox : ∀ j ∈ I, Sbox j ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ j ∈ I, ∀ s ∈ Sbox j, s.Coprime (modulus (D j)))
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m)
    (hbeta : ∀ j ∈ I, ∀ s ∈ Sbox j, ‖beta j s‖ ≤ 1)
    (hscale : ∀ j ∈ I, (scale j).Coprime (D j))
    (hRcop : ∀ j ∈ I, ∀ r ∈ Rbox j, r.Coprime (modulus (D j)))
    (hRle : ∀ j ∈ I, ∀ r ∈ Rbox j, r ≤ Rbound j)
    (hshort : ∀ j ∈ I,
      Rbound j < D j / Nat.gcd (D j) (frequency j)) :
    (∑ j ∈ I, ∑ r ∈ Rbox j,
        ‖∑ s ∈ Sbox j,
          beta j s * ZMod.stdAddChar
            ((frequency j : ZMod (modulus (D j))) *
              (scale j : ZMod (modulus (D j))) *
              (r : ZMod (modulus (D j)))⁻¹ *
              (s : ZMod (modulus (D j)))⁻¹)‖ ^ ell) ^ 2 ≤
      ((m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
          SubpowerScale.base N k) *
        (∑ j ∈ I, modulus (D j) * (Rbox j).card) : ℕ) := by
  classical
  let moment : ℝ := ∑ j ∈ I, ∑ r ∈ Rbox j,
    ‖∑ s ∈ Sbox j,
      beta j s * ZMod.stdAddChar
        ((frequency j : ZMod (modulus (D j))) *
          (scale j : ZMod (modulus (D j))) *
          (r : ZMod (modulus (D j)))⁻¹ *
          (s : ZMod (modulus (D j)))⁻¹)‖ ^ ell
  let bilinear : ℂ := ∑ j ∈ I, ∑ u : ZMod (modulus (D j)),
    AdditiveOrthogonality.residueFiberSum
        (ReciprocalMoment.halfTuples ell (Sbox j))
        (ReciprocalMoment.halfPhase (modulus (D j)))
        (fun t => ∏ a, beta j (t a)) u *
      AdditiveOrthogonality.characterSum (Rbox j)
        (InversePhase.phase (modulus (D j)) (frequency j) (scale j))
        (Erdos387.ConvenientMoment.inversePhaseEta
          (modulus (D j)) (frequency j) (scale j)
          ell (Sbox j) (beta j)) u
  have heq : (moment : ℂ) = bilinear := by
    simpa [moment, bilinear] using
      sum_norm_reciprocalCharacter_pow_eq_bilinear
        ell I D modulus frequency scale Sbox Rbox beta
  have hmomentNonneg : 0 ≤ moment := by
    dsimp [moment]
    positivity
  have hnorm : moment = ‖bilinear‖ := by
    calc
      moment = ‖(moment : ℂ)‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hmomentNonneg]
      _ = ‖bilinear‖ := congrArg norm heq
  have hweightS : ∀ j ∈ I,
      ∀ t ∈ ReciprocalMoment.halfTuples ell (Sbox j),
        ‖∏ a, beta j (t a)‖ ≤ 1 := by
    intro j hj t ht
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro a _ha
      positivity
    · intro a _ha
      exact hbeta j hj (t a) (Fintype.mem_piFinset.mp ht a)
  have hweightR : ∀ j ∈ I, ∀ r ∈ Rbox j,
      ‖Erdos387.ConvenientMoment.inversePhaseEta
        (modulus (D j)) (frequency j) (scale j)
        ell (Sbox j) (beta j) r‖ ≤ 1 := by
    intro j _hj r _hr
    rw [Erdos387.ConvenientMoment.norm_inversePhaseEta]
  have hbilinear := subpower_bilinear_character_cauchy
    hk I D modulus frequency scale Sbox Rbox U Rbound
      (fun j t => ∏ a, beta j (t a))
      (fun j r => Erdos387.ConvenientMoment.inversePhaseEta
        (modulus (D j)) (frequency j) (scale j)
        ell (Sbox j) (beta j) r)
      hN hTle hDpos hDmod hDrough hbox hUpos hUle hUrough hScop
      hfibre hweightS hscale hweightR hRcop hRle hshort
  change moment ^ 2 ≤ _
  rw [hnorm]
  simpa [bilinear] using hbilinear

end IndexedConvenientMoment

end Erdos387Proof
