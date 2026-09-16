/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ConvenientMomentReduction

/-!
# Reciprocal energy for modulus-dependent coordinate boxes

The convenient-factor application uses a coordinate box which depends on
the outer divisor.  This file keeps the rational diagonal inside the actual
box and embeds every nonzero modular collision into a common ambient box.
Consequently coprimality is needed only for coordinates in the box belonging
to the modulus under consideration.
-/

namespace Erdos387

open scoped BigOperators

namespace VariableBoxReciprocalEnergy

open ReciprocalMoment

/-- The rational diagonal estimate with an arbitrary coordinate cap below
the medium scale. -/
theorem reciprocalHalfEnergy_card_le_variable_mul_base
    {ell N k T : ℕ} (hk : 0 < k)
    (hN : max 1 (2 * ell * (2 * ell + 1)) ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u) :
    (reciprocalEnergyTuples (leftHalf ell) U).card ≤
      T ^ ell * SubpowerScale.base N k := by
  have hNone : 1 ≤ N := (le_max_left _ _).trans hN
  have hpow : T ^ (2 * ell) ≤
      SubpowerScale.medium N k ^ (2 * ell) :=
    Nat.pow_le_pow_left hTle (2 * ell)
  have hTPow : T ^ (2 * ell) <
      SubpowerScale.z N k ^
        (SubpowerScale.reciprocalEnergyDepth N ell + 1) :=
    hpow.trans_lt
      (SubpowerScale.medium_pow_lt_z_pow_reciprocalEnergyDepth
        (by omega) hk)
  have hdiag := diagonalEnergy_card_le_envelope ell U
    (SubpowerScale.two_le_z (by omega) hk) hUpos hUle hUrough hTPow
  exact hdiag.trans (by
    have hmul := Nat.mul_le_mul_left (T ^ ell)
      (SubpowerScale.reciprocalEnergyOverhead_le_base
        (N := N) (k := k) (ell := ell) hN)
    simpa [mul_assoc] using hmul)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Off-diagonal modular collisions, with a different coordinate box for
each outer divisor parameter. -/
noncomputable def offDiagonalModulusTuples
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (box : ℕ → Finset ℕ) :
    Finset (Σ _D : ℕ, ι → ℕ) := by
  classical
  exact Q.sigma fun D =>
    offDiagonalModularReciprocalTuples (modulus D) A (box D)

/-- Swapping the modulus and tuple embeds the variable-box family in the
usual common-box numerator fibres. -/
theorem offDiagonalModulusTuple_mapsTo_commonTupleFibres
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (box : ℕ → Finset ℕ) (U : Finset ℕ)
    (hDmod : ∀ D ∈ Q, D ∣ modulus D)
    (hbox : ∀ D ∈ Q, box D ⊆ U)
    (hcop : ∀ D ∈ Q, ∀ u ∈ box D, u.Coprime (modulus D)) :
    ((offDiagonalModulusTuples Q modulus A box :
        Finset (Σ _D : ℕ, ι → ℕ)) :
      Set (Σ _D : ℕ, ι → ℕ)).MapsTo
      (fun x => ⟨x.2, x.1⟩)
      ((nonzeroNumeratorTuples A U).sigma
        (fun s => dividingModuli Q A s) :
          Set (Σ _s : ι → ℕ, ℕ)) := by
  classical
  rintro ⟨D, s⟩ hs
  change ⟨D, s⟩ ∈ offDiagonalModulusTuples Q modulus A box at hs
  rw [offDiagonalModulusTuples, Finset.mem_sigma] at hs
  obtain ⟨hDQ, hsOff⟩ := hs
  rw [offDiagonalModularReciprocalTuples, Finset.mem_filter] at hsOff
  have hsMod := hsOff.1
  have hcoordBox : ∀ i, s i ∈ box D := fun i =>
    modularReciprocalEnergyTuple_coordinate_mem hsMod i
  have hcoord : ∀ i, s i ∈ U := fun i => hbox D hDQ (hcoordBox i)
  have hsCop : ∀ i, (s i).Coprime (modulus D) := fun i =>
    hcop D hDQ (s i) (hcoordBox i)
  have hmodEq : Nat.ModEq (modulus D)
      (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) :=
    (modularReciprocalSum_eq_iff_numerator_modEq A
      ((Finset.univ : Finset ι) \ A) s hsCop).1
        (modularReciprocalEnergyTuple_phase hsMod)
  change (⟨s, D⟩ : Σ _s : ι → ℕ, ℕ) ∈
    (nonzeroNumeratorTuples A U).sigma
      (fun s => dividingModuli Q A s)
  rw [Finset.mem_sigma]
  constructor
  · rw [nonzeroNumeratorTuples, Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.mpr hcoord, hsOff.2⟩
  · rw [dividingModuli, Finset.mem_filter]
    exact ⟨hDQ, (hDmod D hDQ).trans (Nat.ModEq.dvd_dist hmodEq)⟩

/-- The rough-divisor fibre estimate for modulus-dependent boxes.  The
ambient numerator tuple is drawn from `U`; only the source collision uses
the smaller box belonging to its modulus. -/
theorem offDiagonalModulusTuples_card_le
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (box : ℕ → Finset ℕ) (U : Finset ℕ)
    {z L P : ℕ}
    (hz : 1 < z)
    (hDmod : ∀ D ∈ Q, D ∣ modulus D)
    (hQrough : ∀ D ∈ Q, IsZRough z D)
    (hbox : ∀ D ∈ Q, box D ⊆ U)
    (hcop : ∀ D ∈ Q, ∀ u ∈ box D, u.Coprime (modulus D))
    (hFPow : ∀ s ∈ nonzeroNumeratorTuples A U,
      Nat.dist (reciprocalNumerator A s)
          (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) <
        z ^ (L + 1))
    (hPrimeCount : ∀ s ∈ nonzeroNumeratorTuples A U,
      (Nat.dist (reciprocalNumerator A s)
          (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)).primeFactors.card
          + 1 ≤ P) :
    (offDiagonalModulusTuples Q modulus A box).card ≤
      U.card ^ Fintype.card ι * P ^ L := by
  classical
  let target : Finset (Σ _s : ι → ℕ, ℕ) :=
    (nonzeroNumeratorTuples A U).sigma fun s => dividingModuli Q A s
  have hmaps :
      ((offDiagonalModulusTuples Q modulus A box :
          Finset (Σ _D : ℕ, ι → ℕ)) :
        Set (Σ _D : ℕ, ι → ℕ)).MapsTo
        (fun x => ⟨x.2, x.1⟩) (target : Set (Σ _s : ι → ℕ, ℕ)) := by
    simpa [target] using
      offDiagonalModulusTuple_mapsTo_commonTupleFibres
        Q modulus A box U hDmod hbox hcop
  have hsourceTarget : (offDiagonalModulusTuples Q modulus A box).card ≤
      target.card :=
    Finset.card_le_card_of_injOn _ hmaps swapModulusTuple_injective.injOn
  have hfibre : ∀ s ∈ nonzeroNumeratorTuples A U,
      (dividingModuli Q A s).card ≤ P ^ L := by
    intro s hs
    let F := Nat.dist (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)
    have hF : F ≠ 0 := by
      intro hzero
      have hsne : reciprocalNumerator A s ≠
          reciprocalNumerator ((Finset.univ : Finset ι) \ A) s :=
        (Finset.mem_filter.mp hs).2
      apply hsne
      exact Nat.eq_of_dist_eq_zero hzero
    have hrough : ∀ D ∈ dividingModuli Q A s, IsZRough z D := by
      intro D hD
      exact hQrough D (Finset.mem_filter.mp hD).1
    have hdvd : ∀ D ∈ dividingModuli Q A s, D ∣ F := by
      intro D hD
      exact (Finset.mem_filter.mp hD).2
    exact (roughDivisorFamily_card_le hz hF (by simpa [F] using hFPow s hs)
      (dividingModuli Q A s) hrough hdvd).trans
        (Nat.pow_le_pow_left (by simpa [F] using hPrimeCount s hs) L)
  calc
    (offDiagonalModulusTuples Q modulus A box).card ≤ target.card :=
      hsourceTarget
    _ = ∑ s ∈ nonzeroNumeratorTuples A U,
        (dividingModuli Q A s).card := by simp [target]
    _ ≤ ∑ _s ∈ nonzeroNumeratorTuples A U, P ^ L := by
      exact Finset.sum_le_sum hfibre
    _ = (nonzeroNumeratorTuples A U).card * P ^ L := by simp
    _ ≤ U.card ^ Fintype.card ι * P ^ L := by
      apply Nat.mul_le_mul_right
      have hsub : nonzeroNumeratorTuples A U ⊆
          Fintype.piFinset (fun _ : ι => U) := by
        intro s hs
        rw [nonzeroNumeratorTuples, Finset.mem_filter] at hs
        exact hs.1
      exact (Finset.card_le_card hsub).trans_eq (by simp)

/-- Coordinate-cap version of the variable-box off-diagonal estimate. -/
theorem offDiagonalModulusTuples_card_le_of_coordinate_bound
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (box : ℕ → Finset ℕ) (U : Finset ℕ)
    {z T L D : ℕ}
    (hz : 1 < z) (hT : 1 ≤ T)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough z d)
    (hbox : ∀ d ∈ Q, box d ⊆ U)
    (hcop : ∀ d ∈ Q, ∀ u ∈ box d, u.Coprime (modulus d))
    (hUle : ∀ u ∈ U, u ≤ T)
    (hZPow : 2 * Fintype.card ι * T ^ Fintype.card ι <
      z ^ (L + 1))
    (hTwoPow : 2 * Fintype.card ι * T ^ Fintype.card ι <
      2 ^ (D + 1)) :
    (offDiagonalModulusTuples Q modulus A box).card ≤
      U.card ^ Fintype.card ι * (D + 1) ^ L := by
  apply offDiagonalModulusTuples_card_le Q modulus A box U hz hDmod
    hQrough hbox hcop
  · intro s hs
    exact (numeratorDistance_le_two_mul_card_mul_pow A s hT
      (fun i => hUle (s i)
        (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hs).1 i))).trans_lt hZPow
  · intro s hs
    let F := Nat.dist (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)
    have hF : F ≠ 0 := by
      intro hzero
      exact (Finset.mem_filter.mp hs).2 (Nat.eq_of_dist_eq_zero hzero)
    have hFtwo : F < 2 ^ (D + 1) := by
      exact (numeratorDistance_le_two_mul_card_mul_pow A s hT
        (fun i => hUle (s i)
          (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hs).1 i))).trans_lt hTwoPow
    exact Nat.add_le_add_right
      (primeFactors_card_le_of_lt_two_pow hF hFtwo) 1

/-- Subpower specialization of the variable-box off-diagonal estimate. -/
theorem offDiagonalModulusTuples_card_le_medium_mul_base
    {ell N k : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset (Fin ell ⊕ Fin ell))
    (box : ℕ → Finset ℕ) (U : Finset ℕ)
    (hN : max (4 * ell)
      (max 1 (4 * SubpowerScale.binaryMomentSlope k ell * (ell + 1))) ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hbox : ∀ d ∈ Q, box d ⊆ U)
    (hcop : ∀ d ∈ Q, ∀ u ∈ box d, u.Coprime (modulus d))
    (hUle : ∀ u ∈ U, u ≤ SubpowerScale.medium N k) :
    (offDiagonalModulusTuples Q modulus A box).card ≤
      U.card ^ (2 * ell) * SubpowerScale.base N k := by
  have hell : 4 * ell ≤ N := (le_max_left _ _).trans hN
  have hthreshold :
      max 1 (4 * SubpowerScale.binaryMomentSlope k ell * (ell + 1)) ≤ N :=
    (le_max_right _ _).trans hN
  have hNone : 1 ≤ N := (le_max_left _ _).trans hthreshold
  have hz : 1 < SubpowerScale.z N k :=
    SubpowerScale.two_le_z (by omega) hk
  have hT : 1 ≤ SubpowerScale.medium N k := by
    rw [SubpowerScale.medium_eq_pow_two]
    exact one_le_pow₀ (by norm_num)
  have hcard : Fintype.card (Fin ell ⊕ Fin ell) = 2 * ell := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hZPow :
      2 * Fintype.card (Fin ell ⊕ Fin ell) *
          SubpowerScale.medium N k ^ Fintype.card (Fin ell ⊕ Fin ell) <
        SubpowerScale.z N k ^
          (SubpowerScale.modularMomentDepth N ell + 1) := by
    simpa [hcard, show 2 * (2 * ell) = 4 * ell by ring] using
      SubpowerScale.medium_numerator_lt_z_pow_modularMomentDepth
        hNone hk hell
  have hTwoPow :
      2 * Fintype.card (Fin ell ⊕ Fin ell) *
          SubpowerScale.medium N k ^ Fintype.card (Fin ell ⊕ Fin ell) <
        2 ^ (SubpowerScale.binaryMomentDepth N k ell + 1) := by
    simpa [hcard, show 2 * (2 * ell) = 4 * ell by ring] using
      SubpowerScale.medium_numerator_lt_two_pow_binaryMomentDepth hNone hell
  have hoff := offDiagonalModulusTuples_card_le_of_coordinate_bound
    Q modulus A box U (L := SubpowerScale.modularMomentDepth N ell)
      (D := SubpowerScale.binaryMomentDepth N k ell) hz hT hDmod hQrough
      hbox hcop hUle hZPow hTwoPow
  have hoff' : (offDiagonalModulusTuples Q modulus A box).card ≤
      U.card ^ (2 * ell) *
        (SubpowerScale.binaryMomentDepth N k ell + 1) ^
          SubpowerScale.modularMomentDepth N ell := by
    simpa [hcard] using hoff
  exact hoff'.trans (Nat.mul_le_mul_left _
    (SubpowerScale.momentDivisorOverhead_le_base hthreshold))

/-- Complete reciprocal-energy count for modulus-dependent boxes.  Every
box is contained in a common ambient set used only to count off-diagonal
numerators; coprimality is imposed solely on the actual box for each
modulus. -/
theorem sum_modularReciprocalEnergy_card_le_variable_mul_base
    {ell N k T : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (box : ℕ → Finset ℕ) (U : Finset ℕ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hbox : ∀ d ∈ Q, box d ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hcop : ∀ d ∈ Q, ∀ u ∈ box d, u.Coprime (modulus d)) :
    ∑ d ∈ Q,
        (modularReciprocalEnergyTuples (modulus d)
          (leftHalf ell) (box d)).card ≤
      (Q.card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k := by
  classical
  have hfour : 4 * ell ≤ N := by
    exact (le_max_left _ _).trans hN
  have hrest :
      max (max 1 (2 * ell * (2 * ell + 1)))
          (max 1 (4 * SubpowerScale.binaryMomentSlope k ell * (ell + 1))) ≤ N := by
    exact (le_max_right _ _).trans hN
  have hdiagThreshold : max 1 (2 * ell * (2 * ell + 1)) ≤ N :=
    (le_max_left _ _).trans hrest
  have hoffThreshold :
      max 1 (4 * SubpowerScale.binaryMomentSlope k ell * (ell + 1)) ≤ N :=
    (le_max_right _ _).trans hrest
  have hdiag : ∀ d ∈ Q,
      (reciprocalEnergyTuples (leftHalf ell) (box d)).card ≤
        T ^ ell * SubpowerScale.base N k := by
    intro d hd
    apply reciprocalHalfEnergy_card_le_variable_mul_base hk hdiagThreshold
      hTle (box d)
    · intro u hu
      exact hUpos u (hbox d hd hu)
    · intro u hu
      exact hUle u (hbox d hd hu)
    · intro u hu
      exact hUrough u (hbox d hd hu)
  have hoff := offDiagonalModulusTuples_card_le_medium_mul_base hk
    Q modulus (leftHalf ell) box U (max_le hfour hoffThreshold)
      hDmod hQrough hbox hcop
      (fun u hu => (hUle u hu).trans hTle)
  calc
    ∑ d ∈ Q,
        (modularReciprocalEnergyTuples (modulus d)
          (leftHalf ell) (box d)).card ≤
        ∑ d ∈ Q,
          ((reciprocalEnergyTuples (leftHalf ell) (box d)).card +
            (offDiagonalModularReciprocalTuples (modulus d)
              (leftHalf ell) (box d)).card) := by
      apply Finset.sum_le_sum
      intro d hd
      exact modularReciprocalEnergyTuples_card_le_diagonal_add_offDiagonal
        (modulus d) (leftHalf ell) (box d)
          (fun u hu => hUpos u (hbox d hd hu))
    _ = (∑ d ∈ Q,
          (reciprocalEnergyTuples (leftHalf ell) (box d)).card) +
        (offDiagonalModulusTuples Q modulus (leftHalf ell) box).card := by
      rw [Finset.sum_add_distrib, offDiagonalModulusTuples,
        Finset.card_sigma]
    _ ≤ Q.card * (T ^ ell * SubpowerScale.base N k) +
        U.card ^ (2 * ell) * SubpowerScale.base N k := by
      exact Nat.add_le_add (by simpa using Finset.sum_le_sum hdiag) hoff
    _ = (Q.card * T ^ ell + U.card ^ (2 * ell)) *
        SubpowerScale.base N k := by ring

end VariableBoxReciprocalEnergy

end Erdos387
