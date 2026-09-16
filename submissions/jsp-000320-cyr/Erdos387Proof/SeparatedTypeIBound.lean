import Erdos387Proof.SeparatedTypeIISaving
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Type-I cancellation on the exact pre-stopping Buchstab leaves.
Each reciprocal multiplier is inverted only on the original unit locus.
The sum over distinct selected products costs a harmonic sum, not the
number of leaves. -/

namespace Erdos387Proof.SeparatedTypeIBound

open scoped BigOperators
open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase SeparatedTypeIICauchy
open SeparatedBuchstabDecomposition MaskedReciprocalPhase

noncomputable def singleCoefficient (q : ℕ) (c : ℤ) (u : ℕ) : ℤ :=
  (((c : ZMod q)*(u : ZMod q)⁻¹).val : ℤ)

theorem singleCoefficient_cast (q : ℕ) [NeZero q] (c : ℤ) (u : ℕ) :
    (singleCoefficient q c u : ZMod q) = (c : ZMod q)*(u : ZMod q)⁻¹ := by
  simp [singleCoefficient]

theorem singleCoefficient_cast_divisor (q p : ℕ) [NeZero q] (hp : p ∣ q)
    (c : ℤ) (u : ℕ) (hu : Nat.Coprime u q) :
    (singleCoefficient q c u : ZMod p) = (c : ZMod p)*(u : ZMod p)⁻¹ := by
  have hx : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hu
  have he := congrArg (ZMod.castHom hp (ZMod p)) (singleCoefficient_cast q c u)
  simpa only [map_mul, map_intCast, map_natCast,
    castHom_inv_of_unit q p hp _ hx] using he

/-- Exact rescaling preserves the original denominator mask. -/
theorem seq_mul_single (q : ℕ) [NeZero q] (c : ℤ) (u : ℕ)
    (hu : Nat.Coprime u q) (m : ℤ) :
    seq q c 0 [] ((u : ℤ)*m) = seq q (singleCoefficient q c u) 0 [] m := by
  classical
  have hu' : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hu
  unfold seq
  simp only [good, zero_add, Int.cast_mul, Int.cast_natCast, IsUnit.mul_iff, hu', true_and]
  by_cases hm : IsUnit (m : ZMod q)
  · simp only [hm, if_true, phase, zero_add, Int.cast_mul, Int.cast_natCast]
    congr 1
    rw [inv_mul_of_units q _ _ hu' hm, singleCoefficient_cast]
    ring
  · simp [hm]

/-- A nonunit multiplier annihilates every term, rather than being
silently removed from the phase domain. -/
theorem seq_mul_eq_zero_of_not_coprime (q : ℕ) [NeZero q] (c : ℤ) (u : ℕ)
    (hu : ¬Nat.Coprime u q) (m : ℤ) : seq q c 0 [] ((u : ℤ)*m) = 0 := by
  classical
  have hu' : ¬IsUnit (u : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hu
  simp [seq,good,Int.cast_mul,hu',IsUnit.mul_iff]

theorem certificate_singleCoefficient_ne_zero
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (u : ℕ) (hu : Nat.Coprime u C.modulus) :
    (singleCoefficient C.modulus (h*((b : ℤ)-C.i₀.val)) u : ZMod (C.q C.j)) ≠ 0 := by
  rw [singleCoefficient_cast_divisor C.modulus (C.q C.j) C.terminal_dvd_modulus _ u hu]
  simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast] using
    C.typeI_coefficient_ne_zero b hb h hh u hu

/-- Type-I cancellation on exactly Q/(2u)<m<=Q/u, with the initial unit
additive character retained. No free m-dependent bounded weight is inserted. -/
theorem certificate_typeI_interval_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q u : ℕ) (hQ : C.q C.i₀ ≤ Q) (hu : 0 < u)
    (huy : u ≤ BPZScale.y t S.k)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ m ∈ Finset.Ioc (Q/(2*u)) (Q/u), χ ((u : ℤ)*m)*
      seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((u : ℤ)*m)‖ ≤
      (4*(Q : ℝ)/(t : ℝ))*(u : ℝ)⁻¹ := by
  classical
  by_cases huq : Nat.Coprime u C.modulus
  · by_cases huQ : u ≤ Q
    · have ht1 : 1 ≤ t := by
        have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
        omega
      have hy : 1 ≤ BPZScale.y t S.k := ht1.trans (SeparatedTypeIISaving.base_le_y t S.k ht1)
      have huy2 : u ≤ (BPZScale.y t S.k)^2 := by nlinarith
      simp_rw [seq_mul_single C.modulus _ u huq]
      change ‖∑ m ∈ Finset.Ioc (Q/(2*u)) (Q/u),
        (χ.mulShift (u : ℤ)) (m : ℤ)*seq C.modulus
          (singleCoefficient C.modulus (h*((b : ℤ)-C.i₀.val)) u) 0 [] (m : ℤ)‖ ≤ _
      rw [sum_Ioc_eq_intervalSum (Q/(2*u)) (Q/u)
        (fun m : ℤ => (χ.mulShift (u : ℤ)) m*seq C.modulus
          (singleCoefficient C.modulus (h*((b : ℤ)-C.i₀.val)) u) 0 [] m)]
      have he := C.norm_dyadic_phase_le ht hg hM Q u hQ hu huQ huy2
        (χ.mulShift (u : ℤ)) (fun m => hχ _) _ 0 (((Q/(2*u) : ℕ) : ℤ)+1)
        (certificate_singleCoefficient_ne_zero C b hb h hh u huq)
      apply he.trans
      have hUL : u*(Q/u-Q/(2*u)) ≤ Q :=
        (Nat.mul_le_mul_left u (Nat.sub_le _ _)).trans (by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self Q u)
      have hUL' : (u : ℝ)*((Q/u-Q/(2*u) : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hUL
      have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0<t)
      have huR : (0 : ℝ) < u := by exact_mod_cast hu
      apply (le_mul_inv_iff₀ huR).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right htR).mpr
      nlinarith
    · have hdiv : Q/u = 0 := Nat.div_eq_of_lt (by omega)
      have hempty : Finset.Ioc (Q/(2*u)) (Q/u) = ∅ :=
        Finset.Ioc_eq_empty_of_le (by rw [hdiv]; exact Nat.zero_le _)
      simp only [hempty, Finset.sum_empty, norm_zero]
      positivity
  · have hz (m : ℕ) : seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((u : ℤ)*m) = 0 :=
      seq_mul_eq_zero_of_not_coprime _ _ _ huq _
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero]
    positivity

/-- The exact pre-stopping leaves, before imposing the redundant unit filter. -/
noncomputable def typeILeaves (y : ℕ) : Finset Leaf := by
  classical
  exact ((leaves y 1 (primeList y)).toFinset).filter (fun l => l.stopped = false)

theorem mem_typeILeaves (y : ℕ) (l : Leaf) :
    l ∈ typeILeaves y ↔ l ∈ leaves y 1 (primeList y) ∧ l.stopped = false := by
  classical
  simp [typeILeaves]

theorem typeILeaves_data (y : ℕ) (hy : 1 ≤ y) (l : Leaf) (hl : l ∈ typeILeaves y) :
    0 < l.chosen.prod ∧ l.chosen.prod ≤ y := by
  obtain ⟨hl,hs⟩ := (mem_typeILeaves y l).mp hl
  exact ⟨(chosen_prime_data y 1 y l hl).2.2,((e5_leaf_domain y hy l hl).1 hs).2⟩

/-- Distinct selected products make the absolute reciprocal coefficient
sum no larger than the harmonic sum. No factor equal to the leaf count
is introduced. -/
theorem sum_typeILeaves_inv_le (y : ℕ) (hy : 1 ≤ y) :
    (∑ l ∈ typeILeaves y, (l.chosen.prod : ℝ)⁻¹) ≤ 1+Real.log y := by
  classical
  let U := (typeILeaves y).image (fun l => l.chosen.prod)
  have he : (∑ u ∈ U, (u : ℝ)⁻¹) = ∑ l ∈ typeILeaves y, (l.chosen.prod : ℝ)⁻¹ := by
    apply Finset.sum_image
    intro a ha b hb hab
    exact chosen_prod_injective y 1 y a b ((mem_typeILeaves y a).mp ha).1
      ((mem_typeILeaves y b).mp hb).1 hab
  have hsub : U ⊆ Finset.Icc 1 y := by
    intro u hu
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
    have hd := typeILeaves_data y hy l hl
    exact Finset.mem_Icc.mpr ⟨by omega,hd.2⟩
  rw [← he]
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 y, (u : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro u hu hU; positivity)
    _ = (harmonic y : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ 1+Real.log y := harmonic_le_one_add_log y

/-- The exact signed Type-I leaf sum, with the original conductor mask
already encoded by seq on every product u*m. -/
noncomputable def typeISum (M Q y : ℕ) [NeZero M] (c : ℤ) (χ : AddChar ℤ ℂ) : ℂ :=
  ∑ l ∈ typeILeaves y, (-1 : ℂ)^l.chosen.length *
    ∑ m ∈ Finset.Ioc (Q/(2*l.chosen.prod)) (Q/l.chosen.prod),
      χ ((l.chosen.prod : ℤ)*m)*seq M c 0 [] ((l.chosen.prod : ℤ)*m)

/-- The defined sum is exactly the Type-I part of the original Buchstab
identity on Q/2<n<=Q. Signs, endpoints and masks are all unchanged. -/
theorem typeISum_eq_original (M Q y : ℕ) [NeZero M] (hy : 1 ≤ y)
    (c : ℤ) (χ : AddChar ℤ ℂ) :
    typeISum M Q y c χ = ∑ l ∈ typeILeaves y, ∑ n ∈ Finset.Ioc (Q/2) Q,
      l.value n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ)) := by
  classical
  unfold typeISum
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨hl,hs⟩ := (mem_typeILeaves y l).mp hl
  have he := typeI_interval_sum (Q/2) Q y 1 y l hy hl hs (fun _ => True)
    (fun n => χ (n : ℤ)*seq M c 0 [] (n : ℤ))
  simpa only [if_true, Finset.filter_true, Nat.div_div_eq_div_mul, Nat.cast_mul] using he.symm

/-- Full finite Buchstab splitting on the ORIGINAL interval. The stopped
part is kept exactly as a signed complex sum; no cancellation is postulated. -/
theorem rough_phase_eq_typeI_add_stopped (M Q y : ℕ) [NeZero M] (hy : 1 ≤ y)
    (c : ℤ) (χ : AddChar ℤ ℂ) :
    (∑ n ∈ Finset.Ioc (Q/2) Q,
      roughIndicator y n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ))) =
      typeISum M Q y c χ + ∑ l ∈ SeparatedProductWindow.stoppedLeaves y,
        ∑ n ∈ Finset.Ioc (Q/2) Q, l.value n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ)) := by
  classical
  let F : Leaf → ℂ := fun l => ∑ n ∈ Finset.Ioc (Q/2) Q,
    l.value n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ))
  have hnd : (leaves y 1 (primeList y)).Nodup :=
    List.Nodup.of_map Leaf.chosen (chosen_nodup y 1 (primeList y) (primeList_nodup y))
  have he := weighted_rough_identity (Finset.Ioc (Q/2) Q) y y (fun _ => True)
    (fun n => χ (n : ℤ)*seq M c 0 [] (n : ℤ))
  simp only [if_true] at he
  rw [← List.sum_toFinset F hnd] at he
  have hfilter : ((leaves y 1 (primeList y)).toFinset.filter
      (fun l => ¬l.stopped = false)) = SeparatedProductWindow.stoppedLeaves y := by
    ext l
    simp only [Finset.mem_filter,List.mem_toFinset,
      SeparatedProductWindow.mem_stoppedLeaves]
    cases l.stopped <;> simp
  have hp := Finset.sum_filter_add_sum_filter_not (leaves y 1 (primeList y)).toFinset
    (fun l => l.stopped = false) F
  rw [hfilter] at hp
  rw [typeISum_eq_original M Q y hy c χ]
  exact he.trans hp.symm

/-- Actual-certificate Type-I estimate with its logarithmic cost explicit. -/
theorem norm_typeISum_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q : ℕ) (hQ : C.q C.i₀ ≤ Q)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖typeISum C.modulus Q (BPZScale.y t S.k) (h*((b : ℤ)-C.i₀.val)) χ‖ ≤
      (4*(Q : ℝ)/(t : ℝ))*(1+Real.log (BPZScale.y t S.k)) := by
  classical
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
    omega
  have hy : 1 ≤ BPZScale.y t S.k := ht1.trans (SeparatedTypeIISaving.base_le_y t S.k ht1)
  unfold typeISum
  calc
    _ ≤ ∑ l ∈ typeILeaves (BPZScale.y t S.k), ‖(-1 : ℂ)^l.chosen.length *
        ∑ m ∈ Finset.Ioc (Q/(2*l.chosen.prod)) (Q/l.chosen.prod),
          χ ((l.chosen.prod : ℤ)*m)*seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 []
            ((l.chosen.prod : ℤ)*m)‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ typeILeaves (BPZScale.y t S.k),
        (4*(Q : ℝ)/(t : ℝ))*(l.chosen.prod : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      have hd := typeILeaves_data (BPZScale.y t S.k) hy l hl
      simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      exact certificate_typeI_interval_le C ht hg hM Q l.chosen.prod hQ hd.1 hd.2 b hb h hh χ hχ
    _ = (4*(Q : ℝ)/(t : ℝ))*
        ∑ l ∈ typeILeaves (BPZScale.y t S.k), (l.chosen.prod : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_typeILeaves_inv_le _ hy) (by positivity)

end Erdos387Proof.SeparatedTypeIBound
