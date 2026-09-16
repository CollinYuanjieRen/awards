import Erdos387Proof.ConvenientNormalizedMoment
import Erdos387Proof.FiniteLogSeparator
import Erdos387Proof.FourierMixedVariation

/-! The actual convenient-error weighted dyadic moment.
The two sharp product restrictions are separated exactly before applying a
moment estimate to independent rough/unit prefixes. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientWeightedMoment
open Erdos387 Erdos387.CoverBPZ
open ConvenientMomentBoxes ConvenientMomentBound ConvenientSplitFibre
open ConvenientNormalizedMoment FourierVariation FiniteAbel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The active complementary index has a genuine near-product witness. -/
theorem active_near_product_lower {B K X z y medium e r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : Index S X z y medium i}
    (hc : c ∈ activeIndices S X z y medium i e r s) :
    X < 8*B*product c*2^r*2^s := by
  classical
  obtain ⟨_,p,hp,hr,hs⟩ := (Finset.mem_filter.mp hc).2
  have hd := (mem_splitPairDomain_iff c).mp hp
  have hnear := hd.2.2.2.2.2.2.2.1
  rw [← product_eq_otherValue] at hnear
  have hn := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).mp hnear
  have hpr := (Finset.mem_Ico.mp hr).2.le
  have hps := (Finset.mem_Ico.mp hs).2.le
  rw [pow_succ] at hpr hps
  calc
    _ < B*product c*p.1*p.2*2 := by simpa only [mul_assoc] using hn
    _ ≤ B*product c*(2^r*2)*(2^s*2)*2 := by gcongr
    _ = _ := by ring

/-- No reciprocal-modulus denominator is replaced by an unproved typical
size: the uniform ratio follows from the original active witness. -/
theorem active_weight_ratio_le {B K X z y medium e r s g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} [NeZero g]
    {c : Index S X z y medium i}
    (hc : c ∈ activeIndices S X z y medium i e r s) :
    (X : ℝ)/((modulus S g (product c) : ℝ)*2^r*2^s) ≤ 8*B := by
  have hD := (product_data c).1
  have hQ : modulus S g (product c)=refinementModulus S*product c*g :=
    ConvenientMomentApplicability.momentModulus_eq hD
  have hDQ : product c ≤ modulus S g (product c) := by
    rw [hQ]
    exact (Nat.le_mul_of_pos_left _ (refinementModulus_pos S)).trans
      (Nat.le_mul_of_pos_right _ (NeZero.pos g))
  have hQr : (0 : ℝ) < modulus S g (product c) := by exact_mod_cast hD.trans_le hDQ
  apply (div_le_iff₀ (by positivity)).mpr
  have hlo : (X : ℝ) ≤ 8*B*(product c : ℝ)*2^r*2^s := by
    exact_mod_cast (active_near_product_lower hc).le
  calc
    _ ≤ 8*B*(product c : ℝ)*2^r*2^s := hlo
    _ ≤ 8*B*(modulus S g (product c) : ℝ)*2^r*2^s := by
      have hdq : (product c : ℝ) ≤ modulus S g (product c) := by exact_mod_cast hDQ
      gcongr
    _ = _ := by ring

/-- The actual tent weight on the whole dyadic rectangle has a polynomial
H,B mixed-variation bound, uniform in its complementary vector. -/
theorem active_tent_mixedVariation_le {B K X z y medium e r s g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} [NeZero g]
    {c : Index S X z y medium i}
    (hc : c ∈ activeIndices S X z y medium i e r s)
    (hX : 0 < X) (hindex : i.val ≤ X) (h : ℤ) (H : ℕ) (hh : h.natAbs ≤ H) :
    mixedVariationMass
      (fun u v => tentWeight X h (-(i.val : ℤ))
        ((modulus S g (product c) : ℝ)*(2^r+u)*(2^s+v))⁻¹)
      (2^r) (2^s) ≤
      128*(B : ℝ)+40960*H*B^2+2097152*(H : ℝ)^2*B^3 := by
  let Q := modulus S g (product c)
  have hQ : 0 < Q := NeZero.pos Q
  have hi : |-(i.val : ℤ)| ≤ (X : ℤ) := by
    simpa only [abs_neg,abs_of_nonneg (Int.natCast_nonneg _)] using
      (show (i.val : ℤ) ≤ X by exact_mod_cast hindex)
  have hhZ : |h| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hh
  have hhR : |(h : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hhZ
  have hv := FourierMixedVariation.mixedVariationMass_tentWeight_reciprocal_le X h (-(i.val : ℤ))
    (fun u => Q*(2^r+u)) (fun v => 2^s+v) (2^r) (2^s)
    hX (R := 8*B) (H := H) (by positivity) (by positivity) hhR hi
    (fun u => Nat.mul_pos hQ (by positivity)) (fun v => by positivity)
    (fun _ _ hab => Nat.mul_le_mul_left Q (Nat.add_le_add_left hab _))
    (fun _ _ hab => Nat.add_le_add_left hab _)
    (by simpa only [Q,Nat.add_zero,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using
      active_weight_ratio_le (g := g) hc)
  push_cast at hv
  dsimp [Q] at hv
  convert hv using 1
  ring

noncomputable def sharpMask (B X medium D r s : ℕ) : ℂ :=
  if r*s ≤ medium ∧ X/2 < B*(D*r*s) ∧ D*r*s ≤ X then 1 else 0

noncomputable def separatorTwist (X medium : ℕ)
    (a : ZMod (FiniteLogSeparator.modulus X))
    (b : ZMod (FiniteLogSeparator.modulus medium)) (n : ℕ) : ℂ :=
  FiniteLogSeparator.character X a n*FiniteLogSeparator.character medium b n

noncomputable def separatorCoefficient (B X medium D : ℕ)
    (a : ZMod (FiniteLogSeparator.modulus X))
    (b : ZMod (FiniteLogSeparator.modulus medium)) : ℂ :=
  FiniteLogSeparator.coefficient X ((X/2)/B) a*
    FiniteLogSeparator.coefficient medium 0 b*
    FiniteLogSeparator.character X a D*FiniteLogSeparator.character medium b 1

theorem norm_separatorTwist (X medium n : ℕ)
    (a : ZMod (FiniteLogSeparator.modulus X))
    (b : ZMod (FiniteLogSeparator.modulus medium)) :
    ‖separatorTwist X medium a b n‖=1 := by
  simp only [separatorTwist,norm_mul,FiniteLogSeparator.norm_character,mul_one]

/-- Both product masks are removed exactly, and their new frequencies occur
only in the finite Fourier coefficient sum. -/
theorem sharpMask_eq_sum_separated {B X medium D r s : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hr : 0 < r) (hs : 0 < s)
    (hDX : D ≤ X) (hrm : r ≤ medium) (hsm : s ≤ medium) (hmX : medium ≤ X) :
    sharpMask B X medium D r s =
      ∑ a : ZMod (FiniteLogSeparator.modulus X),
      ∑ b : ZMod (FiniteLogSeparator.modulus medium),
        separatorCoefficient B X medium D a b*
          separatorTwist X medium a b r*separatorTwist X medium a b s := by
  classical
  have hm : 0 < medium := hr.trans_le hrm
  have hnear := FiniteLogSeparator.near_indicator_eq_sum_separated hB hD hr hs hDX
    (hrm.trans hmX) (hsm.trans hmX)
  have hselected : (if r*s ≤ medium then (1 : ℂ) else 0) =
      ∑ b : ZMod (FiniteLogSeparator.modulus medium),
        FiniteLogSeparator.coefficient medium 0 b*
          (FiniteLogSeparator.character medium b 1*
            FiniteLogSeparator.character medium b r*FiniteLogSeparator.character medium b s) := by
    simpa only [one_mul,and_iff_right (Nat.mul_pos hr hs)] using
      FiniteLogSeparator.indicator_eq_sum_separated (by omega : 0 < (1 : ℕ)) hr hs
        hm hrm hsm (Nat.zero_le medium)
  calc
    _ = (if X/2 < B*(D*r*s) ∧ D*r*s ≤ X then (1 : ℂ) else 0)*
        (if r*s ≤ medium then (1 : ℂ) else 0) := by
      by_cases hsel : r*s ≤ medium <;>
        by_cases hnear : X/2 < B*(D*r*s) ∧ D*r*s ≤ X <;>
        simp [sharpMask,hsel,hnear]
    _ = _ := by
      rw [hnear,hselected,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      unfold separatorCoefficient separatorTwist
      ring

/-- The exact separator has only logarithmic L1 cost in each of its two
frequencies, independent of the complementary product. -/
theorem sum_norm_separatorCoefficient_le {B X medium D : ℕ}
    (hX : 0 < X) (hm : 0 < medium) (hmX : medium ≤ X) :
    (∑ a : ZMod (FiniteLogSeparator.modulus X),
      ∑ b : ZMod (FiniteLogSeparator.modulus medium),
        ‖separatorCoefficient B X medium D a b‖) ≤
      (Real.log 25+3)^2*(1+Real.log (X : ℝ))^2 := by
  have hA : (X/2)/B ≤ X := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  have hx := FiniteLogSeparator.sum_norm_coefficient_le_log hX hA
  have hm' := FiniteLogSeparator.sum_norm_coefficient_le_log hm (Nat.zero_le medium)
  have hlog : Real.log (medium : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmX)
  have hc : 0 ≤ Real.log 25+3 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 25); linarith
  have hXlog : 0 ≤ 1+Real.log (X : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast hX)
    linarith
  calc
    _ = (∑ a : ZMod (FiniteLogSeparator.modulus X),
          ‖FiniteLogSeparator.coefficient X ((X/2)/B) a‖)*
        (∑ b : ZMod (FiniteLogSeparator.modulus medium),
          ‖FiniteLogSeparator.coefficient medium 0 b‖) := by
      simp only [separatorCoefficient,norm_mul,FiniteLogSeparator.norm_character,mul_one]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ((Real.log 25+3)*(1+Real.log (X : ℝ)))*
        ((Real.log 25+3)*(1+Real.log (X : ℝ))) := by
      apply mul_le_mul hx
      · exact hm'.trans (mul_le_mul_of_nonneg_left (by linarith) hc)
      · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      · positivity
    _ = _ := by ring

noncomputable def momentKernel {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (u v : ℕ) : ℂ :=
  ZMod.stdAddChar ((h.natAbs : ZMod (modulus S g (product c)))*
    (phaseScale a h c hg hsupport : ZMod (modulus S g (product c)))*
    (u : ZMod (modulus S g (product c)))⁻¹*(v : ZMod (modulus S g (product c)))⁻¹)

theorem momentKernel_eq_bilinear {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (u v : ℕ) :
    momentKernel S i a h hg hsupport c u v =
      ZMod.stdAddChar ((((-h)*phaseDifference a c hg hsupport : ℤ) :
        ZMod (modulus S g (product c)))*
        (u : ZMod (modulus S g (product c)))⁻¹*(v : ZMod (modulus S g (product c)))⁻¹) := by
  unfold momentKernel phaseScale
  rw [ConvenientPhaseData.frequency_mul_momentScale]

/-- A separated row twist has norm one and disappears before the true
moment estimate. The column twist remains an admissible beta, independent
of the row variable. -/
theorem twisted_prefix_mass_le_firstMoment {B K N g : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g]
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (rCut sCut : ActualIndex S N i → ℕ)
    (row column : ActualIndex S N i → ℕ → ℂ)
    (hrow : ∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ∀ u ∈ variableBox g r (rCut c) c, ‖row c u‖ ≤ 1) :
    (∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ‖∑ u ∈ variableBox g r (rCut c) c, ∑ v ∈ variableBox g s (sCut c) c,
        row c u*column c v*momentKernel S i a h hg hsupport c u v‖) ≤
      firstMoment S N i e r s a h hg hsupport rCut sCut column := by
  classical
  unfold firstMoment
  apply Finset.sum_le_sum
  intro c hc
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  have he : (∑ v ∈ variableBox g s (sCut c) c,
      row c u*column c v*momentKernel S i a h hg hsupport c u v) =
      row c u*(∑ v ∈ variableBox g s (sCut c) c,
        column c v*momentKernel S i a h hg hsupport c u v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he,norm_mul]
  simpa only [one_mul,momentKernel] using
    mul_le_mul_of_nonneg_right (hrow c hc u hu)
      (norm_nonneg (∑ v ∈ variableBox g s (sCut c) c,
        column c v*momentKernel S i a h hg hsupport c u v))

noncomputable def boxAllowed {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g : ℕ) (c : Index S X z y medium i) (n : ℕ) : Prop :=
  y < n ∧ n ≤ medium ∧ IsZRough z n ∧ n.Coprime (modulus S g (product c))

/-- Even the empty Abel prefix has the exact natural cutoff 2^b-1. -/
theorem variableBox_eq_prefix {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g b n : ℕ) (c : Index S X z y medium i) (hn : n ≤ 2^b) :
    variableBox g b (2^b+n-1) c =
      (Finset.Ico (2^b) (2^b+n)).filter (boxAllowed g c) := by
  classical
  ext v
  simp only [variableBox,boxAllowed,modulus,Finset.mem_filter,Finset.mem_Ico]
  have hp : 0 < 2^b := by positivity
  rw [pow_succ]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hy,hm,hcut,hr,hcop⟩
    exact ⟨⟨hlo,by omega⟩,hy,hm,hr,hcop⟩
  · rintro ⟨⟨hlo,hhi⟩,hy,hm,hr,hcop⟩
    exact ⟨⟨hlo,by omega⟩,hy,hm,by omega,hr,hcop⟩

/-- Finite Abel prefixes on translated ranges are precisely the independent
rough/unit prefix boxes accepted by the inherited moment theorem. -/
theorem sum_range_mask_eq_variableBox {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g b n : ℕ) (c : Index S X z y medium i) (hn : n ≤ 2^b)
    (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, if boxAllowed g c (2^b+j) then F (2^b+j) else 0) =
      ∑ v ∈ variableBox g b (2^b+n-1) c, F v := by
  classical
  rw [variableBox_eq_prefix g b n c hn,Finset.sum_filter,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

end Erdos387Proof.ConvenientWeightedMoment
