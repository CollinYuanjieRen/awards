import Erdos387Proof.ConvenientMomentBoxes

/-! The actual complement-indexed convenient moment. The arithmetic phase,
boxes, roughness, fibre multiplicity and shortness are all derived from the
concrete enlarged certificates. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMomentBound
open Erdos387 Erdos387.CoverBPZ ConvenientSplitFibre
open ConvenientMomentBoxes ConvenientMomentApplicability
open scoped BigOperators

noncomputable abbrev ActualIndex {B K : ℕ} (S : BPZSection6Input B K)
    (N : ℕ) (i : Fin S.k) := Index S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i

noncomputable def phaseDifference {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} (a : ℕ)
    (c : Index S X z y medium i) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z) : ℤ :=
  let hcop := (ConvenientPhaseData.sieve_applicability
    (complementRepresentative_mem c) hg hsupport).2.2.1.symm
  (MediumComplementFourier.combinedResidue (complementRepresentative c).1 i g a hcop : ℤ)-i.val

noncomputable def phaseScale {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} (a : ℕ) (h : ℤ)
    (c : Index S X z y medium i) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z) : ℕ :=
  ConvenientPhaseData.momentScale (modulus S g (product c)) h
    (phaseDifference a c hg hsupport)

theorem phaseScale_coprime {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} [NeZero g]
    (a : ℕ) (h : ℤ) (c : Index S X z y medium i)
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z)
    (hkz : S.k ≤ z) : (phaseScale a h c hg hsupport).Coprime (product c) := by
  have : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  have hdelta : Int.gcd (phaseDifference a c hg hsupport) (product c : ℤ)=1 := by
    rw [product_eq_otherValue]
    exact ConvenientPhaseData.gcd_combinedResidue_sub_index_eq_one
      (complementRepresentative_mem c) hkz _
  exact ConvenientPhaseData.momentScale_coprime (product_data c).1
    (dvd_momentModulus (M := refinementModulus S) (g := g) (product_data c).1)
    h _ hdelta

noncomputable def firstMoment {B K g : ℕ} (S : BPZSection6Input B K)
    (N : ℕ) (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g]
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (rCut sCut : ActualIndex S N i → ℕ) (beta : ActualIndex S N i → ℕ → ℂ) : ℝ :=
  ∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
    ∑ u ∈ variableBox g r (rCut c) c,
      ‖∑ v ∈ variableBox g s (sCut c) c,
        beta c v*ZMod.stdAddChar ((h.natAbs : ZMod (modulus S g (product c)))*
          (phaseScale a h c hg hsupport : ZMod (modulus S g (product c)))*
          (u : ZMod (modulus S g (product c)))⁻¹*
          (v : ZMod (modulus S g (product c)))⁻¹)‖

/-- The precise inherited moment budget, before the dyadic cardinal
simplifications. No family/cardinality/shortness bound is assumed. -/
theorem firstMoment_pow_le_actual {B K N g ell : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g]
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (rCut sCut : ActualIndex S N i → ℕ) (beta : ActualIndex S N i → ℕ → ℂ)
    (hB : 0 < B) (hN : 0 < N) (hell : 1 ≤ ell) (hellMax : ell ≤ S.k^100)
    (hthreshold : uniformMomentThreshold S.k ≤ N)
    (hkz : S.k ≤ SubpowerScale.z N S.k) (hh : h≠0)
    (hH : h.natAbs ≤ MediumFourierTailDecay.height N S.k)
    (hbudget : (2*SubpowerScale.medium N S.k+1)*MediumFourierTailDecay.height N S.k ≤
      (SubpowerScale.X N S.k/2)/(B*SubpowerScale.medium N S.k))
    (hbeta : ∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ∀ v ∈ variableBox g s (sCut c) c, ‖beta c v‖ ≤ 1) :
    let I := activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s
    let T := upperEndpoint (SubpowerScale.medium N S.k) s
    let U := ambientBox (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
      (SubpowerScale.medium N S.k) s
    firstMoment S N i e r s a h hg hsupport rCut sCut beta^(2*ell) ≤
      ((∑ c ∈ I, (variableBox g r (rCut c) c).card : ℕ) : ℝ)^(2*(ell-1))*
        (((S.k^(N^2)*((I.image product).card*T^ell+U.card^(2*ell))*SubpowerScale.base N S.k)*
          (∑ c ∈ I, modulus S g (product c)*(variableBox g r (rCut c) c).card) : ℕ) : ℝ) := by
  classical
  have : ∀ d, NeZero (modulus S g d) := fun d => inferInstance
  dsimp only
  apply ConvenientMomentSaving.firstMoment_pow_le
    (by have := S.hk3; omega) hell
    (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s)
    product (modulus S g) (fun _ => h.natAbs) (fun c => phaseScale a h c hg hsupport)
    (fun c => variableBox g s (sCut c) c) (fun c => variableBox g r (rCut c) c)
    (ambientBox (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
      (SubpowerScale.medium N S.k) s)
    (fun _ => SubpowerScale.medium N S.k) beta
  · exact (reciprocalMomentThreshold_le_uniform hellMax).trans hthreshold
  · exact min_le_left _ _
  · intro c _
    exact (product_data c).1
  · intro c _
    exact dvd_momentModulus (product_data c).1
  · intro c _
    exact (product_data c).2.2.2
  · intro c _
    exact variableBox_subset_ambient _ _ _ _
  · intro v hv
    exact (ambientBox_data hv).1
  · intro v hv
    exact (ambientBox_data hv).2.1
  · intro v hv
    exact (ambientBox_data hv).2.2
  · intro c _ v hv
    exact variableBox_unit hv
  · intro d hd
    exact fibre_card_le i _ hN hd
  · exact hbeta
  · intro c _
    exact phaseScale_coprime a h c hg hsupport hkz
  · intro c _ v hv
    exact variableBox_unit hv
  · intro c _ v hv
    exact ((ambientBox_data (variableBox_subset_ambient _ _ _ _ hv)).2.1).trans
      (min_le_left _ _)
  · intro c _
    have hlo := certificate_complement_lower hB (complementRepresentative_mem c)
    rw [← product_eq_otherValue] at hlo
    have hs := shortness_of_floor_bound hlo hbudget (Int.natAbs_pos.mpr hh) hH
    exact (show SubpowerScale.medium N S.k ≤ 2*SubpowerScale.medium N S.k by omega).trans_lt hs

/-- Pure integer simplification of the concrete moment budget. Multiplying
by R keeps the saving visible without division or fractional powers. -/
theorem dyadic_budget_mul_R_le (m E R V q b ell : ℕ)
    (hell : 1 ≤ ell) (hE : E ≤ V^ell) :
    (m*E*R)^(2*(ell-1)) *
      (m*(E*(2*V)^ell+V^(2*ell))*b*(2*q*m*E^2*R))*R ≤
      2^(ell+2)*q*m^(2*ell)*b*(E*R*V)^(2*ell) := by
  have hdiag : E*(2*V)^ell+V^(2*ell) ≤ 2^(ell+1)*V^(2*ell) := by
    calc
      _ ≤ V^ell*(2*V)^ell+V^(2*ell) := by gcongr
      _ = (2^ell+1)*V^(2*ell) := by
        rw [mul_pow,show 2*ell=ell+ell by omega,pow_add]
        ring
      _ ≤ (2^ell+2^ell)*V^(2*ell) := by
        gcongr
        exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
      _ = 2^(ell+1)*V^(2*ell) := by rw [pow_succ]; ring
  calc
    _ ≤ (m*E*R)^(2*(ell-1)) *
        (m*(2^(ell+1)*V^(2*ell))*b*(2*q*m*E^2*R))*R := by gcongr
    _ = _ := by
      have hexp : 2*ell=2*(ell-1)+2 := by omega
      simp only [hexp,mul_pow,pow_add,pow_two]
      ring

end Erdos387Proof.ConvenientMomentBound
