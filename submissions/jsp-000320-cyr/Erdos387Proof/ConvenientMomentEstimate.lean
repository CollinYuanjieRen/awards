import Erdos387Proof.ConvenientMomentBound

/-! Dyadic simplification and normalization of the actual convenient moment.
The exact complementary-vector domains and phases are those already verified
in ConvenientMomentBoxes and ConvenientMomentBound. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMomentEstimate
open Erdos387 Erdos387.CoverBPZ
open ConvenientMomentBoxes ConvenientMomentBound ConvenientMomentApplicability
open scoped BigOperators

theorem cardinal_budget_mul_R_le (nC nD nU T nQ m E R V q b ell : ℕ)
    (hC : nC ≤ m*E*R) (hD : nD ≤ E) (hU : nU ≤ V) (hT : T ≤ 2*V)
    (hQ : nQ ≤ 2*q*m*E^2*R) (hell : 1 ≤ ell) (hE : E ≤ V^ell) :
    nC^(2*(ell-1))*(m*(nD*T^ell+nU^(2*ell))*b*nQ)*R ≤
      2^(ell+2)*q*m^(2*ell)*b*(E*R*V)^(2*ell) := by
  calc
    _ ≤ (m*E*R)^(2*(ell-1)) *
        (m*(E*(2*V)^ell+V^(2*ell))*b*(2*q*m*E^2*R))*R := by gcongr
    _ ≤ _ := dyadic_budget_mul_R_le m E R V q b ell hell hE

/-- The actual moment keeps one full R factor of saving. Every cardinal
estimate is proved for the concrete complementary-vector family. -/
theorem firstMoment_pow_mul_R_le {B K N g ell : ℕ}
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
      ∀ v ∈ variableBox g s (sCut c) c, ‖beta c v‖ ≤ 1)
    (hE : 2^e ≤ (2^s)^ell) :
    firstMoment S N i e r s a h hg hsupport rCut sCut beta^(2*ell)*(2^r : ℕ) ≤
      (2^(ell+2)*refinementModulus S*g*(S.k^(N^2))^(2*ell)*SubpowerScale.base N S.k*
        (2^e*2^r*2^s)^(2*ell) : ℕ) := by
  classical
  let I := activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s
  let T := upperEndpoint (SubpowerScale.medium N S.k) s
  let U := ambientBox (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
    (SubpowerScale.medium N S.k) s
  have hIc : I.card ≤ S.k^(N^2)*2^e := card_activeIndices_le i hN
  have hC : (∑ c ∈ I, (variableBox g r (rCut c) c).card) ≤ S.k^(N^2)*2^e*2^r :=
    (sum_box_card_le I g r rCut).trans (Nat.mul_le_mul_right _ hIc)
  have hD : (I.image product).card ≤ 2^e := card_product_image_le
  have hU : U.card ≤ 2^s := card_ambientBox_le _ _ _ _
  have hT : T ≤ 2*2^s := by
    exact (min_le_right _ _).trans (by rw [pow_succ]; omega)
  have hQ : (∑ c ∈ I, modulus S g (product c)*(variableBox g r (rCut c) c).card) ≤
      2*(refinementModulus S*g)*(S.k^(N^2))*(2^e)^2*2^r := by
    calc
      _ ≤ 2*refinementModulus S*g*I.card*2^e*2^r := sum_modulus_mul_card_le g rCut
      _ ≤ 2*refinementModulus S*g*(S.k^(N^2)*2^e)*2^e*2^r := by gcongr
      _ = _ := by ring
  have hraw := cardinal_budget_mul_R_le
    (∑ c ∈ I, (variableBox g r (rCut c) c).card) (I.image product).card U.card T
    (∑ c ∈ I, modulus S g (product c)*(variableBox g r (rCut c) c).card)
    (S.k^(N^2)) (2^e) (2^r) (2^s) (refinementModulus S*g)
    (SubpowerScale.base N S.k) ell hC hD hU hT hQ hell hE
  have hmoment := firstMoment_pow_le_actual S i e r s a h hg hsupport rCut sCut beta
    hB hN hell hellMax hthreshold hkz hh hH hbudget hbeta
  dsimp only at hmoment
  apply (mul_le_mul_of_nonneg_right hmoment (by positivity : (0 : ℝ) ≤ (2^r : ℕ))).trans
  norm_cast
  simpa only [mul_assoc] using hraw

theorem X_eq_pow_xLog (N k : ℕ) :
    SubpowerScale.X N k=2^ConvenientMomentSaving.xLog N k := by
  simpa only [ConvenientMomentSaving.xLog,SubpowerScale.scalePower,mul_comm] using
    SubpowerScale.X_eq_pow_two N k

/-- Nonempty original dyadic fibres determine all exponent restrictions;
none is inserted as an unproved moment-use hypothesis. -/
theorem active_exponent_bounds {B K N e r s : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k}
    (hne : (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s).Nonempty) :
    e ≤ ConvenientMomentSaving.xLog N S.k ∧
      ConvenientMomentSaving.yLog N S.k ≤ r ∧ ConvenientMomentSaving.yLog N S.k ≤ s ∧
      2^r ≤ SubpowerScale.medium N S.k ∧ 2^s ≤ SubpowerScale.medium N S.k := by
  classical
  obtain ⟨c,hc⟩ := hne
  obtain ⟨hD,p,hp,hr,hs⟩ := (Finset.mem_filter.mp hc).2
  have hd := (ConvenientSplitFibre.mem_splitPairDomain_iff c).mp hp
  have hpr := Finset.mem_Ioc.mp hd.1
  have hps := Finset.mem_Ioc.mp hd.2.1
  have hmed := hd.2.2.2.2.2.2.1
  have heX : 2^e ≤ 2^ConvenientMomentSaving.xLog N S.k := by
    rw [← X_eq_pow_xLog]
    exact (Finset.mem_Ico.mp hD).1.trans (product_data c).2.1
  refine ⟨(Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp heX,?_,?_,?_,?_⟩
  · by_contra hnot
    have hle : r+1 ≤ ConvenientMomentSaving.yLog N S.k := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hle
    rw [← ConvenientMomentSaving.y_eq_pow_two] at hpow
    have := (Finset.mem_Ico.mp hr).2
    omega
  · by_contra hnot
    have hle : s+1 ≤ ConvenientMomentSaving.yLog N S.k := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hle
    rw [← ConvenientMomentSaving.y_eq_pow_two] at hpow
    have := (Finset.mem_Ico.mp hs).2
    omega
  · exact (Finset.mem_Ico.mp hr).1.trans
      ((Nat.le_mul_of_pos_right _ ((Nat.zero_le _).trans_lt hps.1)).trans hmed)
  · exact (Finset.mem_Ico.mp hs).1.trans
      ((Nat.le_mul_of_pos_left _ ((Nat.zero_le _).trans_lt hpr.1)).trans hmed)

theorem active_moment_data {B K N e r s : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (hB : 0 < B) (hN : 0 < N)
    (hbudget : (2*SubpowerScale.medium N S.k+1)*MediumFourierTailDecay.height N S.k ≤
      (SubpowerScale.X N S.k/2)/(B*SubpowerScale.medium N S.k))
    (hne : (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s).Nonempty) :
    2 ≤ ConvenientMomentSaving.dyadicMoment e s ∧
      ConvenientMomentSaving.dyadicMoment e s ≤ S.k^100 ∧
      2^e ≤ (2^s)^ConvenientMomentSaving.dyadicMoment e s ∧
      SubpowerScale.y N S.k ≤ 2^r := by
  classical
  have hb := active_exponent_bounds hne
  have hylog : 0 < ConvenientMomentSaving.yLog N S.k := by
    unfold ConvenientMomentSaving.yLog SubpowerScale.scalePower BPZScale.yExp
    positivity
  have hspos : 0 < s := hylog.trans_le hb.2.2.1
  obtain ⟨c,hc⟩ := hne
  have hlo := certificate_complement_lower hB (ConvenientSplitFibre.complementRepresentative_mem c)
  rw [← product_eq_otherValue] at hlo
  have hDshort : 2*SubpowerScale.medium N S.k < product c := by
    have h := shortness_of_floor_bound hlo hbudget (by norm_num : 0 < (1 : ℕ))
      (Nat.succ_le_of_lt (MediumFourierTailDecay.height_pos N S.k))
    simpa using h
  have hDupper := (Finset.mem_Ico.mp (product_mem_interval hc)).2
  rw [pow_succ] at hDupper
  have hpow : 2^s < 2^e := by
    have hS := hb.2.2.2.2
    omega
  have hse : s < e := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow
  refine ⟨ConvenientMomentSaving.dyadicMoment_two_le hspos hse,
    ConvenientMomentSaving.dyadicMoment_le_k_pow hN (by have := S.hk3; omega) hb.1 hb.2.2.1,
    ConvenientMomentSaving.pow_le_pow_dyadicMoment hspos,?_⟩
  rw [ConvenientMomentSaving.y_eq_pow_two]
  exact Nat.pow_le_pow_right (by norm_num) hb.2.1

end Erdos387Proof.ConvenientMomentEstimate
