import Erdos387Proof.SeparatedTypeIBound

/-! Exact stopped-leaf coefficients and the two Fourier separations on
actual Type-II rectangles. Coefficients are extended along the injective
selected-product map; no multiplicity or arbitrary coupled weight is lost. -/

namespace Erdos387Proof.SeparatedTypeIIAssembly

open scoped BigOperators
open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase SeparatedTypeIICauchy
open SeparatedBuchstabDecomposition SeparatedBuchstabSeparation SeparatedProductWindow
open SeparatedTypeIISaving MaskedReciprocalPhase

noncomputable def stoppedProduct (y : ℕ) (l : {l // l ∈ stoppedLeaves y}) : ℕ :=
  l.val.chosen.prod

theorem stoppedProduct_injective (y : ℕ) : Function.Injective (stoppedProduct y) := by
  intro a b hab
  apply Subtype.ext
  exact chosen_prod_injective y 1 y a.val b.val ((mem_stoppedLeaves y a.val).mp a.property).1
    ((mem_stoppedLeaves y b.val).mp b.property).1 hab

noncomputable def stoppedSign (y u : ℕ) : ℂ :=
  Function.extend (stoppedProduct y) (fun l => (-1 : ℂ)^l.val.chosen.length) (fun _ => 0) u

noncomputable def stoppedPrime (y u : ℕ) : ℕ :=
  Function.extend (stoppedProduct y) (fun l => l.val.chosen.getLastD 0) (fun _ => 0) u

theorem stoppedSign_prod (y : ℕ) (l : Leaf) (hl : l ∈ stoppedLeaves y) :
    stoppedSign y l.chosen.prod = (-1 : ℂ)^l.chosen.length := by
  exact (stoppedProduct_injective y).extend_apply _ _ ⟨l,hl⟩

theorem stoppedPrime_prod (y : ℕ) (l : Leaf) (hl : l ∈ stoppedLeaves y) :
    stoppedPrime y l.chosen.prod = l.chosen.getLastD 0 := by
  exact (stoppedProduct_injective y).extend_apply _ _ ⟨l,hl⟩

/-- The prime cutoff is exactly the last chosen prime from the source
Buchstab branch; it is not a substitute roughness condition. -/
theorem stoppedPrime_data (y : ℕ) (hy : 1 ≤ y) (l : Leaf) (hl : l ∈ stoppedLeaves y) :
    (stoppedPrime y l.chosen.prod).Prime ∧ stoppedPrime y l.chosen.prod < y ∧
    ∀ n, l.value n = if l.chosen.prod ∣ n then
      (-1 : ℂ)^l.chosen.length * roughIndicator (stoppedPrime y l.chosen.prod) (n/l.chosen.prod)
      else 0 := by
  obtain ⟨hl',hs⟩ := (mem_stoppedLeaves y l).mp hl
  obtain ⟨pre,p,hchosen,hbound,hprime,hpy,hvalue⟩ := typeII_value y 1 y l hy hl' hs
  have hp : stoppedPrime y l.chosen.prod = p := by
    rw [stoppedPrime_prod y l hl,hchosen]
    simp
  rw [hp]
  exact ⟨hprime,hpy,hvalue⟩

theorem dyadic_stopped_weights (y M j u : ℕ) (hy : 1 ≤ y) (hu : u ∈ dyadicUnits y M j) :
    ‖stoppedSign y u‖ ≤ 1 ∧ stoppedPrime y u ≤ y := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
  constructor
  · rw [stoppedSign_prod y l hl]
    simp
  · exact (stoppedPrime_data y hy l hl).2.1.le

noncomputable def leftWeight (y Q : ℕ) (r : ZMod (2*y+1)) (s : ZMod (2*Q+1))
    (u : ℕ) : ℂ :=
  stoppedSign y u * ZMod.stdAddChar (-(r*(stoppedPrime y u : ZMod (2*y+1)))) *
    windowLeft (Q/2) Q u s / 2

noncomputable def rightWeight (y Q : ℕ) (r : ZMod (2*y+1)) (s : ZMod (2*Q+1))
    (m : ℕ) : ℂ :=
  ZMod.stdAddChar (r*(roughCutoff y m : ZMod (2*y+1))) * windowRight Q m s

theorem norm_leftWeight_le (y M Q j u : ℕ) (hy : 1 ≤ y)
    (hu : u ∈ dyadicUnits y M j) (r : ZMod (2*y+1)) (s : ZMod (2*Q+1)) :
    ‖leftWeight y Q r s u‖ ≤ 1 :=
  normalized_left_weight_le y (Q/2) Q u (stoppedPrime y u) r s (stoppedSign y u)
    (dyadic_stopped_weights y M j u hy hu).1

theorem norm_rightWeight_le (y Q m : ℕ) (r : ZMod (2*y+1)) (s : ZMod (2*Q+1)) :
    ‖rightWeight y Q r s m‖ ≤ 1 := by
  simpa only [rightWeight,one_mul] using right_weight_le y Q m r s 1 (by simp)

/-- Both original masks remain in this exact containing rectangle. -/
noncomputable def stoppedRectangle (M Q y j : ℕ) [NeZero M]
    (c : ℤ) (χ : AddChar ℤ ℂ) : ℂ :=
  ∑ u ∈ dyadicUnits y M j, ∑ m ∈ Finset.Ioc (Q/(4*2^j)) (Q/2^j),
    windowIndicator (Q/2) Q u m * roughIndicator (stoppedPrime y u) m *
      stoppedSign y u * (χ ((u : ℤ)*m)*seq M c 0 [] ((u : ℤ)*m))

/-- Exact finite double separation. The norm-two window factor is restored
as an explicit factor2 in every separated bilinear sum. -/
theorem stoppedRectangle_fourier (M Q y j : ℕ) [NeZero M] (hy : 1 ≤ y)
    (c : ℤ) (χ : AddChar ℤ ℂ) :
    stoppedRectangle M Q y j c χ =
      ∑ s : ZMod (2*Q+1), thresholdCoefficient Q s *
        ∑ r : ZMod (2*y+1), thresholdCoefficient y r *
          (2*dyadicBilinear M Q y j c χ (leftWeight y Q r s) (rightWeight y Q r s)) := by
  classical
  let U := dyadicUnits y M j
  let V := Finset.Ioc (Q/(4*2^j)) (Q/2^j)
  let F : ℕ → ℕ → ℂ := fun u m => χ ((u : ℤ)*m)*seq M c 0 [] ((u : ℤ)*m)
  have hu (u : ℕ) (hu : u ∈ U) : 0 < u := (dyadicUnits_data y M j u hy hu).1
  have hm (m : ℕ) (hm : m ∈ V) : m ≤ Q :=
    (Finset.mem_Ioc.mp hm).2.trans (Nat.div_le_self _ _)
  have hstart : stoppedRectangle M Q y j c χ =
      ∑ u ∈ U, ∑ m ∈ V, windowIndicator (Q/2) Q u m *
        (roughIndicator (stoppedPrime y u) m*stoppedSign y u*F u m) := by
    unfold stoppedRectangle
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [F]
    ring
  apply hstart.trans
  have hw := weighted_window_separation U V (Q/2) Q id id (Nat.div_le_self _ _) hu hm
    (fun u m => roughIndicator (stoppedPrime y u) m*stoppedSign y u*F u m)
  simp only [id_eq] at hw
  apply hw.trans
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have he : (∑ u ∈ U, ∑ m ∈ V,
      windowLeft (Q/2) Q u s*windowRight Q m s*
        (roughIndicator (stoppedPrime y u) m*stoppedSign y u*F u m)) =
      ∑ u ∈ U, ∑ m ∈ V, roughIndicator (stoppedPrime y u) m*
        (stoppedSign y u*windowLeft (Q/2) Q u s)*(windowRight Q m s)*F u m := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [he, weighted_rough_separation_factors U V y (stoppedPrime y)
    (fun u hu => (dyadic_stopped_weights y M j u hy hu).2)
    (fun u => stoppedSign y u*windowLeft (Q/2) Q u s) (fun m => windowRight Q m s) F]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  unfold dyadicBilinear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [leftWeight,rightWeight,F]
  ring

/-- The concrete nonexceptional certificate estimate after BOTH finite
separations. The coefficient costs and factor2 remain explicit. -/
theorem norm_stoppedRectangle_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q j : ℕ) (hQ : C.q C.i₀ ≤ Q)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖stoppedRectangle C.modulus Q (BPZScale.y t S.k) j (h*((b : ℤ)-C.i₀.val)) χ‖ ≤
      (1+Real.log (2*(Q : ℝ)+1))*(1+Real.log (2*(BPZScale.y t S.k : ℝ)+1))*
        (2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ))) := by
  classical
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
    omega
  have hy : 1 ≤ BPZScale.y t S.k := ht1.trans (base_le_y t S.k ht1)
  let R : ℝ := 2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ))
  have hR : 0 ≤ R := by positivity
  have hc (s : ZMod (2*Q+1)) (r : ZMod (2*BPZScale.y t S.k+1)) :
      ‖2*dyadicBilinear C.modulus Q (BPZScale.y t S.k) j (h*((b : ℤ)-C.i₀.val)) χ
        (leftWeight (BPZScale.y t S.k) Q r s) (rightWeight (BPZScale.y t S.k) Q r s)‖ ≤ R := by
    have he := norm_dyadicBilinear_sq_le_six C ht hg hM Q j hQ b hb h hh χ hχ
      (leftWeight (BPZScale.y t S.k) Q r s) (rightWeight (BPZScale.y t S.k) Q r s)
      (fun u hu => norm_leftWeight_le _ _ _ _ _ hy hu r s)
      (fun m hm => norm_rightWeight_le _ _ _ r s)
    have hs := Real.le_sqrt_of_sq_le he
    simpa only [norm_mul,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2)
  rw [stoppedRectangle_fourier _ _ _ _ hy]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ s : ZMod (2*Q+1), ‖thresholdCoefficient Q s‖ *
        ((∑ r : ZMod (2*BPZScale.y t S.k+1), ‖thresholdCoefficient (BPZScale.y t S.k) r‖)*R) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hc s r) (norm_nonneg _)
    _ = (∑ s : ZMod (2*Q+1), ‖thresholdCoefficient Q s‖)*
        (∑ r : ZMod (2*BPZScale.y t S.k+1), ‖thresholdCoefficient (BPZScale.y t S.k) r‖)*R := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      have hQlog : 0 ≤ 1+Real.log (2*(Q : ℝ)+1) := by
        have := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) Q; linarith : (1:ℝ)≤2*(Q : ℝ)+1)
        linarith
      have hqy : (∑ s : ZMod (2*Q+1), ‖thresholdCoefficient Q s‖)*
          (∑ r : ZMod (2*BPZScale.y t S.k+1), ‖thresholdCoefficient (BPZScale.y t S.k) r‖) ≤
          (1+Real.log (2*(Q : ℝ)+1))*(1+Real.log (2*(BPZScale.y t S.k : ℝ)+1)) := by
        apply mul_le_mul _ _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hQlog
        · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,add_comm] using sum_norm_thresholdCoefficient_le Q
        · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,add_comm] using sum_norm_thresholdCoefficient_le (BPZScale.y t S.k)
      exact mul_le_mul_of_nonneg_right hqy hR

end Erdos387Proof.SeparatedTypeIIAssembly
