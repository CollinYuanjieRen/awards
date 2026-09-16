import Erdos387Proof.SeparatedTypeIIAssembly

/-! Exact transfer of the original stopped Buchstab sum to the actual
unit-filtered dyadic rectangles. No coupled product-window constraint is
removed; nonunit multipliers vanish by the original phase mask. -/

namespace Erdos387Proof.SeparatedBuchstabAssembly

open scoped BigOperators
open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase SeparatedTypeIICauchy
open SeparatedBuchstabDecomposition SeparatedBuchstabSeparation SeparatedProductWindow
open SeparatedTypeIISaving SeparatedTypeIBound SeparatedTypeIIAssembly MaskedReciprocalPhase

/-- Exact m-fibre of the original product window. -/
theorem product_window_domain (Q u : ℕ) (hu : 0 < u) :
    (Finset.Icc 1 Q).filter (fun m => Q/2 < u*m ∧ u*m ≤ Q) =
      Finset.Ioc (Q/(2*u)) (Q/u) := by
  ext m
  simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
  have hlo : Q/(2*u) < m ↔ Q/2 < u*m := by
    rw [← Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul hu, Nat.mul_comm m u]
  have hhi : m ≤ Q/u ↔ u*m ≤ Q := by
    rw [Nat.le_div_iff_mul_le hu, Nat.mul_comm m u]
  constructor
  · exact fun h => ⟨hlo.mpr h.2.1,hhi.mpr h.2.2⟩
  · intro h
    refine ⟨⟨?_,h.2.trans (Nat.div_le_self _ _)⟩,hlo.mp h.1,hhi.mp h.2⟩
    exact Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt h.1)

noncomputable def productPhase (M : ℕ) [NeZero M] (c : ℤ) (χ : AddChar ℤ ℂ)
    (u m : ℕ) : ℂ := χ ((u : ℤ)*m)*seq M c 0 [] ((u : ℤ)*m)

noncomputable def stoppedPairWeight (M y : ℕ) [NeZero M] (c : ℤ) (χ : AddChar ℤ ℂ)
    (x : Leaf × ℕ) : ℂ :=
  stoppedSign y x.1.chosen.prod * roughIndicator (stoppedPrime y x.1.chosen.prod) x.2 *
    productPhase M c χ x.1.chosen.prod x.2

theorem stopped_leaf_interval (M Q y : ℕ) [NeZero M] (hy : 1 ≤ y)
    (c : ℤ) (χ : AddChar ℤ ℂ) (l : Leaf) (hl : l ∈ stoppedLeaves y) :
    (∑ n ∈ Finset.Ioc (Q/2) Q, l.value n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ))) =
      ∑ m ∈ Finset.Ioc (Q/(2*l.chosen.prod)) (Q/l.chosen.prod),
        stoppedPairWeight M y c χ (l,m) := by
  obtain ⟨hl',hs⟩ := (mem_stoppedLeaves y l).mp hl
  obtain ⟨pre,p,hchosen,hbound,hprime,hpy,he⟩ :=
    typeII_interval_sum (Q/2) Q y 1 y l hy hl' hs (fun _ => True)
      (fun n => χ (n : ℤ)*seq M c 0 [] (n : ℤ))
  have hp : stoppedPrime y l.chosen.prod = p := by
    rw [stoppedPrime_prod y l hl,hchosen]
    simp
  simp only [if_true,Finset.filter_true,Nat.div_div_eq_div_mul,Nat.cast_mul] at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [stoppedPairWeight,stoppedSign_prod y l hl,hp,productPhase]
  ring

/-- The original stopped complex sum is the same finite original-pair
sum used by the previously proved disjoint dyadic partition. -/
theorem stopped_sum_eq_originalPairs (M Q y : ℕ) [NeZero M] (hy : 1 ≤ y)
    (c : ℤ) (χ : AddChar ℤ ℂ) :
    (∑ l ∈ stoppedLeaves y, ∑ n ∈ Finset.Ioc (Q/2) Q,
      l.value n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ))) =
      ∑ x ∈ originalPairs y Q (fun _ _ => True), stoppedPairWeight M y c χ x := by
  classical
  unfold originalPairs
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro l hl
  rw [stopped_leaf_interval M Q y hy c χ l hl]
  have hu := (chosen_prime_data y 1 y l ((mem_stoppedLeaves y l).mp hl).1).2.2
  rw [← product_window_domain Q l.chosen.prod hu,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [and_true]

noncomputable def dyadicUnitLeaves (y M j : ℕ) : Finset Leaf := by
  classical
  exact (stoppedLeaves y).filter (fun l => 2^j ≤ l.chosen.prod ∧
    l.chosen.prod < 2^(j+1) ∧ Nat.Coprime l.chosen.prod M)

theorem image_dyadicUnitLeaves (y M j : ℕ) :
    (dyadicUnitLeaves y M j).image (fun l => l.chosen.prod) = dyadicUnits y M j := by
  classical
  ext u
  simp only [dyadicUnitLeaves,dyadicUnits,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨l,⟨hl,hlo,hhi,hcop⟩,rfl⟩
    exact ⟨⟨l,hl,rfl⟩,hlo,hhi,hcop⟩
  · rintro ⟨⟨l,hl,rfl⟩,hlo,hhi,hcop⟩
    exact ⟨l,⟨hl,hlo,hhi,hcop⟩,rfl⟩

/-- Exact dyadic reindexing after the original nonunit phase terms vanish.
The product window survives as the same windowIndicator in every term. -/
theorem dyadic_sum_eq_stoppedRectangle (M Q y j : ℕ) [NeZero M]
    (c : ℤ) (χ : AddChar ℤ ℂ) :
    (∑ x ∈ dyadicPairs y Q j (fun _ _ => True), stoppedPairWeight M y c χ x) =
      stoppedRectangle M Q y j c χ := by
  classical
  unfold stoppedRectangle
  rw [← image_dyadicUnitLeaves y M j,Finset.sum_image]
  · unfold dyadicPairs dyadicUnitLeaves
    rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hblock : 2^j ≤ l.chosen.prod ∧ l.chosen.prod < 2^(j+1)
    · obtain ⟨hlo,hhi⟩ := hblock
      by_cases hunit : Nat.Coprime l.chosen.prod M
      · simp only [hlo,hhi,true_and,and_true,if_true]
        rw [if_pos hunit]
        apply Finset.sum_congr rfl
        intro m hm
        unfold stoppedPairWeight productPhase windowIndicator
        split_ifs <;> ring
      · simp only [hlo,hhi,hunit,true_and,and_true,if_true,if_false]
        apply Finset.sum_eq_zero
        intro m hm
        have hz := seq_mul_eq_zero_of_not_coprime M c l.chosen.prod hunit (m : ℤ)
        simp only [stoppedPairWeight,productPhase,hz,mul_zero,ite_self]
    · have hblock' : ¬(2^j ≤ l.chosen.prod ∧ l.chosen.prod < 2^(j+1) ∧
          Nat.Coprime l.chosen.prod M) := by tauto
      simp [hblock,hblock']
  · intro a ha b hb hab
    exact chosen_prod_injective y 1 y a b
      ((mem_stoppedLeaves y a).mp (Finset.mem_filter.mp ha).1).1
      ((mem_stoppedLeaves y b).mp (Finset.mem_filter.mp hb).1).1 hab

/-- Complete exact unweighted phase assembly before applying norm bounds.
All dyadic summands are the concrete rectangles whose cancellation was
proved with both finite Fourier coefficient costs. -/
theorem rough_phase_eq_typeI_add_rectangles (M Q y : ℕ) [NeZero M]
    (hy : 1 ≤ y) (c : ℤ) (χ : AddChar ℤ ℂ) :
    (∑ n ∈ Finset.Ioc (Q/2) Q,
      roughIndicator y n*(χ (n : ℤ)*seq M c 0 [] (n : ℤ))) =
      typeISum M Q y c χ + ∑ j ∈ Finset.range (Nat.log2 (y^2)+1),
        stoppedRectangle M Q y j c χ := by
  rw [rough_phase_eq_typeI_add_stopped M Q y hy,
    stopped_sum_eq_originalPairs M Q y hy,
    sum_originalPairs_eq_dyadic y Q hy (fun _ _ => True)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact dyadic_sum_eq_stoppedRectangle M Q y j c χ

/-- A fully concrete uniform-in-linear-character rough reciprocal phase
bound. No separate cancellation hypothesis remains in this theorem. -/
theorem norm_rough_phase_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q : ℕ) (hQ : C.q C.i₀ ≤ Q)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ v ∈ Finset.Ioc (Q/2) Q, roughIndicator (BPZScale.y t S.k) v*
      (χ (v : ℤ)*seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] (v : ℤ))‖ ≤
      (4*(Q : ℝ)/(t : ℝ))*(1+Real.log (BPZScale.y t S.k)) +
      ((Nat.log2 ((BPZScale.y t S.k)^2)+1 : ℕ) : ℝ)*
        (1+Real.log (2*(Q : ℝ)+1))*(1+Real.log (2*(BPZScale.y t S.k : ℝ)+1))*
          (2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ))) := by
  classical
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
    omega
  have hy : 1 ≤ BPZScale.y t S.k := ht1.trans (base_le_y t S.k ht1)
  rw [rough_phase_eq_typeI_add_rectangles _ _ _ hy]
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_typeISum_le C ht hg hM Q hQ b hb h hh χ hχ)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (Nat.log2 ((BPZScale.y t S.k)^2)+1),
        (1+Real.log (2*(Q : ℝ)+1))*(1+Real.log (2*(BPZScale.y t S.k : ℝ)+1))*
          (2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_stoppedRectangle_le C ht hg hM Q j hQ b hb h hh χ hχ
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end Erdos387Proof.SeparatedBuchstabAssembly
