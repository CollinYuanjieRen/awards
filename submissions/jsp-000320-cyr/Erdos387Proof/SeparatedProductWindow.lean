import Erdos387Proof.SeparatedBuchstabSeparation

/-!
# Exact product-window separation and first-crossing dyadic rectangles

The difference of two threshold indicators uses a common Fourier coefficient
family. A finite disjoint partition then places the actual Buchstab leaves
in rectangles of the correct m-length, retaining the original window and
all external predicates. No arbitrary coupled weight is cancelled.
-/

namespace Erdos387Proof.SeparatedProductWindow

open scoped BigOperators
open SeparatedBuchstabDecomposition SeparatedBuchstabSeparation

def windowIndicator (A B u m : ℕ) : ℂ :=
  if A < u*m ∧ u*m ≤ B then 1 else 0

/-- Both floors are exact, and A≤B permits subtraction of the lower cutoff. -/
theorem window_eq_threshold_difference (A B u m : ℕ) (hAB : A ≤ B) (hu : 0 < u) :
    windowIndicator A B u m =
      (if m ≤ B/u then (1 : ℂ) else 0) - (if m ≤ A/u then (1 : ℂ) else 0) := by
  have he (T : ℕ) : m ≤ T/u ↔ u*m ≤ T := by
    rw [Nat.le_div_iff_mul_le hu, Nat.mul_comm m u]
  simp only [he,windowIndicator]
  by_cases hA : u*m ≤ A
  · have hB := hA.trans hAB
    simp [hA,hB,show ¬A<u*m by omega]
  · by_cases hB : u*m ≤ B <;> simp [hA,hB,show A<u*m by omega]

noncomputable def windowLeft (A B u : ℕ) (h : ZMod (2*B+1)) : ℂ :=
  ZMod.stdAddChar (h*((B/u : ℕ) : ZMod (2*B+1))) - ZMod.stdAddChar (h*((A/u : ℕ) : ZMod (2*B+1)))

noncomputable def windowRight (B m : ℕ) (h : ZMod (2*B+1)) : ℂ :=
  ZMod.stdAddChar (-(h*(m : ZMod (2*B+1))))

theorem norm_windowLeft_le (A B u : ℕ) (h : ZMod (2*B+1)) :
    ‖windowLeft A B u h‖ ≤ 2 := by
  unfold windowLeft
  have hh := norm_sub_le (ZMod.stdAddChar (h*((B/u : ℕ) : ZMod (2*B+1))) : ℂ)
    (ZMod.stdAddChar (h*((A/u : ℕ) : ZMod (2*B+1))) : ℂ)
  norm_num at hh
  exact hh

theorem norm_windowRight (B m : ℕ) (h : ZMod (2*B+1)) :
    ‖windowRight B m h‖ = 1 := by simp [windowRight]

/-- One Fourier family separates both endpoints: a single logarithmic
coefficient cost and a left factor bounded by2. -/
theorem window_fourier (A B u m : ℕ) (hAB : A ≤ B) (hu : 0 < u) (hm : m ≤ B) :
    windowIndicator A B u m =
      ∑ h : ZMod (2*B+1), thresholdCoefficient B h * windowLeft A B u h * windowRight B m h := by
  rw [window_eq_threshold_difference A B u m hAB hu,
    threshold_fourier B m (B/u) hm (Nat.div_le_self _ _),
    threshold_fourier B m (A/u) hm ((Nat.div_le_self _ _).trans hAB),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  unfold windowLeft windowRight
  ring

/-- Pointwise norm mass of the product-window expansion. -/
theorem window_coefficient_mass_le (A B u m : ℕ) :
    (∑ h : ZMod (2*B+1), ‖thresholdCoefficient B h * windowLeft A B u h * windowRight B m h‖) ≤
      2*(Real.log (2*B+1 : ℕ)+1) := by
  calc
    _ ≤ ∑ h : ZMod (2*B+1), ‖thresholdCoefficient B h‖*2 := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul, norm_mul, norm_windowRight, mul_one]
      exact mul_le_mul_of_nonneg_left (norm_windowLeft_le A B u h) (norm_nonneg _)
    _ = 2*∑ h : ZMod (2*B+1), ‖thresholdCoefficient B h‖ := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_thresholdCoefficient_le B) (by norm_num)

/-- Exact weighted separation with unchanged complex W. -/
theorem weighted_window_separation {α β : Type*} (U : Finset α) (V : Finset β)
    (A B : ℕ) (u : α → ℕ) (m : β → ℕ) (hAB : A ≤ B)
    (hu : ∀ x ∈ U, 0 < u x) (hm : ∀ x ∈ V, m x ≤ B) (W : α → β → ℂ) :
    (∑ x ∈ U, ∑ z ∈ V, windowIndicator A B (u x) (m z)*W x z) =
      ∑ h : ZMod (2*B+1), thresholdCoefficient B h *
        ∑ x ∈ U, ∑ z ∈ V, windowLeft A B (u x) h * windowRight B (m z) h * W x z := by
  calc
    _ = ∑ x ∈ U, ∑ z ∈ V,
        (∑ h : ZMod (2*B+1), thresholdCoefficient B h *
          windowLeft A B (u x) h * windowRight B (m z) h) * W x z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      rw [window_fourier A B (u x) (m z) hAB (hu x hx) (hm z hz)]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]

/-- A dyadic u-block forces the correct shorter m-interval from the
original Q/2<u*m≤Q window. -/
theorem dyadic_rectangle_membership (Q U u m : ℕ) (hU : 0 < U)
    (hulo : U ≤ u) (huhi : u < 2*U) (hlo : Q/2 < u*m) (hhi : u*m ≤ Q) :
    m ∈ Finset.Ioc (Q/(4*U)) (Q/U) := by
  have hmlo : Q/2 < (2*U)*m := hlo.trans_le (Nat.mul_le_mul_right m huhi.le)
  have hdiv : Q/2/(2*U) < m :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using hmlo)
  have hdiv' : Q/(4*U) < m := by
    simpa only [Nat.div_div_eq_div_mul, show 2*(2*U)=4*U by ring] using hdiv
  have hmhi : m ≤ Q/U := (Nat.le_div_iff_mul_le hU).mpr (by
    exact (by simpa [Nat.mul_comm] using (Nat.mul_le_mul_right m hulo).trans hhi))
  exact Finset.mem_Ioc.mpr ⟨hdiv',hmhi⟩

/-- The containing rectangle has at most Q/U m-values, not Q. -/
theorem card_dyadic_m_interval_le (Q U : ℕ) :
    (Finset.Ioc (Q/(4*U)) (Q/U)).card ≤ Q/U := by
  simp only [Nat.card_Ioc]
  exact Nat.sub_le _ _

/-- Every actual stopped leaf has a unique dyadic scale in the explicit
finite index range. -/
theorem stopped_leaf_dyadic (y : ℕ) (hy : 1 ≤ y) (l : Leaf)
    (hl : l ∈ leaves y 1 (primeList y)) (hs : l.stopped = true) :
    ∃ j ∈ Finset.range (Nat.log2 (y^2)+1),
      2^j ≤ l.chosen.prod ∧ l.chosen.prod < 2^(j+1) := by
  have hdom := (e5_leaf_domain y hy l hl).2 hs
  have hu : 0 < l.chosen.prod := by omega
  have hj := (Nat.log2_eq_iff hu.ne').mp rfl
  refine ⟨Nat.log2 l.chosen.prod, ?_, hj⟩
  have hpow : 2^Nat.log2 l.chosen.prod ≤ y^2 := hj.1.trans hdom.2.1
  have hne : y^2 ≠ 0 := by positivity
  have := (Nat.le_log2 hne).mpr hpow
  simp only [Finset.mem_range]
  omega

noncomputable def stoppedLeaves (y : ℕ) : Finset Leaf := by
  classical
  exact (leaves y 1 (primeList y)).toFinset.filter (fun l => l.stopped = true)

theorem mem_stoppedLeaves (y : ℕ) (l : Leaf) :
    l ∈ stoppedLeaves y ↔ l ∈ leaves y 1 (primeList y) ∧ l.stopped = true := by
  classical
  simp only [stoppedLeaves, Finset.mem_filter, List.mem_toFinset]

/-- Original positive pairs, with the original product window and P. -/
noncomputable def originalPairs (y Q : ℕ) (P : Leaf → ℕ → Prop) : Finset (Leaf × ℕ) := by
  classical
  exact (stoppedLeaves y ×ˢ Finset.Icc 1 Q).filter
    (fun x => Q/2 < x.1.chosen.prod*x.2 ∧ x.1.chosen.prod*x.2 ≤ Q ∧ P x.1 x.2)

/-- One containing rectangle, filtered by exactly the ORIGINAL window
and external predicate, not by an assumed separable replacement. -/
noncomputable def dyadicPairs (y Q j : ℕ) (P : Leaf → ℕ → Prop) : Finset (Leaf × ℕ) := by
  classical
  exact (((stoppedLeaves y).filter (fun l => 2^j ≤ l.chosen.prod ∧ l.chosen.prod < 2^(j+1))) ×ˢ
    Finset.Ioc (Q/(4*2^j)) (Q/2^j)).filter
      (fun x => Q/2 < x.1.chosen.prod*x.2 ∧ x.1.chosen.prod*x.2 ≤ Q ∧ P x.1 x.2)

theorem mem_originalPairs (y Q : ℕ) (P : Leaf → ℕ → Prop) (l : Leaf) (m : ℕ) :
    (l,m) ∈ originalPairs y Q P ↔
      l ∈ stoppedLeaves y ∧ (1 ≤ m ∧ m ≤ Q) ∧
        Q/2 < l.chosen.prod*m ∧ l.chosen.prod*m ≤ Q ∧ P l m := by
  classical
  simp only [originalPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- The finite m-range in originalPairs adds no mathematical condition:
positivity and m≤Q follow from the original product window and leaf data. -/
theorem mem_originalPairs_iff_window (y Q : ℕ) (P : Leaf → ℕ → Prop) (l : Leaf) (m : ℕ) :
    (l,m) ∈ originalPairs y Q P ↔
      l ∈ stoppedLeaves y ∧ Q/2 < l.chosen.prod*m ∧ l.chosen.prod*m ≤ Q ∧ P l m := by
  rw [mem_originalPairs]
  constructor
  · rintro ⟨hl,hm,hlo,hhi,hP⟩
    exact ⟨hl,hlo,hhi,hP⟩
  · rintro ⟨hl,hlo,hhi,hP⟩
    have hll := ((mem_stoppedLeaves y l).mp hl).1
    have hu := (chosen_prime_data y 1 y l hll).2.2
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      simp at hlo
    exact ⟨hl,⟨Nat.pos_of_ne_zero hm0,(Nat.le_mul_of_pos_left m hu).trans hhi⟩,hlo,hhi,hP⟩

theorem mem_dyadicPairs (y Q j : ℕ) (P : Leaf → ℕ → Prop) (l : Leaf) (m : ℕ) :
    (l,m) ∈ dyadicPairs y Q j P ↔
      (l ∈ stoppedLeaves y ∧ 2^j ≤ l.chosen.prod ∧ l.chosen.prod < 2^(j+1)) ∧
      (Q/(4*2^j) < m ∧ m ≤ Q/2^j) ∧
        Q/2 < l.chosen.prod*m ∧ l.chosen.prod*m ≤ Q ∧ P l m := by
  classical
  simp only [dyadicPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, and_assoc]

/-- Exact finite dyadic cover, preserving every original predicate. -/
theorem originalPairs_eq_biUnion (y Q : ℕ) (hy : 1 ≤ y) (P : Leaf → ℕ → Prop) :
    originalPairs y Q P =
      (Finset.range (Nat.log2 (y^2)+1)).biUnion (fun j => dyadicPairs y Q j P) := by
  classical
  ext ⟨l,m⟩
  rw [mem_originalPairs, Finset.mem_biUnion]
  constructor
  · rintro ⟨hl,hm,hlo,hhi,hP⟩
    obtain ⟨hll,hs⟩ := (mem_stoppedLeaves y l).mp hl
    obtain ⟨j,hj,hulo,huhi⟩ := stopped_leaf_dyadic y hy l hll hs
    refine ⟨j,hj,(mem_dyadicPairs y Q j P l m).mpr ⟨⟨hl,hulo,huhi⟩,?_,hlo,hhi,hP⟩⟩
    exact Finset.mem_Ioc.mp (dyadic_rectangle_membership Q (2^j) l.chosen.prod m
      (by positivity) hulo (by simpa only [pow_succ, Nat.mul_comm] using huhi) hlo hhi)
  · rintro ⟨j,hj,hmem⟩
    obtain ⟨⟨hl,hulo,huhi⟩,hm,hlo,hhi,hP⟩ := (mem_dyadicPairs y Q j P l m).mp hmem
    exact ⟨hl,⟨Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt hm.1),
      hm.2.trans (Nat.div_le_self _ _)⟩,hlo,hhi,hP⟩

/-- A pair cannot lie in two different dyadic rectangles. -/
theorem dyadicPairs_disjoint (y Q i j : ℕ) (P : Leaf → ℕ → Prop) (hij : i ≠ j) :
    Disjoint (dyadicPairs y Q i P) (dyadicPairs y Q j P) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨l,m⟩ hi hj
  have hi' := (mem_dyadicPairs y Q i P l m).mp hi
  have hj' := (mem_dyadicPairs y Q j P l m).mp hj
  have hu : l.chosen.prod ≠ 0 := by
    have : 0 < 2^i := by positivity
    omega
  have hei := (Nat.log2_eq_iff hu).mpr hi'.1.2
  have hej := (Nat.log2_eq_iff hu).mpr hj'.1.2
  exact hij (hei.symm.trans hej)

/-- The finite cover is disjoint, so arbitrary complex sums (including
signed sieve weights) split exactly, with no positivity assumption. -/
theorem sum_originalPairs_eq_dyadic (y Q : ℕ) (hy : 1 ≤ y) (P : Leaf → ℕ → Prop)
    (W : Leaf × ℕ → ℂ) :
    (∑ x ∈ originalPairs y Q P, W x) =
      ∑ j ∈ Finset.range (Nat.log2 (y^2)+1), ∑ x ∈ dyadicPairs y Q j P, W x := by
  classical
  rw [originalPairs_eq_biUnion y Q hy P, Finset.sum_biUnion]
  intro i hi j hj hij
  exact dyadicPairs_disjoint y Q i j P hij

end Erdos387Proof.SeparatedProductWindow
