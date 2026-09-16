import Mathlib
import Jsp827.Tower.Basic
import Jsp827.Tower.Iterate
import Jsp827.Tower.Sup

/-!
# Rokhlin towers for commuting endomorphisms (Avila–Candela Theorem 1.2)

For a free measure-preserving `ℕ^d`-action on a probability space with a countable
separating family of measurable sets, every box `n` (all sides positive) admits an
`n`-tower of measure `≥ 1 − ε`: dyadic refinement `2^K n` and the sup argument of AC §2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Doubling all sides `K` times multiplies the cardinality of a box by `(2 ^ K) ^ d`. -/
lemma card_box_pow_mul {d : ℕ} (K : ℕ) (N : Fin d → ℕ) :
    (box fun i ↦ 2 ^ K * N i).card = (2 ^ K) ^ d * (box N).card := by
  simp [card_box, Finset.prod_mul_distrib]

/-- The index set `fun i ↦ (t i + 1) * N i + j i`, for `t` in the box of side `2 ^ K - 1`.
It indexes the levels of the sub-tower `D` in the proof of Theorem 1.2: all coordinates of
the `N`-scaled part are at least `1`, which leaves room to subtract an index `j < N`. -/
def shiftBox {d : ℕ} (K : ℕ) (N j : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ ↦ 2 ^ K - 1).image fun t i ↦ (t i + 1) * N i + j i

/-- The shifted index set sits inside the box of side `2 ^ K * N`. -/
lemma shiftBox_subset {d : ℕ} (K : ℕ) {N j : Fin d → ℕ} (hj : ∀ i, j i < N i) :
    shiftBox K N j ⊆ box fun i ↦ 2 ^ K * N i := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
  refine mem_box.2 fun i ↦ ?_
  have h1 : t i < 2 ^ K - 1 := mem_box.1 ht i
  have h3 : 1 ≤ 2 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have h4 : t i + 2 ≤ 2 ^ K := by omega
  calc (t i + 1) * N i + j i < (t i + 1) * N i + N i := Nat.add_lt_add_left (hj i) _
    _ = (t i + 2) * N i := by ring
    _ ≤ 2 ^ K * N i := Nat.mul_le_mul h4 le_rfl

/-- The shifted index set has `(2 ^ K - 1) ^ d` elements. -/
lemma card_shiftBox {d : ℕ} (K : ℕ) {N : Fin d → ℕ} (hN : ∀ i, 0 < N i) (j : Fin d → ℕ) :
    (shiftBox K N j).card = (2 ^ K - 1) ^ d := by
  have hinj : Set.InjOn (fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + j i)
      ↑(box fun _ : Fin d ↦ 2 ^ K - 1) := by
    intro t _ t' _ h
    funext i
    have hi : (t i + 1) * N i + j i = (t' i + 1) * N i + j i := congrFun h i
    have h2 : (t i + 1) * N i = (t' i + 1) * N i := by omega
    have := Nat.eq_of_mul_eq_mul_right (hN i) h2
    omega
  rw [shiftBox, Finset.card_image_of_injOn hinj, card_box]
  simp

/-- Shifted index sets attached to distinct offsets `j < N` are disjoint. -/
lemma disjoint_shiftBox {d : ℕ} (K : ℕ) {N j j' : Fin d → ℕ} (hj : ∀ i, j i < N i)
    (hj' : ∀ i, j' i < N i) (h : j ≠ j') :
    Disjoint (shiftBox K N j) (shiftBox K N j') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hu'
  refine h (funext fun i ↦ ?_)
  have hi : (t i + 1) * N i + j i = (t' i + 1) * N i + j' i := (congrFun ht' i).symm
  have hmod := congrArg (· % N i) hi
  simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (hj i), Nat.mod_eq_of_lt (hj' i)]
    using hmod

/-- Translating the basic shifted index set by `j` gives the shifted index set at `j`. -/
lemma image_add_shiftBox {d : ℕ} (K : ℕ) (N j : Fin d → ℕ) :
    (shiftBox K N 0).image (fun k ↦ k + j) = shiftBox K N j := by
  have h : ((fun k ↦ k + j) ∘ fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + (0 : Fin d → ℕ) i)
      = fun (t : Fin d → ℕ) i ↦ (t i + 1) * N i + j i := by
    funext t i
    simp
  rw [shiftBox, shiftBox, Finset.image_image, h]

/-- Every element of a shifted index set stays in the box of side `2 ^ K * N` after
subtracting an index `j < N`. -/
lemma exists_add_eq_of_mem_shiftBox {d : ℕ} (K : ℕ) {N j' j u : Fin d → ℕ}
    (hj' : ∀ i, j' i < N i) (hj : ∀ i, j i < N i) (hu : u ∈ shiftBox K N j') :
    ∃ m ∈ box fun i ↦ 2 ^ K * N i, m + j = u := by
  have hub : ∀ i, u i < 2 ^ K * N i := fun i ↦ mem_box.1 (shiftBox_subset K hj' hu) i
  have hlb : ∀ i, N i ≤ u i := by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    intro i
    show N i ≤ (t i + 1) * N i + j' i
    have h1 : 1 * N i ≤ (t i + 1) * N i := Nat.mul_le_mul (by omega) le_rfl
    omega
  refine ⟨fun i ↦ u i - j i, mem_box.2 fun i ↦ ?_, funext fun i ↦ ?_⟩
  · have h1 := hub i
    have h2 := hlb i
    have h3 := hj i
    omega
  · have h2 := hlb i
    have h3 := hj i
    simp only [Pi.add_apply]
    omega

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- The union of the levels of `B` indexed by a finite set of multi-indices. -/
def levels (s : Finset (Fin d → ℕ)) (B : Set X) : Set X :=
  ⋃ k ∈ s, A.f k ⁻¹' B

/-- A sub-union of levels of a measurable set is measurable. -/
lemma measurableSet_levels {s : Finset (Fin d → ℕ)} {B : Set X} (hB : MeasurableSet B) :
    MeasurableSet (A.levels s B) :=
  Finset.measurableSet_biUnion _ fun k _ ↦ A.measurable k hB

/-- The measure of a sub-union of the levels of an admissible tower. -/
lemma measure_levels {m : Fin d → ℕ} {B : Set X} (hB : A.Admissible m B)
    {s : Finset (Fin d → ℕ)} (hs : s ⊆ box m) : μ (A.levels s B) = s.card * μ B := by
  have hd : (↑s : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ A.f k ⁻¹' B :=
    fun k hk l hl hkl ↦ hB.2 k (hs (by simpa using hk)) l (hs (by simpa using hl)) hkl
  have hm : ∀ k ∈ s, MeasurableSet (A.f k ⁻¹' B) := fun k _ ↦ A.measurable k hB.1
  rw [levels, measure_biUnion_finset hd hm]
  simp only [A.measure_preimage _ hB.1, Finset.sum_const, nsmul_eq_mul]

/-- Sub-unions of levels over disjoint index sets are disjoint. -/
lemma disjoint_levels {m : Fin d → ℕ} {B : Set X} (hB : A.Admissible m B)
    {s t : Finset (Fin d → ℕ)} (hs : s ⊆ box m) (ht : t ⊆ box m) (hst : Disjoint s t) :
    Disjoint (A.levels s B) (A.levels t B) := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  simp only [levels, Set.mem_iUnion, Set.mem_preimage, exists_prop] at hx hx'
  obtain ⟨k, hk, hxk⟩ := hx
  obtain ⟨l, hl, hxl⟩ := hx'
  exact Set.disjoint_left.1
    (hB.2 k (hs hk) l (ht hl) fun h ↦ Finset.disjoint_left.1 hst hk (h ▸ hl)) hxk hxl

/-- Pulling a sub-union of levels back translates the index set. -/
lemma preimage_levels (j : Fin d → ℕ) (s : Finset (Fin d → ℕ)) (B : Set X) :
    A.f j ⁻¹' A.levels s B = A.levels (s.image fun k ↦ k + j) B := by
  simp only [levels, Set.preimage_iUnion, Finset.set_biUnion_finset_image,
    A.preimage_preimage]

/-- The union of two admissible sets whose levels do not meet is admissible. -/
lemma Admissible.union {n : Fin d → ℕ} {B C : Set X} (hB : A.Admissible n B)
    (hC : A.Admissible n C)
    (h : ∀ i ∈ box n, ∀ j ∈ box n, Disjoint (A.f i ⁻¹' C) (A.f j ⁻¹' B)) :
    A.Admissible n (B ∪ C) := by
  refine ⟨hB.1.union hC.1, fun k hk l hl hkl ↦ ?_⟩
  rw [Set.preimage_union, Set.preimage_union, Set.disjoint_union_left,
    Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hB.2 k hk l hl hkl, (h l hl k hk).symm⟩, ⟨h k hk l hl, hC.2 k hk l hl hkl⟩⟩

/-- The set of measures of `N`-towers. -/
def towerMeasures (N : Fin d → ℕ) : Set ℝ :=
  {r : ℝ | ∃ B : Set X, A.Admissible N B ∧ r = (μ (A.tower N B)).toReal}

/-- The empty base shows that `0` is a tower measure. -/
lemma zero_mem_towerMeasures (N : Fin d → ℕ) : (0 : ℝ) ∈ A.towerMeasures N :=
  ⟨∅, ⟨MeasurableSet.empty, fun k _ l _ _ ↦ by simp⟩, by simp [tower]⟩

/-- The set of tower measures is nonempty. -/
lemma towerMeasures_nonempty (N : Fin d → ℕ) : (A.towerMeasures N).Nonempty :=
  ⟨0, A.zero_mem_towerMeasures N⟩

/-- The set of tower measures is bounded above by `1`. -/
lemma towerMeasures_bddAbove [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    BddAbove (A.towerMeasures N) := by
  refine ⟨1, ?_⟩
  rintro r ⟨B, -, rfl⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The supremum of the tower measures is nonnegative. -/
lemma sSup_towerMeasures_nonneg [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    0 ≤ sSup (A.towerMeasures N) :=
  le_csSup (A.towerMeasures_bddAbove N) (A.zero_mem_towerMeasures N)

/-- The supremum of the tower measures is at most `1`. -/
lemma sSup_towerMeasures_le_one [IsProbabilityMeasure μ] (N : Fin d → ℕ) :
    sSup (A.towerMeasures N) ≤ 1 :=
  csSup_le (A.towerMeasures_nonempty N) <| by
    rintro r ⟨B, -, rfl⟩
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- **The key step of Theorem 1.2.**  Fix a box `N` with positive sides and a refinement
factor `2 ^ K`.  Out of any `2 ^ K * N`-admissible set `B₀` one builds an `N`-admissible set
whose tower keeps all but a `d * 2 ^ (-K)` fraction of the tower of `B₀` (the sub-union `D`,
indexed by `shiftBox`) and, by Lemma 2.4 applied in the complement, gains a further
`2 ^ (-d)` fraction of what is left over. -/
lemma sSup_towerMeasures_ge [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) {N : Fin d → ℕ}
    (hN : ∀ i, 0 < N i) (K : ℕ) {B₀ : Set X} (hB₀ : A.Admissible (fun i ↦ 2 ^ K * N i) B₀)
    {δ : ℝ} (hδ : 0 < δ) :
    (1 - (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal) / 2 ^ d - δ
        + (1 - d / 2 ^ K) * (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      ≤ sSup (A.towerMeasures N) := by
  classical
  have hz : ∀ i, (0 : Fin d → ℕ) i < N i := fun i ↦ hN i
  have hTmeas : MeasurableSet (A.tower (fun i ↦ 2 ^ K * N i) B₀) := A.measurableSet_tower hB₀.1
  obtain ⟨N', B₁, hB₁, hB₁sub, hB₁ge⟩ :=
    A.exists_admissible_tower_ge hfree N hN hTmeas.compl hδ
  set D : Set X := A.f N' ⁻¹' A.levels (shiftBox K N 0) B₀ with hD
  have hDmeas : MeasurableSet D := A.measurable N' (A.measurableSet_levels hB₀.1)
  have hlev : ∀ j : Fin d → ℕ, A.f j ⁻¹' D = A.f N' ⁻¹' A.levels (shiftBox K N j) B₀ := by
    intro j
    calc A.f j ⁻¹' D = A.f (N' + j) ⁻¹' A.levels (shiftBox K N 0) B₀ := by
          rw [hD, A.preimage_preimage]
      _ = A.f N' ⁻¹' (A.f j ⁻¹' A.levels (shiftBox K N 0) B₀) := by
          rw [A.preimage_preimage, add_comm]
      _ = A.f N' ⁻¹' A.levels (shiftBox K N j) B₀ := by
          rw [A.preimage_levels, image_add_shiftBox]
  have hDadm : A.Admissible N D := by
    refine ⟨hDmeas, fun k hk l hl hkl ↦ ?_⟩
    rw [hlev k, hlev l]
    exact Disjoint.preimage _ (A.disjoint_levels hB₀ (shiftBox_subset K (mem_box.1 hk))
      (shiftBox_subset K (mem_box.1 hl))
      (disjoint_shiftBox K (mem_box.1 hk) (mem_box.1 hl) hkl))
  have hcross : ∀ i ∈ box N, ∀ j ∈ box N, Disjoint (A.f i ⁻¹' D) (A.f j ⁻¹' B₁) := by
    intro i hi j hj
    rw [hlev i, Set.disjoint_left]
    intro z hz₁ hz₂
    simp only [Set.mem_preimage, levels, Set.mem_iUnion, exists_prop] at hz₁
    obtain ⟨u, hu, hzu⟩ := hz₁
    obtain ⟨m, hm, hmu⟩ := exists_add_eq_of_mem_shiftBox K (mem_box.1 hi) (mem_box.1 hj) hu
    have hnot : A.f N' (A.f j z) ∉ A.tower (fun i ↦ 2 ^ K * N i) B₀ := hB₁sub hz₂
    refine hnot (A.preimage_subset_tower hm B₀ ?_)
    show A.f m (A.f N' (A.f j z)) ∈ B₀
    have e : m + (N' + j) = u + N' := by
      rw [← hmu]
      abel
    have h1 : A.f m (A.f N' (A.f j z)) = A.f u (A.f N' z) :=
      calc A.f m (A.f N' (A.f j z)) = A.f (m + (N' + j)) z := by
            rw [A.f_apply_add, A.f_apply_add]
        _ = A.f (u + N') z := by rw [e]
        _ = A.f u (A.f N' z) := A.f_apply_add _ _ _
    rw [h1]
    exact hzu
  have hadm : A.Admissible N (B₁ ∪ D) := Admissible.union A hB₁ hDadm hcross
  have hdisjBD : Disjoint B₁ D := by
    have h0 : (0 : Fin d → ℕ) ∈ box N := mem_box.2 hz
    have h := hcross 0 h0 0 h0
    rw [A.f_zero] at h
    simpa using h.symm
  have hmeasD : μ D = (((2 ^ K - 1) ^ d : ℕ) : ℝ≥0∞) * μ B₀ := by
    rw [hD, A.measure_preimage _ (A.measurableSet_levels hB₀.1),
      A.measure_levels hB₀ (shiftBox_subset K hz), card_shiftBox K hN 0]
  have hTreal : (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      = ((2 : ℝ) ^ K) ^ d * (((box N).card : ℝ) * (μ B₀).toReal) := by
    rw [A.measure_tower hB₀, card_box_pow_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    push_cast
    ring
  have hone : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hTDreal : (μ (A.tower N D)).toReal
      = ((box N).card : ℝ) * (((2 : ℝ) ^ K - 1) ^ d * (μ B₀).toReal) := by
    rw [A.measure_tower hDadm, hmeasD, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    push_cast [Nat.cast_sub hone]
    ring
  have hber : 1 - (d : ℝ) / 2 ^ K ≤ (1 - 1 / 2 ^ K) ^ d := by
    have hx : (0 : ℝ) < 2 ^ K := by positivity
    have hle1 : (1 : ℝ) / 2 ^ K ≤ 1 := by
      rw [div_le_one hx]
      exact one_le_pow₀ (by norm_num)
    calc 1 - (d : ℝ) / 2 ^ K = 1 + (d : ℝ) * -(1 / 2 ^ K) := by ring
      _ ≤ (1 + -(1 / (2 : ℝ) ^ K)) ^ d := one_add_mul_le_pow (by linarith) d
      _ = (1 - 1 / 2 ^ K) ^ d := by ring_nf
  have hpow : (1 - (d : ℝ) / 2 ^ K) * ((2 : ℝ) ^ K) ^ d ≤ ((2 : ℝ) ^ K - 1) ^ d := by
    have hx : (0 : ℝ) < 2 ^ K := by positivity
    have h2 : ((2 : ℝ) ^ K - 1) ^ d = (1 - 1 / 2 ^ K) ^ d * ((2 : ℝ) ^ K) ^ d := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right hber (by positivity)
  have hDlow : (1 - (d : ℝ) / 2 ^ K) * (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal
      ≤ (μ (A.tower N D)).toReal := by
    rw [hTreal, hTDreal]
    have hPb : (0 : ℝ) ≤ ((box N).card : ℝ) * (μ B₀).toReal := by positivity
    calc (1 - (d : ℝ) / 2 ^ K) * (((2 : ℝ) ^ K) ^ d * (((box N).card : ℝ) * (μ B₀).toReal))
        = ((1 - (d : ℝ) / 2 ^ K) * ((2 : ℝ) ^ K) ^ d)
            * (((box N).card : ℝ) * (μ B₀).toReal) := by ring
      _ ≤ ((2 : ℝ) ^ K - 1) ^ d * (((box N).card : ℝ) * (μ B₀).toReal) :=
          mul_le_mul_of_nonneg_right hpow hPb
      _ = ((box N).card : ℝ) * (((2 : ℝ) ^ K - 1) ^ d * (μ B₀).toReal) := by ring
  have hcompl : (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)ᶜ).toReal
      = 1 - (μ (A.tower (fun i ↦ 2 ^ K * N i) B₀)).toReal := by
    rw [prob_compl_eq_one_sub hTmeas,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hsum : μ (A.tower N (B₁ ∪ D)) = μ (A.tower N B₁) + μ (A.tower N D) := by
    rw [A.measure_tower hadm, A.measure_tower hB₁, A.measure_tower hDadm,
      measure_union hdisjBD hDmeas, mul_add]
  have hle : (μ (A.tower N (B₁ ∪ D))).toReal ≤ sSup (A.towerMeasures N) :=
    le_csSup (A.towerMeasures_bddAbove N) ⟨B₁ ∪ D, hadm, rfl⟩
  rw [hsum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hle
  rw [hcompl] at hB₁ge
  linarith

/-- **AC Theorem 1.2.** -/
theorem exists_tower [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ)
    (hn : ∀ i, 0 < n i) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set X, A.Admissible n B ∧ 1 - ε ≤ (μ (A.tower n B)).toReal := by
  have hbdd : BddBelow (Set.range fun K : ℕ ↦ sSup (A.towerMeasures fun i ↦ 2 ^ K * n i)) :=
    ⟨0, by rintro _ ⟨K, rfl⟩; exact A.sSup_towerMeasures_nonneg _⟩
  set κ : ℝ := ⨅ K : ℕ, sSup (A.towerMeasures fun i ↦ 2 ^ K * n i) with hκdef
  have hκle : ∀ K : ℕ, κ ≤ sSup (A.towerMeasures fun i ↦ 2 ^ K * n i) :=
    fun K ↦ ciInf_le hbdd K
  have hκ0 : 0 ≤ κ := le_ciInf fun K ↦ A.sSup_towerMeasures_nonneg _
  have hκ1 : κ ≤ 1 := (hκle 0).trans (A.sSup_towerMeasures_le_one _)
  obtain ⟨v, hv0, hv1, hvd⟩ : ∃ v : ℝ, 0 < v ∧ v ≤ 1 ∧ ∀ x : ℝ, x / 2 ^ d = x * v := by
    refine ⟨((2 : ℝ) ^ d)⁻¹, by positivity, ?_, fun x ↦ by ring⟩
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hstep : ∀ δ : ℝ, 0 < δ → (1 - κ) * v ≤ 3 * δ := by
    intro δ hδ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (d : ℝ) / 2 ^ m ≤ δ := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((d : ℝ) / δ) (by norm_num : (1 : ℝ) < 2)
      refine ⟨m, ?_⟩
      rw [div_lt_iff₀ hδ] at hm
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)]
      linarith
    obtain ⟨θ, hθ0, hθδ, hθe⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ δ ∧ (d : ℝ) / 2 ^ m = θ :=
      ⟨_, by positivity, hm, rfl⟩
    have hkey : ∀ k : ℕ, (1 - κ) * v + κ - 3 * δ ≤
        sSup (A.towerMeasures fun i ↦ 2 ^ k * n i) := by
      intro k
      have hNpos : ∀ i, 0 < 2 ^ k * n i := fun i ↦
        Nat.mul_pos (pow_pos (by norm_num) k) (hn i)
      have hMeq : (fun i ↦ 2 ^ m * (2 ^ k * n i)) = fun i ↦ 2 ^ (m + k) * n i := by
        funext i
        rw [pow_add, mul_assoc]
      have hsSup : κ ≤ sSup (A.towerMeasures fun i ↦ 2 ^ m * (2 ^ k * n i)) := by
        rw [hMeq]
        exact hκle (m + k)
      obtain ⟨r, ⟨B₀, hB₀, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (A.towerMeasures_nonempty _)
        (show κ - δ < sSup (A.towerMeasures fun i ↦ 2 ^ m * (2 ^ k * n i)) by linarith)
      have hβ0 : (0 : ℝ) ≤ (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal :=
        ENNReal.toReal_nonneg
      have hβ1 : (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal ≤ 1 := by
        have h : μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀) ≤ 1 := prob_le_one
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top h
      have hkeylem := A.sSup_towerMeasures_ge hfree hNpos m hB₀ hδ
      rw [hvd, hθe] at hkeylem
      have h1 : (0 : ℝ) ≤ ((μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal - κ + δ)
          * (1 - v) := mul_nonneg (by linarith) (by linarith)
      have h2 : (0 : ℝ) ≤ (δ - θ)
          * (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal :=
        mul_nonneg (by linarith) hβ0
      have h3 : (0 : ℝ) ≤ δ * (1 - (μ (A.tower (fun i ↦ 2 ^ m * (2 ^ k * n i)) B₀)).toReal) :=
        mul_nonneg hδ.le (by linarith)
      have h4 : (0 : ℝ) ≤ δ * v := mul_nonneg hδ.le hv0.le
      linarith
    have hinf : (1 - κ) * v + κ - 3 * δ ≤ κ := le_ciInf hkey
    linarith
  have hκ : (1 : ℝ) ≤ κ := by
    rcases le_or_gt 1 κ with h | hcon
    · exact h
    · exfalso
      have hpos : 0 < (1 - κ) * v := mul_pos (by linarith) hv0
      have h := hstep ((1 - κ) * v / 6) (by linarith)
      linarith
  have hfinal : (1 : ℝ) ≤ sSup (A.towerMeasures n) := by
    have h := hκle 0
    simp only [pow_zero, one_mul] at h
    linarith
  obtain ⟨r, ⟨B, hB, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (A.towerMeasures_nonempty n)
    (show 1 - ε < sSup (A.towerMeasures n) by linarith)
  exact ⟨B, hB, hr.le⟩

end NatAction

end RokhlinTower
