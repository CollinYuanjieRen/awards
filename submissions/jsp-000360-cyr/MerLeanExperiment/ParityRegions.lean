import MerLeanExperiment.ParityRegionDefinitions
import MerLeanExperiment.CellCover
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

/-- Splitting a half-open parity region at an intermediate endpoint. -/
theorem parity_region_split (A : Finset ℕ) (a b c R : ℝ) (r : ℤ)
    (hab : a ≤ b) (hbc : b ≤ c) (hR : 0 ≤ R) :
    parityRegion A a c R r =
      parityRegion A a b R r ∪ parityRegion A b c R r := by
  ext n
  simp only [parityRegion, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hnA, han, hnc, hnpar⟩
    by_cases hnb : (n : ℝ) ≤ b * R
    · exact Or.inl ⟨hnA, han, hnb, hnpar⟩
    · exact Or.inr ⟨hnA, lt_of_not_ge hnb, hnc, hnpar⟩
  · rintro (hn | hn)
    · exact ⟨hn.1, hn.2.1, hn.2.2.1.trans
        (mul_le_mul_of_nonneg_right hbc hR), hn.2.2.2⟩
    · exact ⟨hn.1, (mul_le_mul_of_nonneg_right hab hR).trans_lt hn.2.1,
        hn.2.2.1, hn.2.2.2⟩

/-- Regions whose underlying real intervals are ordered and disjoint are
disjoint, independently of their parity labels. -/
theorem parity_regions_disjoint (A : Finset ℕ) (a b c d R : ℝ) (r s : ℤ)
    (hbc : b ≤ c) (hR : 0 ≤ R) :
    Disjoint (parityRegion A a b R r) (parityRegion A c d R s) := by
  rw [Finset.disjoint_left]
  intro n hn₁ hn₂
  simp only [parityRegion, Finset.mem_filter] at hn₁ hn₂
  have hscaled : b * R ≤ c * R := mul_le_mul_of_nonneg_right hbc hR
  linarith [hn₁.2.2.1, hn₂.2.1]

/-- The actual parity-filtered natural-number region has at most the usual
integer interval count. -/
theorem parity_region_card_le (A : Finset ℕ) (a b R : ℝ) (r : ℤ)
    (hab : a ≤ b) (hR : 0 ≤ R) :
    ((parityRegion A a b R r).card : ℝ) ≤ (b - a) * R + 1 := by
  let S : Finset ℤ := (parityRegion A a b R r).image (fun n : ℕ ↦ (n : ℤ))
  have hcardS : S.card = (parityRegion A a b R r).card := by
    dsimp [S]
    exact Finset.card_image_of_injective _ (fun x y hxy ↦ by exact_mod_cast hxy)
  have hsub : S ⊆ realIntIoc (a * R) (b * R) := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hnr := (Finset.mem_filter.mp hn).2
    exact (mem_realIntIoc _ _ _).mpr ⟨hnr.1, hnr.2.1⟩
  have hcardN : S.card ≤ (realIntIoc (a * R) (b * R)).card :=
    Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ ((realIntIoc (a * R) (b * R)).card : ℝ) := by
    exact_mod_cast hcardN
  have habR : a * R ≤ b * R := mul_le_mul_of_nonneg_right hab hR
  have hinterval := card_realIntIoc_le (a * R) (b * R) habR
  rw [hcardS] at hcardR
  calc
    ((parityRegion A a b R r).card : ℝ) ≤
        ((realIntIoc (a * R) (b * R)).card : ℝ) := hcardR
    _ ≤ b * R - a * R + 1 := hinterval
    _ = (b - a) * R + 1 := by ring

/-- A finite union of consecutive actual cells is exactly the longer parity
region with the same left endpoint. -/
theorem consecutive_cells_union (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 ≤ delta) (hR : 0 ≤ R) :
    (Finset.range m).biUnion (consecutiveCell A a delta R r) =
      parityRegion A a (a + m * delta) R r := by
  induction m with
  | zero =>
      simp only [Finset.range_zero, Finset.biUnion_empty]
      ext n
      simp only [Finset.notMem_empty, parityRegion, Finset.mem_filter, false_iff]
      rintro ⟨_, hnlo, hnhi, _⟩
      norm_num at hnhi
      linarith
  | succ m ih =>
      have hm : (0 : ℝ) ≤ m := by positivity
      have ham : a ≤ a + (m : ℝ) * delta := by
        nlinarith [mul_nonneg hm hd]
      have hmm : a + (m : ℝ) * delta ≤ a + ((m : ℝ) + 1) * delta := by
        nlinarith
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      rw [show consecutiveCell A a delta R r m =
          parityRegion A (a + (m : ℝ) * delta)
            (a + ((m : ℝ) + 1) * delta) R r by
        simp [consecutiveCell]]
      rw [show (↑(m + 1) : ℝ) = (m : ℝ) + 1 by norm_num]
      rw [Finset.union_comm]
      exact (parity_region_split A a (a + (m : ℝ) * delta)
        (a + ((m : ℝ) + 1) * delta) R r ham hmm hR).symm

/-- Consecutive actual cells are pairwise disjoint, so their cardinalities
sum to the cardinality of their union. -/
theorem consecutive_cells_card (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 ≤ delta) (hR : 0 ≤ R) :
    (∑ s ∈ Finset.range m, (consecutiveCell A a delta R r s).card) =
      (parityRegion A a (a + m * delta) R r).card := by
  have hpw : ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (consecutiveCell A a delta R r) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply parity_regions_disjoint
      · have hs : ((i : ℝ) + 1) * delta ≤ (j : ℝ) * delta := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show i + 1 ≤ j by omega)) hd
        linarith
      · exact hR
    · exact (parity_regions_disjoint A
        (a + (j : ℝ) * delta) (a + ((j : ℝ) + 1) * delta)
        (a + (i : ℝ) * delta) (a + ((i : ℝ) + 1) * delta) R r r
        (by
          have hs : ((j : ℝ) + 1) * delta ≤ (i : ℝ) * delta := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (show j + 1 ≤ i by omega)) hd
          linarith) hR).symm
  rw [← consecutive_cells_union A a delta R r m hd hR]
  symm
  rw [Finset.card_biUnion hpw]

/-- The uncovered tail after the consecutive mesh costs at most one interval
length plus the unavoidable integer endpoint error. -/
theorem parity_region_le_cells_add (A : Finset ℕ) (a b delta R : ℝ) (r : ℤ)
    (m : ℕ) (hd : 0 < delta) (hR : 0 < R)
    (hlo : (m : ℝ) * delta ≤ b - a)
    (hhi : b - a < ((m : ℝ) + 1) * delta) :
    ((parityRegion A a b R r).card : ℝ) ≤
      (∑ s ∈ Finset.range m,
        ((consecutiveCell A a delta R r s).card : ℝ)) + delta * R + 1 := by
  let c : ℝ := a + (m : ℝ) * delta
  have hm : (0 : ℝ) ≤ m := by positivity
  have hac : a ≤ c := by
    dsimp [c]
    nlinarith [mul_nonneg hm hd.le]
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hsplit := parity_region_split A a c b R r hac hcb hR.le
  have hdis := parity_regions_disjoint A a c c b R r r le_rfl hR.le
  have hcardN : (parityRegion A a b R r).card =
      (parityRegion A a c R r).card + (parityRegion A c b R r).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdis]
  have htail := parity_region_card_le A c b R r hcb hR.le
  have hlen : b - c < delta := by
    dsimp [c]
    nlinarith
  have htail' : ((parityRegion A c b R r).card : ℝ) ≤ delta * R + 1 := by
    calc
      ((parityRegion A c b R r).card : ℝ) ≤ (b - c) * R + 1 := htail
      _ ≤ delta * R + 1 := by nlinarith
  have hcovered := consecutive_cells_card A a delta R r m hd.le hR.le
  have hcoveredR : ((parityRegion A a c R r).card : ℝ) =
      ∑ s ∈ Finset.range m,
        ((consecutiveCell A a delta R r s).card : ℝ) := by
    rw [show c = a + (m : ℝ) * delta by rfl]
    exact_mod_cast hcovered.symm
  rw [hcardN, Nat.cast_add, hcoveredR]
  linarith

end Erdos441
