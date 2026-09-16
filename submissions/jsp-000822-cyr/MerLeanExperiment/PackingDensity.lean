import MerLeanExperiment.BoxGeometry

open Set

namespace DiskDiscrepancy

noncomputable section

private def packingCenter (R : ℝ) (q : Fin n × Fin n) : Plane :=
  WithLp.toLp 2 (fun k ↦ if k = 0 then 3 * R * (q.1.val + 1) else 3 * R * (q.2.val + 1))

private theorem packingCenter_mem {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n)
    (q : Fin n × Fin n) : packingCenter R q ∈ coordinateBox (4 * R * n - R) := by
  intro k
  fin_cases k
  · simp [packingCenter, abs_of_pos hR]
    rw [abs_of_nonneg (by positivity)]
    have hq : (q.1.val : ℝ) + 1 ≤ n := by exact_mod_cast q.1.isLt
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 3 * R)
    have hnR := mul_le_mul_of_nonneg_left hn' hR.le
    nlinarith
  · simp [packingCenter, abs_of_pos hR]
    rw [abs_of_nonneg (by positivity)]
    have hq : (q.2.val : ℝ) + 1 ≤ n := by exact_mod_cast q.2.isLt
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 3 * R)
    have hnR := mul_le_mul_of_nonneg_left hn' hR.le
    nlinarith

private theorem packingCenter_separated {R : ℝ} (hR : 0 < R) {n : ℕ}
    {q q' : Fin n × Fin n} (hne : q ≠ q') : 2 * R < dist (packingCenter R q) (packingCenter R q') := by
  have hor : q.1 ≠ q'.1 ∨ q.2 ≠ q'.2 := by
    contrapose! hne
    exact Prod.ext hne.1 hne.2
  rcases hor with hfirst | hsecond
  · have hval : q.1.val ≠ q'.1.val := fun h ↦ hfirst (Fin.ext h)
    have hcoord := PiLp.dist_apply_le (packingCenter R q) (packingCenter R q') (0 : Fin 2)
    simp [packingCenter] at hcoord
    rw [Real.dist_eq] at hcoord
    have habs : 3 * R ≤ |3 * R * (q.1.val + 1) - 3 * R * (q'.1.val + 1)| := by
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hg : q.1.val + 1 ≤ q'.1.val := by omega
        have hgR : (q.1.val : ℝ) + 1 ≤ (q'.1.val : ℝ) := by exact_mod_cast hg
        have hgap : (1 : ℝ) ≤ (q'.1.val : ℝ) - (q.1.val : ℝ) := by linarith
        rw [abs_of_nonpos (by nlinarith)]
        have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 3 * R)
        nlinarith
      · have hg : q'.1.val + 1 ≤ q.1.val := by omega
        have hgR : (q'.1.val : ℝ) + 1 ≤ (q.1.val : ℝ) := by exact_mod_cast hg
        have hgap : (1 : ℝ) ≤ (q.1.val : ℝ) - (q'.1.val : ℝ) := by linarith
        rw [abs_of_nonneg (by nlinarith)]
        have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 3 * R)
        nlinarith
    change dist (packingCenter R q) (packingCenter R q') ≥ _ at hcoord
    linarith
  · have hval : q.2.val ≠ q'.2.val := fun h ↦ hsecond (Fin.ext h)
    have hcoord := PiLp.dist_apply_le (packingCenter R q) (packingCenter R q') (1 : Fin 2)
    simp [packingCenter] at hcoord
    rw [Real.dist_eq] at hcoord
    have habs : 3 * R ≤ |3 * R * (q.2.val + 1) - 3 * R * (q'.2.val + 1)| := by
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hg : q.2.val + 1 ≤ q'.2.val := by omega
        have hgR : (q.2.val : ℝ) + 1 ≤ (q'.2.val : ℝ) := by exact_mod_cast hg
        have hgap : (1 : ℝ) ≤ (q'.2.val : ℝ) - (q.2.val : ℝ) := by linarith
        rw [abs_of_nonpos (by nlinarith)]
        have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 3 * R)
        nlinarith
      · have hg : q'.2.val + 1 ≤ q.2.val := by omega
        have hgR : (q'.2.val : ℝ) + 1 ≤ (q.2.val : ℝ) := by exact_mod_cast hg
        have hgap : (1 : ℝ) ≤ (q.2.val : ℝ) - (q'.2.val : ℝ) := by linarith
        rw [abs_of_nonneg (by nlinarith)]
        have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 3 * R)
        nlinarith
    change dist (packingCenter R q) (packingCenter R q') ≥ _ at hcoord
    linarith

/-- A uniform lower disk count forces a quadratic number of points in the
actual finite coordinate-box cutoff. -/
theorem cutoffPoints_card_lower_of_disk_counts {S : Set Plane} (hS : Admissible S)
    {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n)
    (hcount : ∀ center : Plane, R ^ 2 ≤ (pointCount S center R : ℝ)) :
    (4 * R * n) ^ 2 / 16 ≤ ((cutoffPoints S hS (4 * R * n)).card : ℝ) := by
  classical
  let grid : Finset (Fin n × Fin n) := Finset.univ ×ˢ Finset.univ
  let disks : Fin n × Fin n → Finset Plane := fun q ↦ (hS.2 (packingCenter R q) R).toFinset
  let packed : Finset Plane := grid.biUnion disks
  have hdisj : (↑grid : Set (Fin n × Fin n)).PairwiseDisjoint disks := by
    intro q hq q' hq' hne
    change Disjoint (disks q) (disks q')
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hxq : dist x (packingCenter R q) ≤ R :=
      (by simpa [disks, diskPoints] using hx : x ∈ S ∧ dist x (packingCenter R q) ≤ R).2
    have hxq' : dist x (packingCenter R q') ≤ R :=
      (by simpa [disks, diskPoints] using hx' : x ∈ S ∧ dist x (packingCenter R q') ≤ R).2
    have hsep := packingCenter_separated hR hne
    have htri := dist_triangle (packingCenter R q) x (packingCenter R q')
    rw [dist_comm (packingCenter R q) x] at htri
    linarith
  have hpacked_card : packed.card = ∑ q ∈ grid, (disks q).card := by
    exact Finset.card_biUnion hdisj
  have hdisk_card (q : Fin n × Fin n) : R ^ 2 ≤ ((disks q).card : ℝ) := by
    have hc := hcount (packingCenter R q)
    rw [pointCount, Set.ncard_eq_toFinset_card _ (hS.2 (packingCenter R q) R)] at hc
    simpa [disks] using hc
  have hsum : (n : ℝ) ^ 2 * R ^ 2 ≤ (packed.card : ℝ) := by
    rw [hpacked_card, Nat.cast_sum]
    have hcard : grid.card = n ^ 2 := by simp [grid, pow_two]
    have hs := Finset.sum_le_sum (s := grid) (fun q _ ↦ hdisk_card q)
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    rw [hcard] at hs
    have heq : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by norm_num
    rw [heq] at hs
    exact hs
  have hsubset : packed ⊆ cutoffPoints S hS (4 * R * n) := by
    intro x hx
    simp only [packed, Finset.mem_biUnion] at hx
    obtain ⟨q, hq, hx⟩ := hx
    have hxset : x ∈ diskPoints S (packingCenter R q) R := by simpa [disks] using hx
    apply (mem_cutoffPoints S hS (4 * R * n) x).2
    refine ⟨hxset.1, ?_⟩
    exact disk_subset_coordinateBox (packingCenter_mem hR hn q) le_rfl hxset.2
  have hcardle := Finset.card_le_card hsubset
  have heq : (4 * R * (n : ℝ)) ^ 2 / 16 = (n : ℝ) ^ 2 * R ^ 2 := by ring
  rw [heq]
  exact hsum.trans (by exact_mod_cast hcardle)

end

end DiskDiscrepancy
