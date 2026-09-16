import MerLeanExperiment.PeriodicGrid
import MerLeanExperiment.GridCells

namespace DiskDiscrepancy

def MeetingCell (center : Plane) (radius : ℝ) (z : ℤ × ℤ) : Prop :=
  (unitCell z ∩ Metric.closedBall center radius).Nonempty

theorem periodicGridPoint_mem_unitCell (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (ω : (Fin L × Fin L) → (Fin q × Fin q)) (z : ℤ × ℤ) :
    periodicGridPoint L q hL hq ω z ∈ unitCell z := by
  have h0 := midpointOffset_mem_Ico L q hL hq ω z 0
  have h1 := midpointOffset_mem_Ico L q hL hq ω z 1
  simp only [mem_unitCell, periodicGridPoint, jitterPoint_apply_zero, jitterPoint_apply_one]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem meetingCell_coordinate_gap {center : Plane} {radius : ℝ} {z w : ℤ × ℤ}
    (hz : MeetingCell center radius z) (hw : MeetingCell center radius w) :
    |(z.1 : ℝ) - w.1| < 2 * radius + 1 ∧ |(z.2 : ℝ) - w.2| < 2 * radius + 1 := by
  obtain ⟨p, hp, hpd⟩ := hz
  obtain ⟨q, hq, hqd⟩ := hw
  have hd : dist p q ≤ 2 * radius := by
    have h := dist_triangle p center q
    have hp' : dist p center ≤ radius := hpd
    have hq' : dist q center ≤ radius := hqd
    rw [dist_comm center q] at h
    linarith
  have h0 : |p 0 - q 0| ≤ 2 * radius := by
    have h := (PiLp.dist_apply_le p q (0 : Fin 2)).trans hd
    simpa only [Real.dist_eq] using h
  have h1 : |p 1 - q 1| ≤ 2 * radius := by
    have h := (PiLp.dist_apply_le p q (1 : Fin 2)).trans hd
    simpa only [Real.dist_eq] using h
  rcases mem_unitCell.mp hp with ⟨hp0,hp0',hp1,hp1'⟩
  rcases mem_unitCell.mp hq with ⟨hq0,hq0',hq1,hq1'⟩
  constructor
  · exact abs_lt.mpr ⟨by linarith [(abs_le.mp h0).1], by linarith [(abs_le.mp h0).2]⟩
  · exact abs_lt.mpr ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩

theorem intResidue_injective_of_close {L : ℕ} (hL : 0 < L) {a b : ℤ}
    (heq : intResidue L hL a = intResidue L hL b)
    (hclose : |(a : ℝ) - b| < L) : a = b := by
  have hmod : a % (L : ℤ) = b % (L : ℤ) := by
    have h := congrArg Fin.val heq
    dsimp [intResidue] at h
    have hLa : 0 ≤ a % (L : ℤ) := Int.emod_nonneg a (by exact_mod_cast hL.ne')
    have hLb : 0 ≤ b % (L : ℤ) := Int.emod_nonneg b (by exact_mod_cast hL.ne')
    omega
  have hdvd : (L : ℤ) ∣ a - b :=
    Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have habs : |a - b| < (L : ℤ) := by exact_mod_cast hclose
  have hzero : |a - b| = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) habs
    (by simpa only [dvd_abs] using hdvd)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Cells meeting a disk use distinct product coordinates when the period exceeds its diameter plus one. -/
theorem residue_injective_on_meetingCells {L : ℕ} (hL : 0 < L)
    {center : Plane} {radius : ℝ} (hperiod : 2 * radius + 1 < L) :
    Set.InjOn (fun z : ℤ × ℤ ↦ (intResidue L hL z.1, intResidue L hL z.2))
      {z | MeetingCell center radius z} := by
  intro z hz w hw heq
  have hgap := meetingCell_coordinate_gap hz hw
  exact Prod.ext
    (intResidue_injective_of_close hL (congrArg Prod.fst heq) (hgap.1.trans hperiod))
    (intResidue_injective_of_close hL (congrArg Prod.snd heq) (hgap.2.trans hperiod))

end DiskDiscrepancy
