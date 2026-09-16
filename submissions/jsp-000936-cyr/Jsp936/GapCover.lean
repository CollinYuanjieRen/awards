import Jsp936.Bounds
import Jsp936.TailBounds

/-! Covering the interval between extreme nodes by its consecutive closed gaps. -/
namespace Jsp936
open Randy1153 Set
noncomputable section

/-- Every point between the extreme ordered nodes belongs to a consecutive closed gap. -/
theorem exists_mem_closedGap {d : ℕ} (nodes : OrderedNodes (d + 2)) {t : ℝ}
    (hlo : nodes.point 0 ≤ t) (hhi : t ≤ nodes.point (Fin.last (d + 1))) :
    ∃ g : Fin (d + 1), t ∈ closedGap nodes g := by
  have hcover (i : Fin (d + 2)) (hi : t ≤ nodes.point i) :
      ∃ g : Fin (d + 1), t ∈ closedGap nodes g := by
    induction i using Fin.induction with
    | zero =>
        refine ⟨0, ?_⟩
        simp only [closedGap, mem_Icc, gapLeftIndex, gapRightIndex]
        exact ⟨hlo, hi.trans (nodes.strictMono.monotone (by simp))⟩
    | succ i ih =>
        by_cases hprev : t ≤ nodes.point i.castSucc
        · exact ih hprev
        · refine ⟨i, ?_⟩
          simp only [closedGap, mem_Icc, gapLeftIndex, gapRightIndex]
          exact ⟨le_of_not_ge hprev, hi⟩
  exact hcover (Fin.last (d + 1)) hhi

/-- A gap maximum is at most the maximum on the whole interpolation interval. -/
theorem gapHeight_le_lebesgueOn {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) :
    gapHeight nodes g ≤ lebesgueOn nodes.toNodeFamily (-1) 1 := by
  apply lebesgueOn_mono nodes.toNodeFamily
  · exact (gap_left_lt_right nodes g).le
  · norm_num
  · exact nodes.neg_one_le (gapLeftIndex g)
  · exact nodes.le_one (gapRightIndex g)

/-- Gap bounds together with the two endpoint bounds control the whole interval maximum. -/
theorem lebesgueOn_le_of_gapHeight_le {d : ℕ} (nodes : OrderedNodes (d + 2)) (C : ℝ)
    (hgaps : ∀ g : Fin (d + 1), gapHeight nodes g ≤ C)
    (hleft : lebesgueFunction nodes.toNodeFamily (-1) ≤ C)
    (hright : lebesgueFunction nodes.toNodeFamily 1 ≤ C) :
    lebesgueOn nodes.toNodeFamily (-1) 1 ≤ C := by
  apply (lebesgueOn_le_iff nodes.toNodeFamily (-1) 1 C (by norm_num)).2
  intro t ht
  by_cases hleftTail : t ≤ nodes.point 0
  · exact (lebesgueFunction_le_left_endpoint nodes.toNodeFamily t ht.1 fun i ↦
      hleftTail.trans (nodes.strictMono.monotone (Fin.zero_le i))).trans hleft
  by_cases hrightTail : nodes.point (Fin.last (d + 1)) ≤ t
  · exact (lebesgueFunction_le_right_endpoint nodes.toNodeFamily t ht.2 fun i ↦
      (nodes.strictMono.monotone (Fin.le_last i)).trans hrightTail).trans hright
  obtain ⟨g, htg⟩ := exists_mem_closedGap nodes
    (le_of_not_ge hleftTail) (le_of_not_ge hrightTail)
  exact (lebesgueFunction_le_on nodes.toNodeFamily (gap_left_lt_right nodes g).le htg).trans
    (hgaps g)

end
end Jsp936
