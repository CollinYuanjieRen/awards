import Jsp937.Bounds
import Jsp937.TailBounds

/-! The augmented-gap objective in terms of its internal and exterior components. -/
namespace Jsp937
open Randy1153
noncomputable section

@[simp]
private theorem augmentedNodes_zero_castSucc {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    augmentedNodes nodes (0 : Fin (n + 2)).castSucc = -1 := by
  rfl

@[simp]
private theorem augmentedNodes_zero_succ {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    augmentedNodes nodes (0 : Fin (n + 2)).succ = nodes.point 0 := by
  have hi : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := by ext; simp
  rw [hi, augmentedNodes, Fin.cases_succ, Fin.lastCases_castSucc]

@[simp]
private theorem augmentedNodes_penultimate {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    augmentedNodes nodes (Fin.last (n + 1)).castSucc = nodes.point (Fin.last n) := by
  have hi : (Fin.last (n + 1)).castSucc = ((Fin.last n).castSucc).succ := by ext; simp
  rw [hi, augmentedNodes, Fin.cases_succ, Fin.lastCases_castSucc]

@[simp]
private theorem augmentedNodes_last {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    augmentedNodes nodes (Fin.last (n + 1)).succ = 1 := by
  rw [augmentedNodes, Fin.cases_succ, Fin.lastCases_last]

@[simp]
private theorem augmentedNodes_internal_left {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) :
    augmentedNodes nodes i.castSucc.succ.castSucc = nodes.point (gapLeftIndex i) := by
  have hi : i.castSucc.succ.castSucc = i.castSucc.castSucc.succ := by ext; simp
  rw [hi, augmentedNodes, Fin.cases_succ, Fin.lastCases_castSucc]
  congr 1

@[simp]
private theorem augmentedNodes_internal_right {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) :
    augmentedNodes nodes i.castSucc.succ.succ = nodes.point (gapRightIndex i) := by
  have hi : i.castSucc.succ.succ = i.succ.castSucc.succ := by ext; simp
  rw [hi, augmentedNodes, Fin.cases_succ, Fin.lastCases_castSucc]
  congr 1

/-- The first augmented local peak is the left endpoint value. -/
theorem localPeak_zero_eq_left {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    localPeak nodes 0 = lebesgueFunction nodes.toNodeFamily (-1) := by
  have hleft : (-1 : ℝ) ≤ nodes.point 0 := nodes.neg_one_le 0
  apply le_antisymm
  · rw [localPeak, augmentedNodes_zero_castSucc, augmentedNodes_zero_succ]
    exact (lebesgueOn_le_iff nodes.toNodeFamily (-1) (nodes.point 0)
      (lebesgueFunction nodes.toNodeFamily (-1)) hleft).mpr fun t ht ↦
        lebesgueFunction_le_left_endpoint nodes.toNodeFamily t ht.1 fun i ↦
          ht.2.trans (nodes.strictMono.monotone (Fin.zero_le i))
  · rw [localPeak, augmentedNodes_zero_castSucc, augmentedNodes_zero_succ]
    exact lebesgueFunction_le_on nodes.toNodeFamily hleft ⟨le_rfl, hleft⟩

/-- The last augmented local peak is the right endpoint value. -/
theorem localPeak_last_eq_right {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    localPeak nodes (Fin.last (n + 1)) = lebesgueFunction nodes.toNodeFamily 1 := by
  have hright : nodes.point (Fin.last n) ≤ (1 : ℝ) := nodes.le_one (Fin.last n)
  apply le_antisymm
  · rw [localPeak, augmentedNodes_penultimate, augmentedNodes_last]
    exact (lebesgueOn_le_iff nodes.toNodeFamily (nodes.point (Fin.last n)) 1
      (lebesgueFunction nodes.toNodeFamily 1) hright).mpr fun t ht ↦
        lebesgueFunction_le_right_endpoint nodes.toNodeFamily t ht.2 fun i ↦
          (nodes.strictMono.monotone (Fin.le_last i)).trans ht.1
  · rw [localPeak, augmentedNodes_penultimate, augmentedNodes_last]
    exact lebesgueFunction_le_on nodes.toNodeFamily hright ⟨hright, le_rfl⟩

/-- Every internal augmented local peak is the corresponding nodal gap height. -/
theorem localPeak_succ_eq_gapHeight {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) :
    localPeak nodes i.castSucc.succ = gapHeight nodes i := by
  rw [localPeak, gapHeight, augmentedNodes_internal_left, augmentedNodes_internal_right]

/-- The augmented objective is at most every internal gap height. -/
theorem upsilon_le_gapHeight {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) :
    upsilon nodes ≤ gapHeight nodes i := by
  rw [← localPeak_succ_eq_gapHeight nodes i, upsilon]
  exact Finset.inf'_le _ (Finset.mem_univ i.castSucc.succ)

/-- The augmented objective is at most the left endpoint value. -/
theorem upsilon_le_left {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    upsilon nodes ≤ lebesgueFunction nodes.toNodeFamily (-1) := by
  rw [← localPeak_zero_eq_left nodes, upsilon]
  exact Finset.inf'_le (s := Finset.univ) (f := localPeak nodes) (Finset.mem_univ 0)

/-- The augmented objective is at most the right endpoint value. -/
theorem upsilon_le_right {n : ℕ} (nodes : OrderedNodes (n + 1)) :
    upsilon nodes ≤ lebesgueFunction nodes.toNodeFamily 1 := by
  rw [← localPeak_last_eq_right nodes, upsilon]
  exact Finset.inf'_le (s := Finset.univ) (f := localPeak nodes)
    (Finset.mem_univ (Fin.last (n + 1)))

/-- A number bounds the augmented objective from below exactly when it bounds every internal
height and both endpoint values from below. -/
theorem le_upsilon_iff {d : ℕ} (nodes : OrderedNodes (d + 2)) (H : ℝ) :
    H ≤ upsilon nodes ↔
      (∀ i : Fin (d + 1), H ≤ gapHeight nodes i) ∧
        H ≤ lebesgueFunction nodes.toNodeFamily (-1) ∧
        H ≤ lebesgueFunction nodes.toNodeFamily 1 := by
  constructor
  · intro h
    exact ⟨fun i ↦ h.trans (upsilon_le_gapHeight nodes i),
      h.trans (upsilon_le_left nodes), h.trans (upsilon_le_right nodes)⟩
  · rintro ⟨hgap, hleft, hright⟩
    rw [upsilon]
    apply Finset.le_inf'
    intro i _
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [localPeak_zero_eq_left] using hleft
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · have hi : (Fin.last (d + 1)).succ = Fin.last (d + 2) := by ext; simp
        rw [hi, localPeak_last_eq_right]
        exact hright
      · simpa only [localPeak_succ_eq_gapHeight] using hgap k

end
end Jsp937
