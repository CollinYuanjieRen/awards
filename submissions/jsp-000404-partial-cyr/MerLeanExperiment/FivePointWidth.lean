import MerLeanExperiment.DirectionalData
import Mathlib.Tactic

/-!
The primitive ordered-direction constraints on five ordered vertices already
force width at least `5 / 2`. The finite orientation split below is checked
entirely by Lean's linear arithmetic procedure.
-/

namespace OrderedDirections

private theorem triple_orientation {V : Type*} [LinearOrder V] {width : ℝ}
    (D : Data V width) {i j k : V} (hij : i < j) (hjk : j < k) :
    (D.value i j ≤ D.value i k ∧ D.value i k ≤ D.value j k ∧
      1 ≤ D.value j k - D.value i j ∧
      D.value i k - D.value i j ≤ width - 1 ∧
      D.value j k - D.value i k ≤ width - 1) ∨
    (D.value j k ≤ D.value i k ∧ D.value i k ≤ D.value i j ∧
      1 ≤ D.value i j - D.value j k ∧
      D.value i j - D.value i k ≤ width - 1 ∧
      D.value i k - D.value j k ≤ width - 1) := by
  rcases D.between hij hjk with hforward | hreverse
  · left
    have hsep := D.separated hij hjk
    have hfirst := D.first_gap hij hjk
    have hlast := D.last_gap hij hjk
    rw [abs_of_nonpos (sub_nonpos.2 (hforward.1.trans hforward.2))] at hsep
    rw [abs_of_nonpos (sub_nonpos.2 hforward.1)] at hfirst
    rw [abs_of_nonpos (sub_nonpos.2 hforward.2)] at hlast
    exact ⟨hforward.1, hforward.2, by linarith, by linarith, by linarith⟩
  · right
    have hsep := D.separated hij hjk
    have hfirst := D.first_gap hij hjk
    have hlast := D.last_gap hij hjk
    rw [abs_of_nonneg (sub_nonneg.2 (hreverse.1.trans hreverse.2))] at hsep
    rw [abs_of_nonneg (sub_nonneg.2 hreverse.2)] at hfirst
    rw [abs_of_nonneg (sub_nonneg.2 hreverse.1)] at hlast
    exact ⟨hreverse.1, hreverse.2, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 2000000 in
/-- Five strictly ordered vertices force direction width at least `5 / 2`. -/
theorem fivePoint_width {V : Type*} [LinearOrder V] {width : ℝ}
    (D : Data V width) {v0 v1 v2 v3 v4 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) :
    (5 : ℝ) / 2 ≤ width := by
  have h02 : v0 < v2 := h01.trans h12
  have h03 : v0 < v3 := h02.trans h23
  have h04 : v0 < v4 := h03.trans h34
  have h13 : v1 < v3 := h12.trans h23
  have h14 : v1 < v4 := h13.trans h34
  have h24 : v2 < v4 := h23.trans h34
  have t012 := triple_orientation D h01 h12
  have t013 := triple_orientation D h01 h13
  have t014 := triple_orientation D h01 h14
  have t023 := triple_orientation D h02 h23
  have t024 := triple_orientation D h02 h24
  have t034 := triple_orientation D h03 h34
  have t123 := triple_orientation D h12 h23
  have t124 := triple_orientation D h12 h24
  have t134 := triple_orientation D h13 h34
  have t234 := triple_orientation D h23 h34
  rcases t012 with t012 | t012 <;>
    rcases t013 with t013 | t013 <;>
    rcases t014 with t014 | t014 <;>
    rcases t023 with t023 | t023 <;>
    rcases t024 with t024 | t024 <;>
    rcases t034 with t034 | t034 <;>
    rcases t123 with t123 | t123 <;>
    rcases t124 with t124 | t124 <;>
    rcases t134 with t134 | t134 <;>
    rcases t234 with t234 | t234 <;> linarith

#print axioms fivePoint_width

end OrderedDirections
