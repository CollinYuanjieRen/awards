import MerLeanExperiment.FivePointWidth

/-!
Six ordered vertices force width at least three. The finite orientation proof
prunes inconsistent branches with kernel-checked linear arithmetic after every
split, rather than constructing the full orientation tree.
-/

namespace OrderedDirections

private theorem six_triple_orientation {V : Type*} [LinearOrder V] {width : ℝ}
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

set_option maxHeartbeats 4000000 in
/-- Six strictly ordered vertices force direction width at least three. -/
theorem sixPoint_width {V : Type*} [LinearOrder V] {width : ℝ}
    (D : Data V width) {v0 v1 v2 v3 v4 v5 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) : (3 : ℝ) ≤ width := by
  by_contra hn
  have hw5 : (5 : ℝ) / 2 ≤ width := fivePoint_width D h01 h12 h23 h34
  have hw3 : width < 3 := lt_of_not_ge hn
  have h02 := h01.trans h12
  have h03 := h02.trans h23
  have h04 := h03.trans h34
  have h05 := h04.trans h45
  have h13 := h12.trans h23
  have h14 := h13.trans h34
  have h15 := h14.trans h45
  have h24 := h23.trans h34
  have h25 := h24.trans h45
  have h35 := h34.trans h45
  have t012 := six_triple_orientation D h01 h12
  have t123 := six_triple_orientation D h12 h23
  have t234 := six_triple_orientation D h23 h34
  have t345 := six_triple_orientation D h34 h45
  have t023 := six_triple_orientation D h02 h23
  have t124 := six_triple_orientation D h12 h24
  have t235 := six_triple_orientation D h23 h35
  have t034 := six_triple_orientation D h03 h34
  have t125 := six_triple_orientation D h12 h25
  have t014 := six_triple_orientation D h01 h14
  have t145 := six_triple_orientation D h14 h45
  have t025 := six_triple_orientation D h02 h25
  have t035 := six_triple_orientation D h03 h35
  have t015 := six_triple_orientation D h01 h15
  have t045 := six_triple_orientation D h04 h45
  have t013 := six_triple_orientation D h01 h13
  have t024 := six_triple_orientation D h02 h24
  have t134 := six_triple_orientation D h13 h34
  have t135 := six_triple_orientation D h13 h35
  have t245 := six_triple_orientation D h24 h45
  all_goals rcases t012 with t012 | t012 <;> try linarith
  all_goals rcases t123 with t123 | t123 <;> try linarith
  all_goals rcases t234 with t234 | t234 <;> try linarith
  all_goals rcases t345 with t345 | t345 <;> try linarith
  all_goals rcases t023 with t023 | t023 <;> try linarith
  all_goals rcases t124 with t124 | t124 <;> try linarith
  all_goals rcases t235 with t235 | t235 <;> try linarith
  all_goals rcases t034 with t034 | t034 <;> try linarith
  all_goals rcases t125 with t125 | t125 <;> try linarith
  all_goals rcases t014 with t014 | t014 <;> try linarith
  all_goals rcases t145 with t145 | t145 <;> try linarith
  all_goals rcases t025 with t025 | t025 <;> try linarith
  all_goals rcases t035 with t035 | t035 <;> try linarith
  all_goals rcases t015 with t015 | t015 <;> try linarith
  all_goals rcases t045 with t045 | t045 <;> try linarith
  all_goals rcases t013 with t013 | t013 <;> try linarith
  all_goals rcases t024 with t024 | t024 <;> try linarith
  all_goals rcases t134 with t134 | t134 <;> try linarith
  all_goals rcases t135 with t135 | t135 <;> try linarith
  all_goals rcases t245 with t245 | t245 <;> linarith

#print axioms sixPoint_width

end OrderedDirections
