import Mathlib

namespace ZeroSum

def V : Finset ℚ := {1/2, -1/3, -1/6}

theorem V_sum : ∑ x ∈ V, x = 0 := by
  have h1 : (1/2 : ℚ) ∉ ({-1/3, -1/6} : Finset ℚ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have h2 : (-1/3 : ℚ) ∉ ({-1/6} : Finset ℚ) := by
    norm_num [Finset.mem_singleton]
  rw [show V = insert (1/2 : ℚ) (insert (-1/3 : ℚ) {(-1/6 : ℚ)}) from rfl,
    Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  norm_num

theorem V_minimal : ∀ T ∈ V.powerset, T.Nonempty → T ≠ V → ∑ x ∈ T, x ≠ 0 := by
  intro T hT hne hneq
  rw [Finset.mem_powerset] at hT
  have hV : V = insert (1/2 : ℚ) (insert (-1/3 : ℚ) {(-1/6 : ℚ)}) := rfl
  have h1 : (1/2 : ℚ) ∉ ({-1/3, -1/6} : Finset ℚ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have h2 : (-1/3 : ℚ) ∉ ({-1/6} : Finset ℚ) := by
    norm_num [Finset.mem_singleton]
  have hsum : ∑ x ∈ T, x = ∑ x ∈ V, (if x ∈ T then x else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hT]
  rw [hsum, hV, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  by_cases ha : (1/2 : ℚ) ∈ T <;> by_cases hb : (-1/3 : ℚ) ∈ T <;>
      by_cases hc : (-1/6 : ℚ) ∈ T <;>
    (try (simp only [ha, hb, hc]; norm_num))
  · -- all three in T: then T = V, contradicting hneq
    exfalso; apply hneq; refine Finset.Subset.antisymm hT ?_; intro x hx
    rw [hV, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · -- none in T: then T = ∅, contradicting hne
    exfalso; obtain ⟨x, hxT⟩ := hne; have hv := hT hxT
    rw [hV, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;>
      first | exact ha hxT | exact hb hxT | exact hc hxT

#print axioms ZeroSum.V_sum
#print axioms ZeroSum.V_minimal

end ZeroSum
