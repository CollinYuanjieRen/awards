import Erdos387Proof.FiniteAbel

/-!
# A common mixed-Abel bound for a finite outer family

For every outer index, one rectangular prefix is selected which maximizes the
norm of the unweighted partial sums.  The selection depends only on the outer
index, never on an inner row.  A uniform mixed-variation bound may therefore
be summed against exactly these selected prefix norms.
-/

set_option autoImplicit false

namespace Erdos387Proof.FamilyMixedAbel

open scoped BigOperators

noncomputable def prefixNorm {J : Type*}
    (f : J → ℕ → ℕ → ℂ) (c : J) (n m : ℕ) : ℝ :=
  ‖∑ u ∈ Finset.range n, ∑ v ∈ Finset.range m, f c u v‖

/-- A single pair of cutoffs is chosen for each outer index.  The full family
of weighted sums is bounded by the sum of the corresponding maximizing
unweighted prefixes. -/
theorem exists_prefix_maximizers
    {J : Type*} (I : Finset J)
    (w f : J → ℕ → ℕ → ℂ) (N M : ℕ) {V : ℝ} (hV : 0 ≤ V)
    (hvar : ∀ c ∈ I, FiniteAbel.mixedVariationMass (w c) N M ≤ V) :
    ∃ rn sn : J → ℕ,
      (∀ c ∈ I, rn c ≤ N ∧ sn c ≤ M) ∧
      (∑ c ∈ I,
        ‖∑ u ∈ Finset.range N, ∑ v ∈ Finset.range M,
          w c u v * f c u v‖) ≤
        V * ∑ c ∈ I, prefixNorm f c (rn c) (sn c) := by
  classical
  let P : Finset (ℕ × ℕ) :=
    (Finset.range (N + 1)).product (Finset.range (M + 1))
  have hP : P.Nonempty := by
    refine ⟨(0,0),?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
  have hmax (c : J) :
      ∃ q ∈ P, ∀ q' ∈ P,
        prefixNorm f c q'.1 q'.2 ≤ prefixNorm f c q.1 q.2 :=
    Finset.exists_max_image P (fun q => prefixNorm f c q.1 q.2) hP
  let q : J → ℕ × ℕ := fun c => Classical.choose (hmax c)
  have hqmem (c : J) : q c ∈ P := (Classical.choose_spec (hmax c)).1
  have hqmax (c : J) : ∀ q' ∈ P,
      prefixNorm f c q'.1 q'.2 ≤ prefixNorm f c (q c).1 (q c).2 :=
    (Classical.choose_spec (hmax c)).2
  refine ⟨fun c => (q c).1,fun c => (q c).2,?_,?_⟩
  · intro c hc
    have hqm : q c ∈ (Finset.range (N + 1)).product
        (Finset.range (M + 1)) := by simpa only [P] using hqmem c
    have hm := Finset.mem_product.mp hqm
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hm.1),
      Nat.le_of_lt_succ (Finset.mem_range.mp hm.2)⟩
  · calc
      _ ≤ ∑ c ∈ I,
          FiniteAbel.mixedVariationMass (w c) N M *
            prefixNorm f c (q c).1 (q c).2 := by
        apply Finset.sum_le_sum
        intro c hc
        apply FiniteAbel.norm_double_sum_mul_le_mixedVariation
        intro n hn m hm
        apply hqmax c (n,m)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
      _ ≤ ∑ c ∈ I, V * prefixNorm f c (q c).1 (q c).2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_right (hvar c hc) (norm_nonneg _)
      _ = V * ∑ c ∈ I, prefixNorm f c (q c).1 (q c).2 := by
        rw [Finset.mul_sum]

end Erdos387Proof.FamilyMixedAbel
