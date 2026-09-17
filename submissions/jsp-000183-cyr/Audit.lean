import Erdos193Walk

open Set

#print axioms Erdos193.erdos_193
#print axioms Erdos193.exists_walk_no_collinear_triple
#print axioms Erdos193Walk.no_collinear_triple
#print axioms Erdos193Walk.norm_w_sub
#print axioms Erdos193Walk.norm_z_sub
#print axioms Erdos193Walk.P_succ_sub_mem
#print axioms Erdos193Walk.P_injective

/-- Erdős Problem 193 exactly as stated in formal-conjectures, with the answer `False`. -/
example :
    False ↔ ∀ S : Set (Fin 3 → ℤ), S.Finite →
      ∀ a : ℕ → Fin 3 → ℤ, Erdos193.IsSWalk S a → (range a).Infinite →
      Erdos193.HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ)) :=
  Erdos193.erdos_193

/-- The positive form with the two auxiliary definitions unfolded. -/
example :
    ∃ S : Set (Fin 3 → ℤ), S.Finite ∧ ∃ a : ℕ → Fin 3 → ℤ, (∀ n, a (n + 1) - a n ∈ S) ∧
      (range a).Infinite ∧
      ¬ ∃ x ∈ range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ),
        ∃ y ∈ range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ),
        ∃ z ∈ range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ),
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear ℚ ({x, y, z} : Set (Fin 3 → ℚ)) :=
  Erdos193.exists_walk_no_collinear_triple
