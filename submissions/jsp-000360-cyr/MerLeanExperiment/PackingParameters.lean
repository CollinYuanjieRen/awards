import MerLeanExperiment.ParityGroupDefinitions
import Mathlib.Tactic

namespace Erdos441

theorem exists_finite_positive_bounds {I : Type*} [Fintype I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ (∀ i, c ≤ f i) ∧ (∀ i, f i ≤ B) := by
  classical
  let D : ℝ := 1 + ∑ i, 1 / f i
  let B : ℝ := 1 + ∑ i, f i
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      (one_div_pos.mpr (hf i)).le)
    dsimp [D]
    linarith
  have hB : 0 < B := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => (hf i).le)
    dsimp [B]
    linarith
  refine ⟨1 / D, B, one_div_pos.mpr hD, hB, ?_, ?_⟩
  · intro i
    have hi : 1 / f i ≤ D := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        (one_div_pos.mpr (hf j)).le) (Finset.mem_univ i)
      dsimp [D]
      linarith
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr (hf i)) hi
    simpa only [one_div_one_div] using hh
  · intro i
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      (hf j).le) (Finset.mem_univ i)
    dsimp [B]
    linarith

theorem exists_packing_mesh {l : ℕ} (K : ℕ) (a b : Fin l → ℝ)
    (hab : ∀ j, a j < b j) (S epsilon : ℝ) (hS : 0 ≤ S)
    (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, ∃ m : Fin l → ℕ, 0 < delta ∧ (∀ j, 0 < m j) ∧
      (∀ j, K ≤ m j) ∧ (∀ j, (m j : ℝ) * delta ≤ b j - a j) ∧
      (∀ j, b j - a j < ((m j : ℝ) + 1) * delta) ∧ delta * S ≤ epsilon / 4 := by
  classical
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨c, _, hc, _, hcw, _⟩ := exists_finite_positive_bounds
    (fun j => (b j - a j) / ((K : ℝ) + 1))
    (fun j => div_pos (sub_pos.mpr (hab j)) hK)
  let delta : ℝ := min c (epsilon / (4 * (S + 1)))
  have hd : 0 < delta := lt_min hc (div_pos hepsilon (by positivity))
  have hdw (j : Fin l) : delta ≤ (b j - a j) / ((K : ℝ) + 1) :=
    (min_le_left _ _).trans (hcw j)
  let m : Fin l → ℕ := fun j => ⌊(b j - a j) / delta⌋₊
  have hm (j : Fin l) : K + 1 ≤ m j := by
    apply Nat.le_floor
    rw [Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hd).mpr
    have hh := (le_div_iff₀ hK).mp (hdw j)
    nlinarith
  refine ⟨delta, m, hd, (fun j => by have := hm j; omega),
    (fun j => by have := hm j; omega), ?_, ?_, ?_⟩
  · intro j
    exact (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg (sub_pos.mpr (hab j)).le hd.le))
  · intro j
    exact (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one ((b j - a j) / delta))
  · have hh : delta ≤ epsilon / (4 * (S + 1)) := min_le_right _ _
    have hc := (le_div_iff₀ (show 0 < 4 * (S + 1) by positivity)).mp hh
    nlinarith

theorem exists_packing_residue_budget {K : ℕ} (r : Fin K → ℤ) :
    ∃ M : ℕ, 3 ≤ M ∧ 2 * K ≤ M ∧ ∀ i j, 2 * (r j - r i).natAbs ≤ M := by
  classical
  let S : ℕ := ∑ i : Fin K, ∑ j : Fin K, 2 * (r j - r i).natAbs
  refine ⟨3 + 2 * K + S, by omega, by omega, ?_⟩
  intro i j
  have hj : 2 * (r j - r i).natAbs ≤ ∑ j : Fin K, 2 * (r j - r i).natAbs :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (2 * (r j - r i).natAbs)) (Finset.mem_univ j)
  have hi : (∑ j : Fin K, 2 * (r j - r i).natAbs) ≤ S :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (∑ j : Fin K, 2 * (r j - r i).natAbs))
      (Finset.mem_univ i)
  omega

end Erdos441

#print axioms Erdos441.exists_finite_positive_bounds
#print axioms Erdos441.exists_packing_mesh
#print axioms Erdos441.exists_packing_residue_budget
