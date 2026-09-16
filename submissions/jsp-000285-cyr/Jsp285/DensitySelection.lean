import Jsp285.FreshSelection

/-! Two disjoint occurrence sequences selected from eventual linear counting witnesses. -/

namespace Jsp285

/-- Eventual linear finite counts yield two disjoint injective occurrence
sequences whose values grow at most like `i / D`. -/
theorem exists_two_linear_selections
    (A : ℕ → ℕ) (D N₀ : ℕ) (hD : 0 < D) (_hN₀ : 1 ≤ N₀)
    (hcount : ∀ N : ℕ, N₀ ≤ N → ∃ s : Finset ℕ,
      8 * D * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N) :
    ∃ β ρ : ℕ → ℕ,
      Function.Injective β ∧ Function.Injective ρ ∧
      Disjoint (Set.range β) (Set.range ρ) ∧
      ∃ I₀ : ℕ, ∀ i : ℕ, I₀ ≤ i →
        A (β i) ≤ i / D ∧ A (ρ i) ≤ i / D := by
  let Nstage : ℕ → ℕ := fun j ↦
    max N₀ (((j / 2) / (2 * D)) + 1)
  let P : ℕ → ℕ → Prop := fun j x ↦ A x ≤ Nstage j
  have havoid : ∀ j (u : Finset ℕ), u.card ≤ j →
      ∃ x, x ∉ u ∧ P j x := by
    intro j u hu
    have hNstage : N₀ ≤ Nstage j := Nat.le_max_left _ _
    obtain ⟨s, hscard, hsbox⟩ := hcount (Nstage j) hNstage
    have hden : 0 < 2 * D := by omega
    have hlt := Nat.lt_mul_div_succ (j / 2) hden
    have hright : (j / 2) / (2 * D) + 1 ≤ Nstage j :=
      Nat.le_max_right _ _
    have hjcard : j + 1 ≤ 8 * D * Nstage j := by
      calc
        j + 1 ≤ 4 * (j / 2 + 1) := by omega
        _ ≤ 4 * ((2 * D) * ((j / 2) / (2 * D) + 1)) :=
          Nat.mul_le_mul_left 4 (Nat.lt_iff_add_one_le.mp hlt)
        _ ≤ 4 * ((2 * D) * Nstage j) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (2 * D) hright)
        _ = 8 * D * Nstage j := by ring
    have hus : u.card < s.card := by omega
    obtain ⟨x, hxs, hxu⟩ := Finset.exists_mem_notMem_of_card_lt_card hus
    exact ⟨x, hxu, hsbox x hxs⟩
  obtain ⟨f, hf, hfP⟩ := exists_injective_of_finite_avoidance P havoid
  let β : ℕ → ℕ := fun i ↦ f (2 * i)
  let ρ : ℕ → ℕ := fun i ↦ f (2 * i + 1)
  have hβ : Function.Injective β := by
    intro i j hij
    exact Nat.mul_left_cancel (by omega) (hf hij)
  have hρ : Function.Injective ρ := by
    intro i j hij
    have hij' := hf hij
    omega
  have hdisj : Disjoint (Set.range β) (Set.range ρ) := by
    rw [Set.disjoint_range_iff]
    intro i j hij
    have hij' := hf hij
    omega
  refine ⟨β, ρ, hβ, hρ, hdisj, max (D * N₀) (2 * D), ?_⟩
  intro i hi
  have hiN₀ : D * N₀ ≤ i := (Nat.le_max_left _ _).trans hi
  have hi2D : 2 * D ≤ i := (Nat.le_max_right _ _).trans hi
  have hN₀div : N₀ ≤ i / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa [Nat.mul_comm] using hiN₀
  have hqpos : 1 ≤ i / (2 * D) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * D)).mpr
    simpa using hi2D
  have htwodiv : 2 * (i / (2 * D)) ≤ i / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    have h := Nat.mul_div_le i (2 * D)
    nlinarith
  have hstage : max N₀ (i / (2 * D) + 1) ≤ i / D := by
    apply max_le hN₀div
    exact (by omega : i / (2 * D) + 1 ≤ i / D)
  constructor
  · have heven : (2 * i) / 2 = i := by omega
    have hstageEven : Nstage (2 * i) ≤ i / D := by
      dsimp only [Nstage]
      rw [heven]
      exact hstage
    exact (hfP (2 * i)).trans hstageEven
  · have hodd : (2 * i + 1) / 2 = i := by omega
    have hstageOdd : Nstage (2 * i + 1) ≤ i / D := by
      dsimp only [Nstage]
      rw [hodd]
      exact hstage
    exact (hfP (2 * i + 1)).trans hstageOdd

end Jsp285
