import Mathlib

namespace Erdos1109

/-- every pairwise sum of `A` (including `a + a`) is squarefree -/
def SquarefreeSumset (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)

/-- a number divisible by `4` is not squarefree (its `2²` factor blocks squarefreeness). -/
private lemma not_squarefree_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) : ¬ Squarefree n := by
  intro hsq
  obtain ⟨m, rfl⟩ := h4
  have h2 : IsUnit (2 : ℕ) := hsq 2 ⟨m, by ring⟩
  rw [Nat.isUnit_iff] at h2
  omega

/-- every element of a squarefree-sumset set is odd -/
theorem odd_of_mem {A : Finset ℕ} (h : SquarefreeSumset A) {a : ℕ} (ha : a ∈ A) : Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨c, hc⟩ := he
    exact absurd (h a ha a ha) (not_squarefree_of_four_dvd (by omega))
  · exact ho

/-- a squarefree-sumset set lies in a single residue class mod 4 (all ≡ 1, or all ≡ 3) -/
theorem single_class_mod_four {A : Finset ℕ} (h : SquarefreeSumset A) :
    (∀ a ∈ A, a % 4 = 1) ∨ (∀ a ∈ A, a % 4 = 3) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨hcon1, hcon3⟩ := hcon
  obtain ⟨a, ha'⟩ := hcon1
  obtain ⟨b, hb'⟩ := hcon3
  rw [not_imp] at ha' hb'
  obtain ⟨ha, ha4⟩ := ha'
  obtain ⟨hb, hb4⟩ := hb'
  have hao := odd_of_mem h ha
  have hbo := odd_of_mem h hb
  rw [Nat.odd_iff] at hao hbo
  exact not_squarefree_of_four_dvd (show (4 : ℕ) ∣ a + b by omega) (h a ha b hb)

/-- if `A ⊆ {1,…,N}` lies in a fixed residue class `r ∈ {1,3}` mod 4, then `4·|A| ≤ N + 3`. -/
private lemma card_le_of_residue {N r : ℕ} {A : Finset ℕ} (hr1 : 1 ≤ r) (hr4 : r < 4)
    (hA : A ⊆ Finset.Icc 1 N) (hres : ∀ a ∈ A, a % 4 = r) :
    4 * A.card ≤ N + 3 := by
  have hsub : A.card ≤ (N - r) / 4 + 1 := by
    have h2 : A.card ≤ (Finset.range ((N - r) / 4 + 1)).card := by
      apply Finset.card_le_card_of_injOn (f := fun a => (a - r) / 4)
      · intro a ha
        have hmem := hA ha
        rw [Finset.mem_Icc] at hmem
        have hr := hres a ha
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro a ha b hb hab
        rw [Finset.mem_coe] at ha hb
        replace hab : (a - r) / 4 = (b - r) / 4 := hab
        have h3 := hres a ha
        have h4 := hres b hb
        omega
    rwa [Finset.card_range] at h2
  rcases A.eq_empty_or_nonempty with hE | ⟨a₀, ha₀⟩
  · subst hE; simp
  · have hmem := hA ha₀
    rw [Finset.mem_Icc] at hmem
    have := hres a₀ ha₀
    omega

/-- the elementary upper bound `4·|A| ≤ N + 3` for `A ⊆ {1,…,N}` -/
theorem card_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (h : SquarefreeSumset A) :
    4 * A.card ≤ N + 3 := by
  rcases single_class_mod_four h with h1 | h3
  · exact card_le_of_residue (by omega) (by omega) hA h1
  · exact card_le_of_residue (by omega) (by omega) hA h3

#print axioms odd_of_mem
#print axioms single_class_mod_four
#print axioms card_le

end Erdos1109
