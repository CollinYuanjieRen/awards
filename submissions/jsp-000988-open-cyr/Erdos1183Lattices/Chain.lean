import Erdos1183Lattices.Basic

/-!
# Erdős Problem 1183 — the lower bound `(n + 2) / 2 ≤ f n`

The `n + 1` initial segments of `Fin n` form a chain, and any subfamily of a chain is closed
under unions and intersections.  A colouring splits the chain into two colour classes, one of
which has at least `(n + 2) / 2` members.
-/

namespace Erdos1183

variable {n : ℕ}

/-- The initial segment `{j | j < i}` of `Fin n`. -/
def C (n : ℕ) (i : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j => j.val < i)

@[simp] theorem mem_C {i : ℕ} {j : Fin n} : j ∈ C n i ↔ j.val < i := by
  simp [C]

theorem C_mono {i j : ℕ} (h : i ≤ j) : C n i ⊆ C n j := by
  intro x hx
  rw [mem_C] at hx ⊢
  omega

theorem card_C {i : ℕ} (h : i ≤ n) : (C n i).card = i := by
  have himg : (C n i).image Fin.val = Finset.range i := by
    ext x
    simp only [Finset.mem_image, mem_C, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx h⟩, hx, rfl⟩
  have hcard := Finset.card_image_of_injective (C n i) Fin.val_injective
  rw [himg, Finset.card_range] at hcard
  exact hcard.symm

/-- The chain of all initial segments of `Fin n`. -/
def chain (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (n + 1)).image (C n)

theorem card_chain (n : ℕ) : (chain n).card = n + 1 := by
  rw [chain, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  have h1 : (C n i).card = i := card_C (by omega)
  have h2 : (C n j).card = j := card_C (by omega)
  rw [hij, h2] at h1
  exact h1.symm

/-- Any two members of the chain are comparable. -/
theorem chain_total {A B : Finset (Fin n)} (hA : A ∈ chain n) (hB : B ∈ chain n) :
    A ⊆ B ∨ B ⊆ A := by
  rw [chain, Finset.mem_image] at hA hB
  obtain ⟨i, -, rfl⟩ := hA
  obtain ⟨j, -, rfl⟩ := hB
  rcases le_total i j with h | h
  · exact Or.inl (C_mono h)
  · exact Or.inr (C_mono h)

/-- Any subfamily of the chain is closed under unions and intersections. -/
theorem closed_of_subset_chain {S : Finset (Finset (Fin n))} (h : S ⊆ chain n) : Closed S := by
  intro A hA B hB
  rcases chain_total (h hA) (h hB) with hs | hs
  · refine ⟨?_, ?_⟩
    · rw [Finset.union_eq_right.mpr hs]
      exact hB
    · rw [Finset.inter_eq_left.mpr hs]
      exact hA
  · refine ⟨?_, ?_⟩
    · rw [Finset.union_eq_left.mpr hs]
      exact hA
    · rw [Finset.inter_eq_right.mpr hs]
      exact hB

/-- The lower bound: every colouring is constant on at least `(n + 2) / 2` members of the
chain, and those form a nonempty closed family. -/
theorem good_lower (n : ℕ) : Good n ((n + 2) / 2) := by
  intro c
  have hunion : (chain n).filter (fun A => c A = true) ∪
      (chain n).filter (fun A => c A = false) = chain n := by
    ext A
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      cases hb : c A
      · exact Or.inr ⟨h, rfl⟩
      · exact Or.inl ⟨h, rfl⟩
  have hdisj : Disjoint ((chain n).filter (fun A => c A = true))
      ((chain n).filter (fun A => c A = false)) := by
    rw [Finset.disjoint_left]
    intro A hA hA'
    rw [Finset.mem_filter] at hA hA'
    rw [hA.2] at hA'
    exact Bool.noConfusion hA'.2
  have hsum : ((chain n).filter (fun A => c A = true)).card +
      ((chain n).filter (fun A => c A = false)).card = n + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, card_chain]
  have hex : ∃ b : Bool, (n + 2) / 2 ≤ ((chain n).filter (fun A => c A = b)).card := by
    by_contra hcon
    simp only [not_exists, Nat.not_le] at hcon
    have h1 := hcon true
    have h2 := hcon false
    omega
  obtain ⟨b, hb⟩ := hex
  refine ⟨(chain n).filter (fun A => c A = b), Finset.card_pos.mp (by omega),
    closed_of_subset_chain (Finset.filter_subset _ _), ⟨b, ?_⟩, hb⟩
  intro A hA
  exact (Finset.mem_filter.mp hA).2

/-- `(n + 2) / 2 ≤ f n`, the trivial lower bound of the problem. -/
theorem le_f (n : ℕ) : (n + 2) / 2 ≤ f n :=
  le_f_of_good (good_lower n)

end Erdos1183
