import Proof.Defs

/-!
# Erdős problem #201 — the trivial inequality `G_k(N) ≤ R_k(N)`, and the values at `N = 5`

The problem page for Erdős problem #201 asks for the size of `G_k(N)`, the largest `g` such
that every set of `N` integers contains a `k`-AP-free subset of size `g`, and for its
relation to `R_k(N)`, the size of the largest `k`-AP-free subset of `{1, …, N}`.  The page
calls the inequality `G_k(N) ≤ R_k(N)` trivial, and illustrates that it can be strict with
the values `G_3(5) = 3` and `R_3(5) = 4`.

This package proves that trivial inequality together with the page's values `R_3(5) = 4`
and `G_3(5) ≤ 3` (witness `{1, 3, 4, 5, 7}`, every four-element subset of which contains a
three-term progression).

Not claimed here: the lower bound `G_3(5) ≥ 3`, the values at `N = 14`, the
Komlós–Sulyok–Szemerédi bound `R_k(N) ≪_k G_k(N)`, and the limit question of Erdős
problem #201.

## Main results

* `Erdos201.G_le_R` (T1) — `G k N ≤ R k N` for all `k` and `N`.
* `Erdos201.R_three_five` (T2) — `R 3 5 = 4`.
* `Erdos201.G_three_five_le` (T3) — `G 3 5 ≤ 3`.
-/

namespace Erdos201

/-- (T1) The trivial inequality of the problem page: `{1, …, N}` is one of the `N`-element
sets of integers over which `G_k(N)` is a minimum, so `G_k(N) ≤ R_k(N)`. -/
theorem G_le_R (k N : ℕ) : G k N ≤ R k N :=
  G_le_apFreeMax k N _ (by simp)

/-- A convenient way to establish `APFree`: no positive common difference gives a full
progression inside `S`. -/
theorem apFree_of_forall (k : ℕ) (S : Finset ℤ)
    (h : ∀ a d : ℤ, 0 < d → (∀ i : ℕ, i < k → a + i * d ∈ S) → False) : APFree k S := by
  rintro ⟨a, d, hd, hmem⟩
  exact h a d hd hmem

/-- A three-term progression `x, y, z` with positive common difference inside `S` witnesses
`HasAP 3 S`. -/
theorem hasAP_three_of_mem {S : Finset ℤ} {a d x y z : ℤ} (hd : 0 < d)
    (hx : a = x) (hy : a + d = y) (hz : a + 2 * d = z)
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S) : HasAP 3 S := by
  refine ⟨a, d, hd, ?_⟩
  intro i hi
  interval_cases i
  · simpa [hx] using hxS
  · simpa [hy] using hyS
  · simpa [hz] using hzS

/-- (T2) The page's value `R_3(5) = 4`: the set `{1, 2, 4, 5}` has no three-term
progression, while the only five-element subset of `{1, …, 5}` is `{1, …, 5}` itself, which
contains `1, 2, 3`. -/
theorem R_three_five : R 3 5 = 4 := by
  have hIcc : R 3 5 = apFreeMax 3 (Finset.Icc (1 : ℤ) 5) := by
    unfold R
    norm_num
  rw [hIcc]
  refine le_antisymm ?_ ?_
  · rw [apFreeMax_le_iff]
    intro S hS hfree
    by_contra hc
    have hcard : (Finset.Icc (1 : ℤ) 5).card ≤ S.card := by
      simp only [Int.card_Icc]
      omega
    have hSeq : S = Finset.Icc (1 : ℤ) 5 := Finset.eq_of_subset_of_card_le hS hcard
    refine hfree (hasAP_three_of_mem (a := (1 : ℤ)) (d := 1) (x := 1) (y := 2) (z := 3)
      (by norm_num) rfl (by norm_num) (by norm_num) ?_ ?_ ?_) <;>
      · rw [hSeq, Finset.mem_Icc]; norm_num
  · have hsub : ({1, 2, 4, 5} : Finset ℤ) ⊆ Finset.Icc (1 : ℤ) 5 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have hcard : ({1, 2, 4, 5} : Finset ℤ).card = 4 := by decide
    have hfree : APFree 3 ({1, 2, 4, 5} : Finset ℤ) := by
      refine apFree_of_forall 3 _ ?_
      intro a d hd h
      have h0 := h 0 (by norm_num)
      have h1 := h 1 (by norm_num)
      have h2 := h 2 (by norm_num)
      simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero,
        Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
      omega
    calc (4 : ℕ) = ({1, 2, 4, 5} : Finset ℤ).card := hcard.symm
      _ ≤ apFreeMax 3 (Finset.Icc (1 : ℤ) 5) := le_apFreeMax 3 hsub hfree

/-- (T3) The page's value `G_3(5) ≤ 3`: every four-element subset of `T = {1, 3, 4, 5, 7}`
contains a three-term progression, so the largest `3`-AP-free subset of `T` has at most
three elements. -/
theorem G_three_five_le : G 3 5 ≤ 3 := by
  have hTcard : ({1, 3, 4, 5, 7} : Finset ℤ).card = 5 := by decide
  refine le_trans (G_le_apFreeMax 3 5 ({1, 3, 4, 5, 7} : Finset ℤ) hTcard) ?_
  rw [apFreeMax_le_iff]
  intro S hS hfree
  by_contra hc
  have h4 : 4 ≤ S.card := by omega
  -- At most one element of `T` is missing from `S`.
  have pair : ∀ x y : ℤ, x ∈ ({1, 3, 4, 5, 7} : Finset ℤ) →
      y ∈ ({1, 3, 4, 5, 7} : Finset ℤ) → x ≠ y → x ∉ S → y ∈ S := by
    intro x y hx hy hxy hxS
    by_contra hyS
    have hsub : S ⊆ (({1, 3, 4, 5, 7} : Finset ℤ).erase x).erase y := by
      intro z hz
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hS hz⟩⟩
      · rintro rfl; exact hyS hz
      · rintro rfl; exact hxS hz
    have he1 : (({1, 3, 4, 5, 7} : Finset ℤ).erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hTcard]
    have he2 : ((({1, 3, 4, 5, 7} : Finset ℤ).erase x).erase y).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩), he1]
    have := Finset.card_le_card hsub
    omega
  refine hfree ?_
  by_cases h4mem : (4 : ℤ) ∈ S
  · by_cases h3mem : (3 : ℤ) ∈ S
    · by_cases h5mem : (5 : ℤ) ∈ S
      · -- `3, 4, 5`
        exact hasAP_three_of_mem (a := (3 : ℤ)) (d := 1) (x := 3) (y := 4) (z := 5)
          (by norm_num) rfl (by norm_num) (by norm_num) h3mem h4mem h5mem
      · -- `1, 4, 7`
        have h1mem : (1 : ℤ) ∈ S := pair 5 1 (by decide) (by decide) (by decide) h5mem
        have h7mem : (7 : ℤ) ∈ S := pair 5 7 (by decide) (by decide) (by decide) h5mem
        exact hasAP_three_of_mem (a := (1 : ℤ)) (d := 3) (x := 1) (y := 4) (z := 7)
          (by norm_num) rfl (by norm_num) (by norm_num) h1mem h4mem h7mem
    · -- `1, 4, 7`
      have h1mem : (1 : ℤ) ∈ S := pair 3 1 (by decide) (by decide) (by decide) h3mem
      have h7mem : (7 : ℤ) ∈ S := pair 3 7 (by decide) (by decide) (by decide) h3mem
      exact hasAP_three_of_mem (a := (1 : ℤ)) (d := 3) (x := 1) (y := 4) (z := 7)
        (by norm_num) rfl (by norm_num) (by norm_num) h1mem h4mem h7mem
  · -- `1, 3, 5`
    have h1mem : (1 : ℤ) ∈ S := pair 4 1 (by decide) (by decide) (by decide) h4mem
    have h3mem : (3 : ℤ) ∈ S := pair 4 3 (by decide) (by decide) (by decide) h4mem
    have h5mem : (5 : ℤ) ∈ S := pair 4 5 (by decide) (by decide) (by decide) h4mem
    exact hasAP_three_of_mem (a := (1 : ℤ)) (d := 2) (x := 1) (y := 3) (z := 5)
      (by norm_num) rfl (by norm_num) (by norm_num) h1mem h3mem h5mem

end Erdos201
