import Mathlib

/-!
# Erdős Problem #865: the `k = 2` case — `A ⊆ {1, …, 2N}` with `|A| ≥ N + 2` contains `a ≠ b`
with `a + b ∈ A`

Erdős and Sós asked whether there is `C > 0` such that every `A ⊆ {1, …, N}` with
`|A| ≥ (5/8)N + C` contains distinct `a, b, c` with `a + b, a + c, b + c ∈ A` (solved by Cipollini
and GPT Pro; not addressed here, nor the general `f_k(N)` questions).  The problem page records:
"It is a classical folklore fact that if `A ⊆ {1, …, 2N}` has size `≥ N + 2` then there are distinct
`a, b ∈ A` such that `a + b ∈ A`, which establishes the `k = 2` case."  This file proves that
fact, in the exact shape of the formal-conjectures statement `Erdos865.erdos_865.variants.k2`.

Proof.  Let `m = min A` and `B = A \ {m}`, so `|B| ≥ N + 1` and `B ⊆ [m + 1, 2N]`.  The
translate `B − m = {x − m : x ∈ B}` also lies in `[1, 2N]`, so `|B ∩ (B − m)| ≥ |B| + |B − m| − 2N
≥ 2 > 0`, and there is some `x ∈ B ∩ (B − m)`.  Then `a = m` and `b = x` are distinct elements of
`A` (as `x ∈ B = A \ {m}`) with `a + b = m + x ∈ B ⊆ A`.
-/

open Finset

/-- **Erdős #865, the `k = 2` case (classical folklore)**: if `A ⊆ {1, …, 2N}` has size at least
`N + 2`, then there are distinct `a, b ∈ A` with `a + b ∈ A`. -/
theorem erdos_865_k2 (N : ℕ) :
    ∀ A ⊆ Icc 1 (2 * N), A.card ≥ N + 2 →
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A := by
  intro A hA hcard
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨m, hmA, hmle⟩ : ∃ m ∈ A, ∀ x ∈ A, m ≤ x :=
    ⟨A.min' hne, A.min'_mem hne, fun x hx => A.min'_le x hx⟩
  set B := A.erase m with hBdef
  have hBA : B ⊆ A := Finset.erase_subset _ _
  have hBlt : ∀ x ∈ B, m < x := by
    intro x hx
    rw [hBdef, Finset.mem_erase] at hx
    exact lt_of_le_of_ne (hmle x hx.2) (Ne.symm hx.1)
  have hBub : ∀ x ∈ B, x ≤ 2 * N := fun x hx => (Finset.mem_Icc.mp (hA (hBA hx))).2
  have hBcard : N + 1 ≤ B.card := by
    rw [hBdef, Finset.card_erase_of_mem hmA]; omega
  set C := B.image (fun x => x - m) with hCdef
  have hCcard : C.card = B.card := by
    rw [hCdef]
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    have hxy' : x - m = y - m := hxy
    have h1 := hBlt x hx
    have h2 := hBlt y hy
    omega
  have hunion : (B ∪ C).card ≤ 2 * N := by
    have hsub : B ∪ C ⊆ Icc 1 (2 * N) := by
      intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · exact hA (hBA h)
      · rw [hCdef, Finset.mem_image] at h
        obtain ⟨x, hx, rfl⟩ := h
        have h1 := hBlt x hx
        have h2 := hBub x hx
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    calc (B ∪ C).card ≤ (Icc 1 (2 * N)).card := Finset.card_le_card hsub
      _ = 2 * N := by simp [Nat.card_Icc]
  have hinter : (B ∩ C).Nonempty := by
    rw [← Finset.card_pos]
    have h := Finset.card_union_add_card_inter B C
    omega
  obtain ⟨x, hx⟩ := hinter
  rw [Finset.mem_inter] at hx
  obtain ⟨hxB, hxC⟩ := hx
  rw [hCdef, Finset.mem_image] at hxC
  obtain ⟨y, hyB, hyx⟩ := hxC
  refine ⟨m, hmA, x, hBA hxB, Ne.symm (Finset.ne_of_mem_erase hxB), ?_⟩
  have h1 := hBlt y hyB
  have h2 : m + x = y := by omega
  rw [h2]
  exact hBA hyB

/-- Closed form of `erdos_865_k2`. -/
theorem erdos_865_k2_closed :
    ¬ ∃ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 (2 * N) ∧ A.card ≥ N + 2 ∧
      ¬ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A := by
  rintro ⟨N, A, hA, hcard, h⟩
  exact h (erdos_865_k2 N A hA hcard)
