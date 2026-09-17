import Jsp731.Defs

/-!
# JSP-000731 / Erdős #880 — the enumeration bridge

`HasBoundedGaps B` is phrased with *windows*: some `C` makes every sufficiently late window
`[n, n + C]` meet `B`.  The question of Burr and Erdős is phrased with the *enumeration*
`b₀ < b₁ < ⋯` of `B`: is `b_{i+1} - b_i` bounded?

For an infinite `B`, Mathlib's `Nat.nth (· ∈ B)` is exactly that enumeration, and this file
shows the two formulations agree:

* `exists_nth_diff_le_of_hasBoundedGaps`: bounded windows give a bound on every consecutive
  difference of the enumeration (not merely eventually — the finitely many early indices are
  absorbed into the constant);
* `exists_nth_diff_gt_of_not_hasBoundedGaps`: conversely, if no window length works then the
  consecutive differences of the enumeration are unbounded.

Together they say `HasBoundedGaps B ↔ ∃ C, ∀ i, b_{i+1} - b_i ≤ C` for infinite `B`.
-/

open Filter

namespace Erdos880

/-- `nth (i+1)` is the least element of `B` above `nth i`. -/
theorem nth_succ_le_of_mem {B : Set ℕ} (hB : B.Infinite) {i b : ℕ} (hb : b ∈ B)
    (hlt : Nat.nth (· ∈ B) i < b) : Nat.nth (· ∈ B) (i + 1) ≤ b := by
  have hB' : (Set.ofPred (· ∈ B)).Infinite := hB
  rw [Nat.nth_eq_sInf]
  refine Nat.sInf_le ⟨hb, fun k hk => ?_⟩
  exact lt_of_le_of_lt ((Nat.nth_le_nth hB').2 (Nat.lt_succ_iff.1 hk)) hlt

/-- Bounded gaps ⇒ the enumeration has bounded consecutive differences (for every index). -/
theorem exists_nth_diff_le_of_hasBoundedGaps {B : Set ℕ} (hB : B.Infinite)
    (h : HasBoundedGaps B) :
    ∃ C : ℕ, ∀ i : ℕ, Nat.nth (· ∈ B) (i + 1) - Nat.nth (· ∈ B) i ≤ C := by
  obtain ⟨C₀, hev⟩ := h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀ + C₀ + 1, fun i => ?_⟩
  by_cases hcase : N₀ ≤ Nat.nth (· ∈ B) i + 1
  · -- the window starting just above `nth i` is already late enough
    obtain ⟨b, hbB, hb1, hb2⟩ := hN₀ (Nat.nth (· ∈ B) i + 1) hcase
    have hle : Nat.nth (· ∈ B) (i + 1) ≤ b := nth_succ_le_of_mem hB hbB (by omega)
    omega
  · -- otherwise `nth i` is small, and the window `[N₀, N₀ + C₀]` lies above it
    obtain ⟨b, hbB, hb1, hb2⟩ := hN₀ N₀ le_rfl
    have hle : Nat.nth (· ∈ B) (i + 1) ≤ b := nth_succ_le_of_mem hB hbB (by omega)
    omega

/-- Unbounded gaps ⇒ the consecutive differences of the enumeration are unbounded. -/
theorem exists_nth_diff_gt_of_not_hasBoundedGaps {B : Set ℕ} (hB : B.Infinite)
    (h : ¬ HasBoundedGaps B) (C : ℕ) :
    ∃ i : ℕ, C < Nat.nth (· ∈ B) (i + 1) - Nat.nth (· ∈ B) i := by
  classical
  have hB' : (Set.ofPred (· ∈ B)).Infinite := hB
  obtain ⟨b₀, hb₀⟩ := hB.nonempty
  -- `C` is not a valid window length, so arbitrarily late windows `[n, n + C]` miss `B`
  have hne : ¬ ∀ᶠ n in atTop, ∃ b ∈ B, n ≤ b ∧ b ≤ n + C := fun hc => h ⟨C, hc⟩
  obtain ⟨n, hn1, hn2⟩ :=
    Filter.frequently_atTop.1 (Filter.not_eventually.1 hne) (b₀ + 1)
  -- `n` is past the element `b₀ ∈ B`, so at least one element of `B` lies below `n`
  have hpos : 0 < Nat.count (· ∈ B) n := lt_of_le_of_lt (Nat.zero_le _)
    (Nat.count_strict_mono hb₀ (by omega))
  obtain ⟨i, hi⟩ : ∃ i, Nat.count (· ∈ B) n = i + 1 := ⟨Nat.count (· ∈ B) n - 1, by omega⟩
  refine ⟨i, ?_⟩
  have h1 : Nat.nth (· ∈ B) i < n := Nat.nth_lt_of_lt_count (by omega)
  have h2 : n ≤ Nat.nth (· ∈ B) (i + 1) := by
    rw [← hi]; exact Nat.le_nth_count hB' n
  have h3 : Nat.nth (· ∈ B) (i + 1) ∈ B := Nat.nth_mem_of_infinite hB' (i + 1)
  have h4 : n + C < Nat.nth (· ∈ B) (i + 1) := by
    by_contra hc
    exact hn2 ⟨_, h3, h2, by omega⟩
  omega

end Erdos880

#print axioms Erdos880.exists_nth_diff_le_of_hasBoundedGaps
#print axioms Erdos880.exists_nth_diff_gt_of_not_hasBoundedGaps
