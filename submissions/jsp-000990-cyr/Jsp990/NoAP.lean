import Jsp990.Defs

/-!
# JSP-000990 / Erdős #1185 — the "no arithmetic progression" step

This module is purely abstract: it takes a modulus `L` divisible by `16`, a multiplier `T`, a set
`A` all of whose elements `n` satisfy `(n * n * T) % L < L / 16`, and a set `B` all of whose
differences `d` satisfy `L / 8 ≤ (2 * d * d * T) % L ≤ 7 * L / 8`, and concludes that `A` contains
no non-trivial `k`-term arithmetic progression (`k ≥ 3`) with common difference in `B - B`.

The engine is the second difference identity `(a + 2d)² + a² = 2 (a + d)² + 2 d²`: multiplied by
`T` and read modulo `L` it says that `2 d² T` is congruent to `z + x - 2 y`, where `x, y, z` are the
three residues, each of which lies in `[0, L/16)`.  Hence `(2 d² T) % L` lies in
`[0, L/8) ∪ (7L/8, L)`, which is disjoint from `[L/8, 7L/8]`.
-/

open Finset

namespace Erdos1185

/-- The second difference of the squares: `(a + 2d)² + a² = 2 (a + d)² + 2 d²`. -/
theorem second_difference (a d : ℕ) :
    (a + 2 * d) * (a + 2 * d) + a * a = 2 * ((a + d) * (a + d)) + 2 * d * d := by
  ring

/-- Arithmetic core of the three-point lemma: if `L = 16 q`, if `x, y, z < q` and if
`z + x ≡ 2 y + M (mod L)`, then `M % L` avoids the middle band `[L/8, 7L/8]`. -/
theorem mod_interval_of_modEq (L q x y z M : ℕ) (hL : L = 16 * q)
    (hx : x < q) (hy : y < q) (hz : z < q) (h : z + x ≡ 2 * y + M [MOD L]) :
    ¬ (L / 8 ≤ M % L ∧ M % L ≤ 7 * L / 8) := by
  rintro ⟨hlo, hhi⟩
  -- `M` is congruent to `w := z + x + 2L - 2y`, a natural number.
  have hw : M % L = (z + x + 2 * L - 2 * y) % L := by
    have h1 : M + 2 * y ≡ (z + x + 2 * L - 2 * y) + 2 * y [MOD L] := by
      have e1 : (z + x + 2 * L - 2 * y) + 2 * y = z + x + L * 2 := by omega
      have e2 : M + 2 * y = 2 * y + M := by ring
      rw [e1, e2]
      calc 2 * y + M ≡ z + x [MOD L] := h.symm
        _ ≡ z + x + L * 2 [MOD L] := (Nat.add_mul_mod_self_left (z + x) L 2).symm
    exact Nat.ModEq.add_right_cancel' (2 * y) h1
  rw [hw] at hlo hhi
  rcases Nat.lt_or_ge (z + x) (2 * y) with hc | hc
  · -- `w % L = L - (2y - z - x) > 7L/8`
    rw [show z + x + 2 * L - 2 * y = (L - (2 * y - z - x)) + L * 1 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hhi
    omega
  · -- `w % L = z + x - 2y < L/8`
    rw [show z + x + 2 * L - 2 * y = (z + x - 2 * y) + L * 2 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hlo
    omega

/-- **Three-point lemma.**  If `16 ∣ L` and the three residues `(a² T) % L`, `((a+d)² T) % L`,
`((a+2d)² T) % L` are all `< L / 16`, then `(2 d² T) % L` is not in the band `[L/8, 7L/8]`. -/
theorem three_point (L T a d : ℕ) (hL : 16 ∣ L)
    (hx : (a * a * T) % L < L / 16)
    (hy : ((a + d) * (a + d) * T) % L < L / 16)
    (hz : ((a + 2 * d) * (a + 2 * d) * T) % L < L / 16) :
    ¬ (L / 8 ≤ (2 * d * d * T) % L ∧ (2 * d * d * T) % L ≤ 7 * L / 8) := by
  obtain ⟨q, hq⟩ := hL
  have hq16 : L / 16 = q := by omega
  rw [hq16] at hx hy hz
  refine mod_interval_of_modEq L q ((a * a * T) % L) (((a + d) * (a + d) * T) % L)
    (((a + 2 * d) * (a + 2 * d) * T) % L) (2 * d * d * T) hq hx hy hz ?_
  calc ((a + 2 * d) * (a + 2 * d) * T) % L + (a * a * T) % L
      ≡ (a + 2 * d) * (a + 2 * d) * T + a * a * T [MOD L] :=
        Nat.ModEq.add (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
    _ = 2 * ((a + d) * (a + d) * T) + 2 * d * d * T := by ring
    _ ≡ 2 * (((a + d) * (a + d) * T) % L) + 2 * d * d * T [MOD L] :=
        Nat.ModEq.add_right _ (Nat.ModEq.mul_left 2 (Nat.mod_modEq _ _).symm)

/-- **No arithmetic progression.**  If every `n ∈ A` has `(n² T) % L < L / 16` and every positive
difference `d` of two elements of `B` has `(2 d² T) % L ∈ [L/8, 7L/8]`, then `A` contains no
non-trivial `k`-term arithmetic progression (`k ≥ 3`) whose common difference lies in `B - B`. -/
theorem no_ap (L T k : ℕ) (hk : 3 ≤ k) (hL : 16 ∣ L) (A : Finset ℕ)
    (hA : ∀ n ∈ A, (n * n * T) % L < L / 16) (B : Finset ℕ)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ d, 0 < d → b₂ + d = b₁ →
      L / 8 ≤ (2 * d * d * T) % L ∧ (2 * d * d * T) % L ≤ 7 * L / 8) :
    ¬ HasAPWithStepInDiff k A B := by
  rintro ⟨a, d, hd, hmem, b₁, hb₁, b₂, hb₂, hdiff⟩
  have h0 := hA _ (hmem 0 (by omega))
  have h1 := hA _ (hmem 1 (by omega))
  have h2 := hA _ (hmem 2 (by omega))
  rw [Nat.zero_mul, Nat.add_zero] at h0
  rw [Nat.one_mul] at h1
  exact three_point L T a d hL h0 h1 h2 (hB b₁ hb₁ b₂ hb₂ d hd hdiff)

end Erdos1185

