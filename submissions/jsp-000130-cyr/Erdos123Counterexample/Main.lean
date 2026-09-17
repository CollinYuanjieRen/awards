import Mathlib

/-!
# Erdős Problem #123: the weaker "no common factor" hypothesis fails (`a, b, c = 6, 10, 15`)

Erdős asked whether, for pairwise coprime `a, b, c > 1`, every large integer is a sum of distinct
integers of the form `a^k b^l c^m` none of which divides another (PROVED; NOT formalized here).
The problem page records: "he also suggests the weaker assumption that `a, b, c` have no common
factor, but it is false under this assumption: for example if `a = 6`, `b = 10`, and `c = 15`, then
any `a^k b^l c^m` is `0 (mod 3)` unless `k = m = 0`, when it is `1 (mod 3)`, and so any integer
`2 (mod 3)` requires at least two summands of the shape `10^l`, one of which must divide the other."
This file proves that counterexample: `gcd(6, 10, 15) = 1` but `6, 10, 15` are not pairwise
coprime, and the set `{6^k 10^l 15^m}` is not `d`-complete.

`IsDComplete` and `PairwiseCoprime` are copied verbatim from the formal-conjectures file for the
problem (whose `erdos_123.variants.powers_2_3` uses the same `↑(powers 2) * ↑(powers 3)` shape for
the set of products of powers).
-/

open Filter
open Submonoid
open scoped Pointwise

namespace Erdos123

/--
A sequence is said to be $d$-complete if every large integer is the sum of distinct integers from the
sequence, none of which divide any other. This particular case of $d$-completeness was conjectured by
Erdős and Lewin [ErLe96], who (among other related results) prove this when $a=3$, $b=5$, and $c=7$.
-/
def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    -- The summands come from A
    (s : Set ℕ) ⊆ A ∧
    -- No summand divides another
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧
    -- They sum to n
    s.sum id = n

/--
Predicate for pairwise coprimality of three integers.
Requires all three input values to be pairwise coprime to each other.
-/
def PairwiseCoprime (a b c : ℕ) : Prop := Pairwise (Nat.Coprime.onFun ![a, b, c])

/-- `6, 10, 15` have no common factor but are not pairwise coprime. -/
theorem gcd_six_ten_fifteen : Nat.gcd (Nat.gcd 6 10) 15 = 1 ∧ ¬ PairwiseCoprime 6 10 15 := by
  refine ⟨by norm_num, ?_⟩
  intro h
  have := h (show (0 : Fin 3) ≠ 1 by decide)
  simp [Function.onFun, Nat.Coprime] at this

/-- Every element of `{6^k 10^l 15^m}` is `0 (mod 3)` unless `k = m = 0`, when it is a power of
`10` and `1 (mod 3)`. -/
theorem mem_powers_mod_three {x : ℕ}
    (hx : x ∈ (↑(powers 6) * ↑(powers 10) * ↑(powers 15) : Set ℕ)) :
    x % 3 = 0 ∨ (x % 3 = 1 ∧ ∃ l : ℕ, x = 10 ^ l) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hu
  obtain ⟨l, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hv
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hw
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hk; subst hm
      refine Or.inr ⟨?_, l, by ring⟩
      rw [show (6 : ℕ) ^ 0 * 10 ^ l * 15 ^ 0 = 10 ^ l by ring, Nat.pow_mod]
      norm_num
    · refine Or.inl (Nat.mod_eq_zero_of_dvd ?_)
      have h15 : (3 : ℕ) ∣ 15 ^ m := dvd_pow (by norm_num) (by omega)
      exact Dvd.dvd.mul_left h15 _
  · refine Or.inl (Nat.mod_eq_zero_of_dvd ?_)
    have h6 : (3 : ℕ) ∣ 6 ^ k := dvd_pow (by norm_num) (by omega)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h6 _) _

/-- **The counterexample**: `{6^k 10^l 15^m : k, l, m ≥ 0}` is not `d`-complete (no integer
`2 (mod 3)` is a sum of distinct members none of which divides another). -/
theorem not_isDComplete_six_ten_fifteen :
    ¬ IsDComplete (↑(powers 6) * ↑(powers 10) * ↑(powers 15) : Set ℕ) := by
  intro h
  rw [IsDComplete, Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  obtain ⟨s, hsA, hanti, hsum⟩ := hN (3 * N + 2) (by omega)
  classical
  have hsum' : ∑ x ∈ s, x = 3 * N + 2 := hsum
  have hmem : ∀ x ∈ s, x % 3 = 0 ∨ (x % 3 = 1 ∧ ∃ l : ℕ, x = 10 ^ l) :=
    fun x hx => mem_powers_mod_three (hsA (Finset.mem_coe.mpr hx))
  set P : Finset ℕ := s.filter (fun x => x % 3 = 1) with hPdef
  have hcard : (∑ x ∈ s, x) % 3 = P.card % 3 := by
    rw [Finset.sum_nat_mod, ← Finset.sum_filter_add_sum_filter_not s (fun x => x % 3 = 1)
      (fun x => x % 3)]
    have h1 : ∑ x ∈ s.filter (fun x => x % 3 = 1), x % 3 = P.card := by
      rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)]
      simp [hPdef]
    have h2 : ∑ x ∈ s.filter (fun x => ¬ (x % 3 = 1)), x % 3 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      obtain ⟨hxs, hx1⟩ := Finset.mem_filter.mp hx
      rcases hmem x hxs with hh | ⟨hh, -⟩
      · exact hh
      · exact absurd hh hx1
    rw [h1, h2, add_zero]
  rw [hsum'] at hcard
  have h2c : 1 < P.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2c
  obtain ⟨has, ha1⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, hb1⟩ := Finset.mem_filter.mp hb
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, a = 10 ^ l := by
    rcases hmem a has with hh | ⟨-, hh⟩
    · omega
    · exact hh
  obtain ⟨l', rfl⟩ : ∃ l' : ℕ, b = 10 ^ l' := by
    rcases hmem b hbs with hh | ⟨-, hh⟩
    · omega
    · exact hh
  have hll : l ≠ l' := by rintro rfl; exact hab rfl
  rcases Nat.lt_or_ge l l' with hlt | hge
  · exact hanti (Finset.mem_coe.mpr has) (Finset.mem_coe.mpr hbs) hab
      (pow_dvd_pow 10 hlt.le)
  · have hlt : l' < l := by omega
    exact hanti (Finset.mem_coe.mpr hbs) (Finset.mem_coe.mpr has) (Ne.symm hab)
      (pow_dvd_pow 10 hlt.le)

end Erdos123

open Erdos123 in
/-- **Erdős #123, the page's counterexample, closed form**: `6, 10, 15` have no common factor, yet
`{6^k 10^l 15^m}` is not `d`-complete. -/
theorem erdos_123_no_common_factor_counterexample :
    Nat.gcd (Nat.gcd 6 10) 15 = 1 ∧
      ¬ IsDComplete (↑(powers 6) * ↑(powers 10) * ↑(powers 15) : Set ℕ) := by
  exact ⟨Erdos123.gcd_six_ten_fifteen.1, Erdos123.not_isDComplete_six_ten_fifteen⟩
