import Jsp731.Construction
import Jsp731.PowTwo
import Jsp731.OrderTwo

/-!
# JSP-000731 / Erdős #880 — coverage: `basis h` is an asymptotic basis of order `h`

This file proves the positive half of the counterexample of Hegyvári–Hennecart–Plagne (2007)
for `h ≥ 3`: every integer `m ≥ h` is a sum of at most `h` elements of `A = basis h`, so `A` is
an asymptotic basis of order `h` in Erdős's "`k` or fewer" sense.

The work happens inside a single block.  Fix `n`, write `x = x n` for the scale and
`c = 3·2^{h−2} − 1` for the coefficient, so that `x_{n+1} = c·x² + h·x`, and recall that block
`n` consists of the interval `[x, x + x²)` together with the spikes `x + 2^j·x²`, `j < h − 1`.
Let `x ≤ m < c·x² + h·x`.

* If `m < h·x` then, since `h·x ≤ x + x²`, the number `m = x + (m − x)` is itself a single
  element of the interval part of the block.
* Otherwise put `y = m − h·x < c·x²` and divide: `y = q·x² + r` with `r < x²` and `q < c`.
  Split off one top spike if needed, `q = ε·2^{h−2} + q'` with `ε ≤ 1` and `q' + 2 ≤ 2^{h−1}`.
  By `exists_bits` the number `q'` is `∑_{j ∈ J} 2^j` for some `J ⊆ range (h−1)`, and the last
  conjunct of `exists_bits` upgrades `|J| ≤ h − 1` to `|J| ≤ h − 2` because `q' + 1 < 2^{h−1}`.
  Then
  `m = ε·(x + 2^{h−2}·x²) + ∑_{j ∈ J} (x + 2^j·x²) + (x + r) + (h − 1 − ε − |J|)·x`
  exhibits `m` as a sum of exactly `h` elements of block `n`: the `x`-coefficients add up to
  `ε + |J| + 1 + (h − 1 − ε − |J|) = h` and the `x²`-coefficients to `ε·2^{h−2} + q' = q`.

All of the block-independent arithmetic is isolated in `isSumOfAtMost_of_bounds`, which only
knows that the interval elements `x + r` (`r < x²`) and the spikes `x + 2^j·x²` (`j < h − 1`)
belong to the ambient set.
-/

open Filter

namespace Erdos880

variable {h : ℕ}

/-! ### Monotonicity in the base set, and blocks inside the basis -/

theorem isSumOfAtMost_mono_set {A B : Set ℕ} {k n : ℕ} (hAB : A ⊆ B) (h : IsSumOfAtMost A k n) :
    IsSumOfAtMost B k n := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  exact ⟨m, fun a ha => hAB (hmA a ha), hcard, hsum⟩

theorem block_subset_basis (h n : ℕ) : block h n ⊆ basis h := Set.subset_iUnion (block h) n

/-! ### Local copies of the defining equations

The corresponding lemmas of `Construction.lean` are `private`, so we reprove them here. -/

private lemma scale_succ' (n : ℕ) :
    scale h (n + 1) = coeff h * (scale h n) ^ 2 + h * scale h n := rfl

private lemma mem_block_iff' {n a : ℕ} :
    a ∈ block h n ↔
      (∃ r, r < (scale h n) ^ 2 ∧ a = scale h n + r) ∨
        (∃ j, j < h - 1 ∧ a = scale h n + 2 ^ j * (scale h n) ^ 2) := Iff.rfl

private lemma two_le_two_pow' (hh : 3 ≤ h) : 2 ≤ 2 ^ (h - 2) := by
  have e : h - 2 = (h - 3) + 1 := by omega
  have h1 : 1 ≤ 2 ^ (h - 3) := Nat.one_le_two_pow
  rw [e, pow_succ]
  omega

private lemma coeff_add_one' (hh : 3 ≤ h) : coeff h + 1 = 3 * 2 ^ (h - 2) := by
  have h2 := two_le_two_pow' hh
  unfold coeff
  omega

private lemma two_pow_pred' (hh : 3 ≤ h) : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
  have e : h - 1 = (h - 2) + 1 := by omega
  rw [e, pow_succ]
  ring

/-- The interval part of a block. -/
private lemma interval_mem_block {n r : ℕ} (hr : r < (scale h n) ^ 2) :
    scale h n + r ∈ block h n :=
  mem_block_iff'.mpr (Or.inl ⟨r, hr, rfl⟩)

/-- The spikes of a block. -/
private lemma spike_mem_block {n j : ℕ} (hj : j < h - 1) :
    scale h n + 2 ^ j * (scale h n) ^ 2 ∈ block h n :=
  mem_block_iff'.mpr (Or.inr ⟨j, hj, rfl⟩)

/-! ### The combinatorial core -/

/-- Summing a family of spikes indexed by a finset of exponents. -/
private lemma sum_spikes (x : ℕ) (J : Finset ℕ) :
    (Multiset.map (fun j => x + 2 ^ j * x ^ 2) J.val).sum
      = J.card * x + (∑ j ∈ J, 2 ^ j) * x ^ 2 := by
  rw [← Finset.sum_eq_multiset_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_mul,
    smul_eq_mul]

/-- The heart of the coverage argument, stated for an arbitrary set `B` containing the interval
`[x, x + x²)` and the spikes `x + 2^j·x²` (`j < h − 1`). -/
private lemma isSumOfAtMost_of_bounds (hh : 3 ≤ h) (B : Set ℕ) {x m : ℕ} (hhx : h ≤ x)
    (hint : ∀ r, r < x ^ 2 → x + r ∈ B) (hspk : ∀ j, j < h - 1 → x + 2 ^ j * x ^ 2 ∈ B)
    (h1 : x ≤ m) (h2 : m < coeff h * x ^ 2 + h * x) :
    IsSumOfAtMost B h m := by
  have hx3 : 3 ≤ x := hh.trans hhx
  have hxsq : 0 < x ^ 2 := by positivity
  have hml : h * x ≤ x + x ^ 2 := by
    have hle : h * x ≤ x * x := Nat.mul_le_mul hhx le_rfl
    have hsq : x ^ 2 = x * x := sq x
    omega
  rcases Nat.lt_or_ge m (h * x) with hcase | hcase
  · -- `m` is a single element of the interval part.
    refine ⟨{m}, ?_, ?_, ?_⟩
    · intro a ha
      rw [Multiset.mem_singleton] at ha
      subst ha
      have hlt : a - x < x ^ 2 := by omega
      have heq : x + (a - x) = a := by omega
      rw [← heq]
      exact hint _ hlt
    · simp only [Multiset.card_singleton]
      omega
    · exact Multiset.sum_singleton m
  · -- `m = h·x + q·x² + r`; build a multiset of exactly `h` block elements.
    have hpow : 2 ≤ 2 ^ (h - 2) := two_le_two_pow' hh
    have hcp : coeff h + 1 = 3 * 2 ^ (h - 2) := coeff_add_one' hh
    have hpp : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := two_pow_pred' hh
    obtain ⟨y, hym⟩ : ∃ y, m = h * x + y := ⟨m - h * x, by omega⟩
    have hy : y < coeff h * x ^ 2 := by omega
    obtain ⟨q, r, hqr, hrlt, hqlt⟩ : ∃ q r, y = q * x ^ 2 + r ∧ r < x ^ 2 ∧ q < coeff h :=
      ⟨y / x ^ 2, y % x ^ 2, (Nat.div_add_mod' y (x ^ 2)).symm, Nat.mod_lt _ hxsq,
        (Nat.div_lt_iff_lt_mul hxsq).mpr hy⟩
    obtain ⟨e, q', hqe, hq'bnd, hebnd⟩ :
        ∃ e q', q = e * 2 ^ (h - 2) + q' ∧ q' + 2 ≤ 2 ^ (h - 1) ∧ e ≤ 1 := by
      by_cases hge : 2 ^ (h - 2) ≤ q
      · exact ⟨1, q - 2 ^ (h - 2), by omega, by omega, le_rfl⟩
      · exact ⟨0, q, by omega, by omega, Nat.zero_le _⟩
    obtain ⟨J, hJsub, hJsum, hJfull⟩ := exists_bits (h - 1) q' (by omega)
    have hJcard : J.card ≤ h - 2 := by
      have hle : J.card ≤ h - 1 := by
        simpa using Finset.card_le_card hJsub
      rcases Nat.lt_or_ge J.card (h - 1) with hlt | hge
      · omega
      · have hfull := hJfull (by omega)
        omega
    obtain ⟨d, hd⟩ : ∃ d, e + J.card + 1 + d = h := ⟨h - 1 - e - J.card, by omega⟩
    refine ⟨Multiset.replicate e (x + 2 ^ (h - 2) * x ^ 2)
        + Multiset.map (fun j => x + 2 ^ j * x ^ 2) J.val
        + ((x + r) ::ₘ Multiset.replicate d x), ?_, ?_, ?_⟩
    · -- every entry is an element of `B`
      intro a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · rcases Multiset.mem_add.mp ha with ha | ha
        · rw [Multiset.eq_of_mem_replicate ha]
          exact hspk (h - 2) (by omega)
        · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp ha
          have hjJ : j ∈ J := hj
          exact hspk j (by have := Finset.mem_range.mp (hJsub hjJ); omega)
      · rcases Multiset.mem_cons.mp ha with rfl | ha
        · exact hint r hrlt
        · rw [Multiset.eq_of_mem_replicate ha]
          simpa using hint 0 hxsq
    · -- there are exactly `h` entries
      simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_map,
        Multiset.card_cons]
      have hcv : Multiset.card J.val = J.card := rfl
      omega
    · -- the entries add up to `m`
      rw [Multiset.sum_add, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_cons,
        Multiset.sum_replicate, sum_spikes, smul_eq_mul, smul_eq_mul, hym, hqr, hqe, hJsum,
        ← hd]
      ring

/-- Every `m` with `x_n ≤ m < x_{n+1}` is a sum of at most `h` elements of block `n`. -/
theorem isSumOfAtMost_block (hh : 3 ≤ h) {n m : ℕ} (h1 : scale h n ≤ m) (h2 : m < scale h (n + 1)) :
    IsSumOfAtMost (block h n) h m :=
  isSumOfAtMost_of_bounds hh (block h n) (h_le_scale hh n) (fun _ hr => interval_mem_block hr)
    (fun _ hj => spike_mem_block hj) h1 (by rwa [← scale_succ' n])

theorem isSumOfAtMost_basis_of_le (hh : 3 ≤ h) {m : ℕ} (hm : h ≤ m) :
    IsSumOfAtMost (basis h) h m := by
  obtain ⟨n, hn1, hn2⟩ := exists_scale_interval hh hm
  exact isSumOfAtMost_mono_set (block_subset_basis h n) (isSumOfAtMost_block hh hn1 hn2)

/-- `A = basis h` is an asymptotic basis of order `h` (Erdős's "k or fewer" definition). -/
theorem basis_isAsymptoticBasis (hh : 3 ≤ h) : IsAsymptoticBasis (basis h) h :=
  Filter.eventually_atTop.2 ⟨h, fun _ hm => isSumOfAtMost_basis_of_le hh hm⟩

end Erdos880

#print axioms Erdos880.basis_isAsymptoticBasis
#print axioms Erdos880.isSumOfAtMost_block
