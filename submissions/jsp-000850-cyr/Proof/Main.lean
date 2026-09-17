import Proof.Defs

/-!
# Erdős problem #1020 — the trivial range `n < rk`

The problem page for Erdős #1020 states the Erdős matching conjecture and then records, under
"small `n`", that *the conjecture is trivially true if `n < kr`*. This module formalises the
elementary content of that remark, in the form in which it is actually true.

If `M` is a family of `k` pairwise disjoint `r`-element subsets of an `n`-element vertex set, then
its union has exactly `rk` elements, so `rk ≤ n`. Hence when `n < rk` no `r`-uniform hypergraph on
`n` vertices has `k` independent edges (`not_hasMatching_of_lt`). Consequently *every* family of
`r`-subsets is admissible, and the extremal one is the family of all of them, so the true value in
this range is

`f(n; r, k) = C(n, r)`

(`f_eq_choose_of_lt`, and `not_exists_lt_and_ne` in negated form). That is what this package
proves.

Not claimed here: the Erdős matching conjecture of Erdős problem #1020 for `n ≥ rk` (the Kleitman,
Frankl and Kolupaev–Kupavskii ranges), Frankl's bound `f(n; r, k) ≤ (k − 1) C(n − 1, r − 1)`, and
the page's displayed formula in the range `n < rk`, which is not asserted here (with `f` defined on
`n` vertices it fails for `n < rk − 1` and `k ≥ 2`, e.g. `r = 3`, `k = 2`, `n = 4`; at `n = rk − 1` it
agrees with `C(n, r)`).
-/

namespace Erdos1020

/-- (T3) The combinatorial core: `k` pairwise disjoint `r`-element edges need `rk` vertices, so on
fewer than `rk` vertices no `r`-uniform hypergraph has `k` independent edges. -/
theorem not_hasMatching_of_lt (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (h : n < r * k) : ¬ HasMatching k H := by
  rintro ⟨M, hMH, hMk, hdisj⟩
  have hbiUnion : (M.biUnion id).card = ∑ e ∈ M, (id e).card := Finset.card_biUnion hdisj
  have hsum : ∑ e ∈ M, (id e).card = M.card * r :=
    Finset.sum_const_nat fun e he => hH e (hMH he)
  have hle : (M.biUnion id).card ≤ n := by
    have hu : (M.biUnion id).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    simpa using hu
  rw [hbiUnion, hsum, hMk] at hle
  exact absurd h (Nat.not_lt.2 (by rw [Nat.mul_comm]; exact hle))

/-- (T2) The true value of `f(n; r, k)` in the trivial range: for `n < rk` every `r`-uniform
hypergraph on `n` vertices is matching-free, so the maximum is attained by the family of all
`r`-subsets and equals `C(n, r)`. -/
theorem f_eq_choose_of_lt (n r k : ℕ) (h : n < r * k) : f n r k = n.choose r := by
  classical
  refine le_antisymm (f_le_choose n r k) ?_
  have huniform : IsUniform r ((Finset.univ : Finset (Fin n)).powersetCard r) :=
    fun _e he => (Finset.mem_powersetCard.1 he).2
  have hcard : ((Finset.univ : Finset (Fin n)).powersetCard r).card = n.choose r := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  calc n.choose r = ((Finset.univ : Finset (Fin n)).powersetCard r).card := hcard.symm
    _ ≤ f n r k :=
        card_le_f n r k _ huniform (not_hasMatching_of_lt n r k _ huniform h)

/-- (T1) The audited root, in negated form: there is no `n, r, k` with `n < rk` whose value
`f(n; r, k)` differs from `C(n, r)`. -/
theorem not_exists_lt_and_ne (n r k : ℕ) : ¬ (n < r * k ∧ f n r k ≠ n.choose r) :=
  fun ⟨h, hne⟩ => hne (f_eq_choose_of_lt n r k h)

end Erdos1020
