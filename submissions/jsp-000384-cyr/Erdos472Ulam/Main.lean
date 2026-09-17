import Mathlib

/-!
# Erdős Problem #472 (Ulam): the example `3, 5, 7, 11, 13, 17, …`

Given an initial finite sequence of primes `q₁ < ⋯ < q_m`, extend it by letting `q_{n+1}` be the
smallest prime of the form `q_n + q_i − 1` (`i ≤ n`).  Ulam asked whether some initial sequence
gives an infinite sequence (OPEN; not addressed here).  The problem page records: "For example if
we begin with `3, 5` then the sequence continues `3, 5, 7, 11, 13, 17, …`."  This file verifies that
example: with the rule formalized as `ulamNext` (the least prime among `q_n + q_i − 1`, or `0` if
there is none, i.e. the sequence stops), the next four terms after `3, 5` are `7, 11, 13, 17`.
There is no formal-conjectures statement for #472, so the definitions are ours.  Whether the
sequence starting `3, 5` is infinite is not claimed.
-/

/-- Ulam's rule: the next term after the finite sequence `l = [q₁, …, qₙ]` is the smallest prime of
the form `qₙ + qᵢ − 1` (`i ≤ n`); if there is none, the value is `0` (the sequence stops). -/
def ulamNext (l : List ℕ) : ℕ :=
  ((l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p)).min?.getD 0

/-- The sequence obtained from the initial sequence `init` by applying Ulam's rule `k` times. -/
def ulamExtend (init : List ℕ) : ℕ → List ℕ
  | 0 => init
  | k + 1 => ulamExtend init k ++ [ulamNext (ulamExtend init k)]

/-- `ulamNext` returns a prime of the required form whenever it is nonzero. -/
theorem ulamNext_spec (l : List ℕ) (h : ulamNext l ≠ 0) :
    (ulamNext l).Prime ∧ ∃ q ∈ l, ulamNext l = l.getLastD 0 + q - 1 := by
  rw [ulamNext] at h ⊢
  cases hL : ((l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p)).min? with
  | none => rw [hL] at h; simp at h
  | some m =>
    simp only [Option.getD_some]
    have hmem : m ∈ (l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p) :=
      List.min?_mem hL
    rw [List.mem_filter] at hmem
    obtain ⟨hmap, hprime⟩ := hmem
    obtain ⟨q, hq, hqm⟩ := List.mem_map.mp hmap
    exact ⟨by simpa using of_decide_eq_true hprime, q, hq, hqm.symm⟩

/-- `ulamNext` is the least prime of the required form. -/
theorem ulamNext_le (l : List ℕ) (p : ℕ) (hp : p.Prime) (hq : ∃ q ∈ l, p = l.getLastD 0 + q - 1) :
    ulamNext l ≤ p := by
  obtain ⟨q, hqmem, hqeq⟩ := hq
  have hpL : p ∈ (l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨q, hqmem, hqeq.symm⟩, by simpa using hp⟩
  rw [ulamNext]
  cases hL : ((l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p)).min? with
  | none => rw [List.min?_eq_none_iff] at hL; rw [hL] at hpL; simp at hpL
  | some m =>
    simp only [Option.getD_some]
    exact (List.min?_eq_some_iff.mp hL).2 p hpL

/-- **Erdős #472, the page's example**: starting from `3, 5`, Ulam's rule gives `7, 11, 13, 17`. -/
theorem erdos_472_example :
    ulamNext [3, 5] = 7 ∧ ulamNext [3, 5, 7] = 11 ∧ ulamNext [3, 5, 7, 11] = 13 ∧
      ulamNext [3, 5, 7, 11, 13] = 17 ∧ ulamExtend [3, 5] 4 = [3, 5, 7, 11, 13, 17] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩
