import CameronErdos.Statement
import CameronErdos.Counting.Basic
import CameronErdos.CE.IntervalCount

/-!
# `Thm_Assembly`: from the exceptional-set bound to the Cameron–Erdős conjecture

This file performs the final assembly of Green's proof of the Cameron–Erdős conjecture
(`ref/green-cameron-erdos-0304058.pdf`).  Every sum-free set `A ⊆ [1, N]` falls into one
of three classes:

* `A` consists entirely of odd numbers — there are `2 ^ ⌈N/2⌉` such sets
  (`CameronErdos.lem_oddCount`);
* `A ⊆ [⌈(N+1)/3⌉, N]` lies in the top third — there are
  `intervalSumFreeCount N ≤ 200 · 2^{N/2}` such sets
  (`CameronErdos.intervalSumFreeCount_le_explicit`);
* `A` is *exceptional* (`CameronErdos.exceptional`) — this is the class that the
  container/granularization machinery of Green's paper bounds by `2^{(1/2 - c)N}`.

`CameronErdos.sumFreeCount_le_split` is the resulting union bound, and
`CameronErdos.cameronErdos_of_exceptional_bound` turns any eventual bound
`#(exceptional N) ≤ 2^{N/2}` into the frozen root `CameronErdos.CameronErdosStatement`.
-/

open Finset

namespace CameronErdos

/-! ## The exceptional class -/

/-- The *exceptional* sum-free subsets of `[1, N]`: those that are neither all-odd nor
contained in the top two-thirds interval `[⌈(N+1)/3⌉, N]`. -/
def exceptional (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun A => IsSumFree A ∧ ¬ (∀ a ∈ A, Odd a) ∧ ¬ (A ⊆ Finset.Icc (topThird N) N))

lemma mem_exceptional {N : ℕ} {A : Finset ℕ} :
    A ∈ exceptional N ↔ A ⊆ Finset.Icc 1 N ∧ IsSumFree A ∧ ¬ (∀ a ∈ A, Odd a) ∧
      ¬ (A ⊆ Finset.Icc (topThird N) N) := by
  simp only [exceptional, Finset.mem_filter, Finset.mem_powerset]

/-! ## The trivial bound `f(N) ≤ 2^N` -/

/-- Every sum-free subset of `[1, N]` is in particular a subset of `[1, N]`, so
`f(N) ≤ 2^N`. -/
theorem sumFreeCount_le_two_pow (N : ℕ) : sumFreeCount N ≤ 2 ^ N := by
  have h : sumFreeCount N ≤ #((Finset.Icc 1 N).powerset) :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [Finset.card_powerset, Nat.card_Icc] using h

/-! ## The three-way union bound -/

/-- **The `Thm_Assembly` split.**  Every sum-free `A ⊆ [1, N]` is all-odd, or contained
in `[⌈(N+1)/3⌉, N]`, or exceptional; hence
`f(N) ≤ 2^{⌈N/2⌉} + T(N) + #(exceptional N)`. -/
theorem sumFreeCount_le_split (N : ℕ) :
    sumFreeCount N ≤ 2 ^ ((N + 1) / 2) + intervalSumFreeCount N + #(exceptional N) := by
  set O : Finset (Finset ℕ) := {x ∈ Finset.Icc 1 N | Odd x}.powerset with hO
  set I : Finset (Finset ℕ) := (Finset.Icc (topThird N) N).powerset.filter IsSumFree with hI
  have hsub : (Finset.Icc 1 N).powerset.filter IsSumFree ⊆ (O ∪ I) ∪ exceptional N := by
    intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    obtain ⟨hAsub, hAsf⟩ := hA
    by_cases hodd : ∀ a ∈ A, Odd a
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [hO, Finset.mem_powerset]
      intro a ha
      exact Finset.mem_filter.mpr ⟨hAsub ha, hodd a ha⟩
    · by_cases hint : A ⊆ Finset.Icc (topThird N) N
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [hI, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hint, hAsf⟩
      · exact Finset.mem_union_right _ (mem_exceptional.mpr ⟨hAsub, hAsf, hodd, hint⟩)
  have hOcard : #O = 2 ^ ((N + 1) / 2) := by rw [hO]; exact (lem_oddCount N).2.1
  have hIcard : #I = intervalSumFreeCount N := by rw [hI]; rfl
  calc sumFreeCount N = #((Finset.Icc 1 N).powerset.filter IsSumFree) := rfl
    _ ≤ #((O ∪ I) ∪ exceptional N) := Finset.card_le_card hsub
    _ ≤ #(O ∪ I) + #(exceptional N) := Finset.card_union_le _ _
    _ ≤ (#O + #I) + #(exceptional N) := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = 2 ^ ((N + 1) / 2) + intervalSumFreeCount N + #(exceptional N) := by
        rw [hOcard, hIcard]

/-! ## Real-analytic helpers -/

private lemma rpow_half_le_two : (2:ℝ) ^ ((1:ℝ)/2) ≤ 2 := by
  calc (2:ℝ) ^ ((1:ℝ)/2) ≤ (2:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

private lemma rpow_half_sq (N : ℕ) :
    (2:ℝ) ^ ((N:ℝ)/2) * (2:ℝ) ^ ((N:ℝ)/2) = (2:ℝ) ^ (N : ℕ) := by
  rw [← Real.rpow_add (by norm_num)]
  have h : (N:ℝ)/2 + (N:ℝ)/2 = ((N : ℕ) : ℝ) := by ring
  rw [h, Real.rpow_natCast]

/-- `2^{⌈N/2⌉} ≤ √2 · 2^{N/2} ≤ 2 · 2^{N/2}`. -/
private lemma two_pow_ceil_half_le (N : ℕ) :
    (2:ℝ) ^ ((N + 1) / 2) ≤ (2:ℝ) ^ ((N:ℝ)/2) * 2 := by
  have hk : 2 * ((N + 1) / 2) ≤ N + 1 := by omega
  have hkR : (((N + 1) / 2 : ℕ) : ℝ) ≤ (N:ℝ)/2 + 1/2 := by
    have h2 : ((2 * ((N + 1) / 2) : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hk
    push_cast at h2
    linarith
  have hposr : (0:ℝ) ≤ (2:ℝ) ^ ((N : ℝ) / 2) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc (2:ℝ) ^ ((N + 1) / 2) = (2:ℝ) ^ ((((N + 1) / 2 : ℕ)) : ℝ) :=
        (Real.rpow_natCast 2 _).symm
    _ ≤ (2:ℝ) ^ ((N : ℝ) / 2 + 1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hkR
    _ = (2:ℝ) ^ ((N : ℝ) / 2) * (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_add (by norm_num) _ _
    _ ≤ (2:ℝ) ^ ((N : ℝ) / 2) * 2 := mul_le_mul_of_nonneg_left rpow_half_le_two hposr

/-! ## `Thm_Assembly` -/

/-- **`Thm_Assembly`.**  Any eventual bound `#(exceptional N) ≤ 2^{N/2}` on the
exceptional class yields the Cameron–Erdős conjecture `f(n)^2 ≤ C · 2^n`. -/
theorem cameronErdos_of_exceptional_bound
    (h : ∀ᶠ N : ℕ in Filter.atTop, (#(exceptional N) : ℝ) ≤ 2 ^ ((N : ℝ) / 2)) :
    CameronErdosStatement := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨41209 + 4 ^ N₀, by positivity, ?_⟩
  intro N
  rcases lt_or_ge N N₀ with hlt | hge
  · -- small `N`: the trivial bound `f(N) ≤ 2^N` suffices
    have h1 : sumFreeCount N ≤ 2 ^ N := sumFreeCount_le_two_pow N
    have h2 : sumFreeCount N ^ 2 ≤ 4 ^ N := by
      calc sumFreeCount N ^ 2 ≤ (2 ^ N) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 4 ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h3 : (4:ℕ) ^ N ≤ 4 ^ N₀ := Nat.pow_le_pow_right (by norm_num) (le_of_lt hlt)
    have h4 : (1:ℕ) ≤ 2 ^ N := Nat.one_le_two_pow
    calc sumFreeCount N ^ 2 ≤ 4 ^ N₀ := h2.trans h3
      _ ≤ 41209 + 4 ^ N₀ := Nat.le_add_left _ _
      _ = (41209 + 4 ^ N₀) * 1 := (Nat.mul_one _).symm
      _ ≤ (41209 + 4 ^ N₀) * 2 ^ N := Nat.mul_le_mul_left _ h4
  · -- large `N`: the three-way split
    have hexc := hN₀ N hge
    have hint := intervalSumFreeCount_le_explicit N
    have hsplitR : (sumFreeCount N : ℝ)
        ≤ (2:ℝ) ^ ((N + 1) / 2) + (intervalSumFreeCount N : ℝ) + (#(exceptional N) : ℝ) := by
      exact_mod_cast sumFreeCount_le_split N
    have hpow := two_pow_ceil_half_le N
    have hfin : (sumFreeCount N : ℝ) ≤ 203 * (2:ℝ) ^ ((N:ℝ)/2) := by linarith
    have hnn : (0:ℝ) ≤ (sumFreeCount N : ℝ) := Nat.cast_nonneg _
    have hsq : (sumFreeCount N : ℝ) ^ 2 ≤ 41209 * (2:ℝ) ^ (N : ℕ) := by
      calc (sumFreeCount N : ℝ) ^ 2 ≤ (203 * (2:ℝ) ^ ((N:ℝ)/2)) ^ 2 := by
            gcongr
        _ = 41209 * ((2:ℝ) ^ ((N:ℝ)/2) * (2:ℝ) ^ ((N:ℝ)/2)) := by ring
        _ = 41209 * (2:ℝ) ^ (N : ℕ) := by rw [rpow_half_sq]
    have hsqN : sumFreeCount N ^ 2 ≤ 41209 * 2 ^ N := by exact_mod_cast hsq
    calc sumFreeCount N ^ 2 ≤ 41209 * 2 ^ N := hsqN
      _ ≤ (41209 + 4 ^ N₀) * 2 ^ N := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-! ## Axiom audit -/

#print axioms mem_exceptional
#print axioms sumFreeCount_le_two_pow
#print axioms sumFreeCount_le_split
#print axioms rpow_half_le_two
#print axioms rpow_half_sq
#print axioms two_pow_ceil_half_le
#print axioms cameronErdos_of_exceptional_bound

end CameronErdos
