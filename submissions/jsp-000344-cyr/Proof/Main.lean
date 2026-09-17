import Mathlib

/-!
# Erdős problem #417 — the trivial inequality `V'(x) ≤ V(x)` for totient value counts

The Erdős problems page for problem #417 sets

* `V'(x) = #{φ(m) : 1 ≤ m ≤ x}`, the number of distinct values of Euler's totient
  function on the integers `1, …, x`, and
* `V(x) = #{φ(m) ≤ x : 1 ≤ m}`, the number of distinct totient values that are at
  most `x`,

and asks whether `lim V(x)/V'(x)` exists and whether it exceeds `1`; in [Er98] Erdős
suggests the limit may be infinite. Those questions are open. The page also records
the remark that **it is trivial that `V'(x) ≤ V(x)`**, and this package proves exactly
that remark: the set of totient values `φ(m)` with `1 ≤ m ≤ x` is contained in the set
of totient values that are `≤ x`, because `φ(m) ≤ m`.

Not claimed here: the existence of the limit of `V(x)/V'(x)`, whether it exceeds `1`,
and Erdős's suggestion that it is infinite (the questions of Erdős problem #417).

## Main statements

* `Erdos417.mem_totientValues` and `Erdos417.mem_totientValuesLE` unfold the two
  finsets to their membership conditions, so the definitions are transparent.
* `Erdos417.totientValues_subset` is the inclusion `{φ(m) : 1 ≤ m ≤ x} ⊆ {v ≤ x : v
  is a totient value}`.
* `Erdos417.V'_le_V` is the page's inequality `V'(x) ≤ V(x)`.
* `Erdos417.V'_le_V_real` restates it for a real argument `x` through `⌊x⌋₊`, the
  page's `x` being real.
-/

namespace Erdos417

/-- The set of totient values `φ(m)` for `1 ≤ m ≤ x`, i.e. the set counted by the
page's `V'(x)`. -/
def totientValues (x : ℕ) : Finset ℕ := (Finset.Icc 1 x).image Nat.totient

open Classical in
/-- The set of values `v ≤ x` that are of the form `φ(m)` for some `m ≥ 1`, i.e. the
set of distinct totient values `≤ x` counted by the page's `V(x)`. -/
noncomputable def totientValuesLE (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun v => ∃ m, 1 ≤ m ∧ Nat.totient m = v)

/-- `V' x` is the page's `V'(x) = #{φ(m) : 1 ≤ m ≤ x}`. -/
def V' (x : ℕ) : ℕ := (totientValues x).card

/-- `V x` is the page's `V(x) = #{φ(m) ≤ x : m ≥ 1}`, the number of distinct totient
values that are at most `x`. -/
noncomputable def V (x : ℕ) : ℕ := (totientValuesLE x).card

/-- Membership in `totientValues x`: `v` is a totient value of some `m` with
`1 ≤ m ≤ x`. -/
theorem mem_totientValues (x v : ℕ) :
    v ∈ totientValues x ↔ ∃ m, 1 ≤ m ∧ m ≤ x ∧ Nat.totient m = v := by
  simp only [totientValues, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨m, ⟨hm1, hmx⟩, hv⟩
    exact ⟨m, hm1, hmx, hv⟩
  · rintro ⟨m, hm1, hmx, hv⟩
    exact ⟨m, ⟨hm1, hmx⟩, hv⟩

/-- Membership in `totientValuesLE x`: `v ≤ x` and `v` is a totient value of some
`m ≥ 1`. -/
theorem mem_totientValuesLE (x v : ℕ) :
    v ∈ totientValuesLE x ↔ v ≤ x ∧ ∃ m, 1 ≤ m ∧ Nat.totient m = v := by
  classical
  simp only [totientValuesLE, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The inclusion behind the page's remark: every totient value of some `m ≤ x` is a
totient value that is itself `≤ x`, since `φ(m) ≤ m`. -/
theorem totientValues_subset (x : ℕ) : totientValues x ⊆ totientValuesLE x := by
  intro v hv
  rw [mem_totientValues] at hv
  obtain ⟨m, hm1, hmx, hv⟩ := hv
  rw [mem_totientValuesLE]
  refine ⟨?_, m, hm1, hv⟩
  calc v = Nat.totient m := hv.symm
    _ ≤ m := Nat.totient_le m
    _ ≤ x := hmx

/-- The page's trivial inequality: `V'(x) ≤ V(x)` for every `x`. -/
theorem V'_le_V (x : ℕ) : V' x ≤ V x :=
  Finset.card_le_card (totientValues_subset x)

/-- The page's inequality for a real argument `x`, read through `⌊x⌋₊`. -/
theorem V'_le_V_real (x : ℝ) : V' ⌊x⌋₊ ≤ V ⌊x⌋₊ :=
  V'_le_V _

end Erdos417
