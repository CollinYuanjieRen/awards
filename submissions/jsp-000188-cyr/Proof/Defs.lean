import Mathlib

/-!
# Erdős problem #201 — definitions

This module fixes the finite-combinatorial vocabulary used for the scoped component of
Erdős problem #201 that this package formalises.

Finite sets of integers are Mathlib's `Finset ℤ`.  A `k`-term arithmetic progression is
required to have a *positive* common difference, so a progression really has `k` distinct
terms.

* `Erdos201.HasAP k S` — the finite set `S` contains a `k`-term arithmetic progression.
* `Erdos201.APFree k S` — the finite set `S` contains no `k`-term arithmetic progression.
* `Erdos201.apFreeMax k T` — the size of the largest `k`-AP-free subset of the finite set `T`.
* `Erdos201.R k N` — the problem page's `R_k(N)`: `apFreeMax k {1, …, N}`.
* `Erdos201.G k N` — the problem page's `G_k(N)`: the least value of `apFreeMax k T` over
  all `N`-element sets `T` of integers.

Two structural facts are also proved here: `Erdos201.apFreeMax_le_iff`, which unfolds
`apFreeMax` as a supremum, and `Erdos201.G_le_apFreeMax`, which unfolds `G` as an infimum.
-/

namespace Erdos201

/-- `HasAP k S` says that the finite set of integers `S` contains a `k`-term arithmetic
progression `a, a + d, …, a + (k-1)d` with positive common difference `d`. -/
def HasAP (k : ℕ) (S : Finset ℤ) : Prop := ∃ a d : ℤ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

/-- `APFree k S` says that the finite set of integers `S` contains no `k`-term arithmetic
progression with positive common difference. -/
def APFree (k : ℕ) (S : Finset ℤ) : Prop := ¬ HasAP k S

open Classical in
/-- `apFreeMax k T` is the size of the largest `k`-AP-free subset of the finite set of
integers `T`, i.e. the supremum of `S.card` over the `k`-AP-free subsets `S ⊆ T`.  The
filter uses classical decidability of `APFree`, hence the `noncomputable` marker. -/
noncomputable def apFreeMax (k : ℕ) (T : Finset ℤ) : ℕ :=
  (T.powerset.filter (fun S => APFree k S)).sup Finset.card

/-- `R k N` is the quantity `R_k(N)` of the problem page: the size of the largest subset of
`{1, …, N}` containing no `k`-term arithmetic progression. -/
noncomputable def R (k N : ℕ) : ℕ := apFreeMax k (Finset.Icc (1 : ℤ) N)

/-- `G k N` is the quantity `G_k(N)` of the problem page: the least `m` such that some set
of `N` integers has largest `k`-AP-free subset of size exactly `m`.  Equivalently, every set
of `N` integers contains a `k`-AP-free subset of size at least `G k N`, and this is optimal.
The infimum is attained because the values are natural numbers. -/
noncomputable def G (k N : ℕ) : ℕ := sInf {m : ℕ | ∃ T : Finset ℤ, T.card = N ∧ apFreeMax k T = m}

/-- (T4) `apFreeMax k T ≤ m` exactly when every `k`-AP-free subset of `T` has at most `m`
elements: `apFreeMax` really is the supremum of the sizes of the `k`-AP-free subsets. -/
theorem apFreeMax_le_iff (k : ℕ) (T : Finset ℤ) (m : ℕ) : apFreeMax k T ≤ m ↔ ∀ S ⊆ T, APFree k S → S.card ≤ m := by
  classical
  unfold apFreeMax
  rw [Finset.sup_le_iff]
  constructor
  · intro h S hST hfree
    exact h S (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hST, hfree⟩)
  · intro h S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact h S hS.1 hS.2

/-- Companion to `apFreeMax_le_iff`: every `k`-AP-free subset of `T` is at most as large as
`apFreeMax k T`. -/
theorem le_apFreeMax (k : ℕ) {T S : Finset ℤ} (hS : S ⊆ T) (hfree : APFree k S) :
    S.card ≤ apFreeMax k T := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hfree⟩)

/-- (T5) `G k N` is a lower bound for `apFreeMax k T` at every `N`-element set `T`: `G` is
the infimum of these values. -/
theorem G_le_apFreeMax (k N : ℕ) (T : Finset ℤ) (hT : T.card = N) : G k N ≤ apFreeMax k T :=
  Nat.sInf_le ⟨T, hT, rfl⟩

end Erdos201
