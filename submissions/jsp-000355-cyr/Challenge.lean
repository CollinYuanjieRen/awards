/-
Comparator-style challenge module for JSP-000355 / Erdős Problem #436 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
the `Proof` modules (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

open Filter

namespace Erdos436Challenge

/-- `r` is a quadratic residue modulo `p`: a nonzero square in `ZMod p`. -/
def IsQR (p r : ℕ) : Prop := (r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)

/-- `r ≥ 1` starts a run of two consecutive quadratic residues modulo `p`. -/
def IsRunStart (p r : ℕ) : Prop := 0 < r ∧ IsQR p r ∧ IsQR p (r + 1)

/-- Lehmer–Lehmer's `r(2,2,p)`: the least `r ≥ 1` with `r`, `r + 1` both quadratic residues
modulo `p` (as an infimum in `ℕ`; `0` if there is none). -/
noncomputable def runStart (p : ℕ) : ℕ := sInf {r : ℕ | IsRunStart p r}

/-- `Λ(2,2) = limsup_{p → ∞} r(2,2,p)` over the primes. -/
noncomputable def Lambda22 : ℕ := limsup runStart (atTop ⊓ 𝓟 {p : ℕ | p.Prime})

theorem lambda22_eq_nine : Lambda22 = 9 := by
  sorry

theorem runStart_le_nine (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : runStart p ≤ 9 := by
  sorry

theorem exists_prime_gt_runStart_eq_nine (N : ℕ) : ∃ p > N, p.Prime ∧ runStart p = 9 := by
  sorry

end Erdos436Challenge
