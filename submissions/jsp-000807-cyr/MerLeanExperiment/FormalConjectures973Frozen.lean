import Mathlib

/-!
# Frozen expanded Formal Conjectures statement for Erdős problem 973

This module imports no candidate proof.  It records the type of
`Erdos973.erdos_973` from `google-deepmind/formal-conjectures` at commit
`d5ba143cc2fafd48cc6d5b6320a3aab287c38df7`, after the pinned `answer`
elaborator expands the explicit term `answer(False)` to `False`.

Source file: `FormalConjectures/ErdosProblems/973.lean`
Source blob: `89150f5b681d48b4bf279647a092ca4e264c5f9f`
Source SHA-256: `a6474289c31ee3bbb08ebb954c9ed82bb4024597a3377023ad5e54485f2fd39a`

Together with the independently checked token correspondence to the pinned
source, this freeze is the source-exact external-statement boundary compiled
on the current project toolchain.  It does not claim that the native Formal
Conjectures package or an official comparator program was run.
-/

open Finset

namespace Erdos973.External

/-- The expanded proposition type of the pinned Formal Conjectures theorem.

The only source transformation is the pinned elaborator's expansion of the
explicit `answer(False)` term to `False`.  The notations `C > 1` and `n ≥ 2`
below are retained from the source text.
-/
def FormalConjectures973Expanded : Prop :=
  False ↔
    ∃ C : ℝ, C > 1 ∧
      ∀ n : ℕ, n ≥ 2 → ∃ z : ℕ → ℂ,
        z 1 = 1 ∧
        (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) ∧
        (∀ k ∈ Icc 2 (n + 1),
          ‖∑ i ∈ Icc 1 n, z i ^ k‖ < C ^ (-(n : ℝ)))

end Erdos973.External
