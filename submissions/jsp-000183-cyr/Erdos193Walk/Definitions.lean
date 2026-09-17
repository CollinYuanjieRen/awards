import Mathlib

/-!
# Erdős Problem 193: the Cambie–Kalviainen walk

Definitions of the explicit walk `P : ℕ → Fin 3 → ℤ` of arXiv:2609.01766 (S. Cambie and
E. Kalviainen, *An infinite small-step ℤ³-walk with no collinear triple*, 2026).

* `α n` is the binary digit sum of `n` reduced modulo `4`, defined by the recursion
  `α 0 = 0`, `α n = (n % 2 + α (n / 2)) % 4`.
* `u n = i ^ α n` is a Gaussian unit and `z n = ∑_{r < n} u r` is a nearest-neighbour walk in the
  Gaussian integers.
* `c k` are the corners `0, i, -1 + i, -1` of a unit square (indexed by `k % 4`).
* `w n = 2 z n + c (α n)`, `h n = 4 n + α n` and `P n = (Re w n, Im w n, h n)`.
* `stepSet` is the (finite) set of the sixteen possible displacements `P (n+1) - P n`.
-/

namespace Erdos193Walk

open Zsqrtd

/-- The Gaussian integers `ℤ[i] = Zsqrtd (-1)`. -/
abbrev G : Type := GaussianInt

/-- The imaginary unit `i`. -/
def I : G := ⟨0, 1⟩

/-- Binary digit sum modulo `4`. -/
def α : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((n + 1) % 2 + α ((n + 1) / 2)) % 4
termination_by n => n
decreasing_by all_goals simp_wf; omega

/-- The Gaussian unit `u n = i ^ α n`. -/
def u (n : ℕ) : G := I ^ α n

/-- The Gaussian-lattice walk `z n = ∑_{r < n} u r`. -/
def z (n : ℕ) : G := ∑ r ∈ Finset.range n, u r

/-- The corners `0, i, -1 + i, -1` of the unit square, indexed cyclically. -/
def c (k : ℕ) : G :=
  match k % 4 with
  | 0 => 0
  | 1 => I
  | 2 => ⟨-1, 1⟩
  | _ => -1

/-- Planar part of the walk. -/
def w (n : ℕ) : G := 2 * z n + c (α n)

/-- Height of the walk. -/
def h (n : ℕ) : ℤ := 4 * (n : ℤ) + (α n : ℤ)

/-- The walk in `ℤ³`. -/
def P (n : ℕ) : Fin 3 → ℤ := ![(w n).re, (w n).im, h n]

/-- The displacement determined by the tag pair `(j, k)`. -/
def step (jk : Fin 4 × Fin 4) : Fin 3 → ℤ :=
  ![(2 * I ^ (jk.1 : ℕ) + c jk.2 - c jk.1).re,
    (2 * I ^ (jk.1 : ℕ) + c jk.2 - c jk.1).im,
    4 + (jk.2 : ℤ) - (jk.1 : ℤ)]

/-- The finite set of possible displacements. -/
def stepSet : Set (Fin 3 → ℤ) := Set.range step

theorem stepSet_finite : stepSet.Finite := Set.finite_range step

end Erdos193Walk
