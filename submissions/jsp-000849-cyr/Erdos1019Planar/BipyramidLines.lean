import Erdos1019Planar.Separation

/-!
# Coordinates for the bipyramid drawing

The bipyramid over the `l`-cycle (`l ≥ 3`) has equatorial vertices `0, …, l-1` and two apices.
We draw equatorial vertex `i` at `(i, i²)` on the parabola `y = x²`, the inner apex at
`(1, 3/2)` (strictly inside the convex polygon spanned by the equator) and the outer apex at
`(0, -l²)` far below the parabola.  All non-crossing claims follow from the signs of a few
affine functionals at these points, recorded in this file:

* `chordFun i`: the line through `(i, i²)` and `(i+1, (i+1)²)`;
* `longFun l`: the line through `(0, 0)` and `(l-1, (l-1)²)`;
* `tangentFun i`: the tangent to the parabola at `(i, i²)`;
* `innerSpokeFun i`: the line through the inner apex and `(i, i²)`;
* `outerSpokeFun l i`: the line through the outer apex and `(i, i²)`.
-/

open Set

noncomputable section

namespace Bipyramid

/-- Equatorial vertex `i`, on the parabola `y = x²`. -/
def equator (i : ℕ) : ℝ × ℝ :=
  ((i : ℝ), (i : ℝ) ^ 2)

/-- The inner apex `(1, 3/2)`. -/
def innerApex : ℝ × ℝ :=
  (1, 3 / 2)

/-- The outer apex `(0, -l²)`. -/
def outerApex (l : ℕ) : ℝ × ℝ :=
  (0, -((l : ℝ) ^ 2))

/-- Positions of the vertices of the bipyramid `bipyramidGraph l` on `Fin l ⊕ Bool`:
equatorial vertices on the parabola, `inr false` the inner apex, `inr true` the outer apex. -/
def pos (l : ℕ) : Fin l ⊕ Bool → ℝ × ℝ
  | Sum.inl i => equator i
  | Sum.inr false => innerApex
  | Sum.inr true => outerApex l

/-- `y - (2i+1) x + i(i+1)`: vanishes at `(i, i²)` and `(i+1, (i+1)²)`. -/
abbrev chordFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun (-(2 * (i : ℝ) + 1)) 1 ((i : ℝ) * ((i : ℝ) + 1))

/-- `(l-1) x - y`: vanishes at `(0, 0)` and `(l-1, (l-1)²)`. -/
abbrev longFun (l : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((l : ℝ) - 1) (-1) 0

/-- `y - 2i x + i²`: the tangent line to the parabola at `(i, i²)`. -/
abbrev tangentFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun (-(2 * (i : ℝ))) 1 ((i : ℝ) ^ 2)

/-- The line through the inner apex `(1, 3/2)` and `(i, i²)`. -/
abbrev innerSpokeFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((i : ℝ) ^ 2 - 3 / 2) (-((i : ℝ) - 1)) (-(i : ℝ) ^ 2 + 3 / 2 * (i : ℝ))

/-- The line through the outer apex `(0, -l²)` and `(i, i²)`. -/
abbrev outerSpokeFun (l i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((i : ℝ) ^ 2 + (l : ℝ) ^ 2) (-(i : ℝ)) (-((i : ℝ) * (l : ℝ) ^ 2))

/-- The vertex positions are pairwise distinct. -/
theorem pos_injective (l : ℕ) (hl : 1 ≤ l) : Function.Injective (pos l) := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  intro x y hxy
  rcases x with i | b <;> rcases y with j | c
  · simp only [pos, equator, Prod.mk.injEq] at hxy
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hxy.1))
  · exfalso
    cases c <;> simp only [pos, equator, innerApex, outerApex, Prod.mk.injEq] at hxy
    · obtain ⟨h1, h2⟩ := hxy
      rw [h1] at h2
      norm_num at h2
    · obtain ⟨h1, h2⟩ := hxy
      rw [h1] at h2
      nlinarith
  · exfalso
    cases b <;> simp only [pos, equator, innerApex, outerApex, Prod.mk.injEq] at hxy
    · obtain ⟨h1, h2⟩ := hxy
      rw [← h1] at h2
      norm_num at h2
    · obtain ⟨h1, h2⟩ := hxy
      rw [← h1] at h2
      nlinarith
  · cases b <;> cases c <;> simp only [pos, innerApex, outerApex, Prod.mk.injEq] at hxy ⊢
    · norm_num at hxy
    · norm_num at hxy

/-! ### The chord line -/

/-- Value of the chord functional at an equatorial vertex. -/
theorem chordFun_equator (i j : ℕ) :
    chordFun i (equator j) = ((j : ℝ) - i) * ((j : ℝ) - i - 1) := by
  simp only [chordFun, lineFun, equator]
  ring

/-- The chord functional is nonnegative on the equator. -/
theorem chordFun_equator_nonneg (i j : ℕ) : 0 ≤ chordFun i (equator j) := by
  rw [chordFun_equator]
  rcases le_or_gt j i with h | h
  · have h' : (j : ℝ) ≤ i := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

/-- The chord functional is positive on the equator away from its two endpoints. -/
theorem chordFun_equator_pos (i j : ℕ) (hj : j ≠ i) (hj' : j ≠ i + 1) :
    0 < chordFun i (equator j) := by
  rw [chordFun_equator]
  rcases hj.lt_or_gt with h | h
  · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h2 : i + 2 ≤ j := by omega
    have h' : (i : ℝ) + 2 ≤ j := by exact_mod_cast h2
    exact mul_pos (by linarith) (by linarith)

/-- The chord functional vanishes at its first endpoint. -/
theorem chordFun_equator_self (i : ℕ) : chordFun i (equator i) = 0 := by
  simp only [chordFun, lineFun, equator]
  ring

/-- The chord functional vanishes at its second endpoint. -/
theorem chordFun_equator_succ (i : ℕ) : chordFun i (equator (i + 1)) = 0 := by
  simp only [chordFun, lineFun, equator]
  push_cast
  ring

/-- The chord functional is positive at the inner apex. -/
theorem chordFun_innerApex_pos (i : ℕ) : 0 < chordFun i innerApex := by
  simp only [chordFun, lineFun, innerApex]
  nlinarith [sq_nonneg ((i : ℝ) - 1 / 2)]

/-- The chord functional is negative at the outer apex. -/
theorem chordFun_outerApex_neg (i l : ℕ) (h : i + 1 < l) : chordFun i (outerApex l) < 0 := by
  simp only [chordFun, lineFun, outerApex]
  have h' : (i : ℝ) + 1 ≤ l := by exact_mod_cast h.le
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-! ### The long chord line -/

/-- Value of the long chord functional at an equatorial vertex. -/
theorem longFun_equator (l j : ℕ) :
    longFun l (equator j) = (j : ℝ) * ((l : ℝ) - 1 - j) := by
  simp only [longFun, lineFun, equator]
  ring

/-- The long chord functional is nonnegative on the equator. -/
theorem longFun_equator_nonneg (l j : ℕ) (hj : j < l) : 0 ≤ longFun l (equator j) := by
  rw [longFun_equator]
  have h' : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
  exact mul_nonneg (Nat.cast_nonneg j) (by linarith)

/-- The long chord functional is positive on the equator away from its two endpoints. -/
theorem longFun_equator_pos (l j : ℕ) (hj : j < l) (h0 : j ≠ 0) (h1 : j + 1 ≠ l) :
    0 < longFun l (equator j) := by
  rw [longFun_equator]
  have h2 : j + 2 ≤ l := by omega
  have h' : (j : ℝ) + 2 ≤ l := by exact_mod_cast h2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
  exact mul_pos hj0 (by linarith)

/-- The long chord functional vanishes at vertex `0`. -/
theorem longFun_equator_zero (l : ℕ) : longFun l (equator 0) = 0 := by
  simp [longFun, lineFun, equator]

/-- The long chord functional vanishes at vertex `l - 1`. -/
theorem longFun_equator_last (l : ℕ) (hl : 1 ≤ l) : longFun l (equator (l - 1)) = 0 := by
  rw [longFun_equator, Nat.cast_pred hl]
  ring

/-- The long chord functional is positive at the inner apex. -/
theorem longFun_innerApex_pos (l : ℕ) (hl : 3 ≤ l) : 0 < longFun l innerApex := by
  simp only [longFun, lineFun, innerApex]
  have h' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  linarith

/-- The long chord functional is positive at the outer apex. -/
theorem longFun_outerApex_pos (l : ℕ) (hl : 1 ≤ l) : 0 < longFun l (outerApex l) := by
  simp only [longFun, lineFun, outerApex]
  have h' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

/-! ### The tangent line -/

/-- Value of the tangent functional at an equatorial vertex. -/
theorem tangentFun_equator (i j : ℕ) : tangentFun i (equator j) = ((j : ℝ) - i) ^ 2 := by
  simp only [tangentFun, lineFun, equator]
  ring

/-- The tangent functional vanishes at its point of tangency. -/
theorem tangentFun_equator_self (i : ℕ) : tangentFun i (equator i) = 0 := by
  simp only [tangentFun, lineFun, equator]
  ring

/-- The tangent functional is positive at every other equatorial vertex. -/
theorem tangentFun_equator_pos (i j : ℕ) (h : j ≠ i) : 0 < tangentFun i (equator j) := by
  rw [tangentFun_equator]
  have h' : (j : ℝ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  positivity

/-- The tangent functional is positive at the inner apex. -/
theorem tangentFun_innerApex_pos (i : ℕ) : 0 < tangentFun i innerApex := by
  simp only [tangentFun, lineFun, innerApex]
  nlinarith [sq_nonneg ((i : ℝ) - 1)]

/-- The tangent functional is negative at the outer apex. -/
theorem tangentFun_outerApex_neg (i l : ℕ) (h : i < l) : tangentFun i (outerApex l) < 0 := by
  simp only [tangentFun, lineFun, outerApex]
  have h' : (i : ℝ) < l := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-! ### The inner spoke line -/

/-- The inner spoke functional vanishes at the inner apex. -/
theorem innerSpokeFun_innerApex (i : ℕ) : innerSpokeFun i innerApex = 0 := by
  simp only [innerSpokeFun, lineFun, innerApex]
  ring

/-- The inner spoke functional vanishes at its equatorial endpoint. -/
theorem innerSpokeFun_equator_self (i : ℕ) : innerSpokeFun i (equator i) = 0 := by
  simp only [innerSpokeFun, lineFun, equator]
  ring

/-- Value of the inner spoke functional at an equatorial vertex. -/
theorem innerSpokeFun_equator (i j : ℕ) :
    innerSpokeFun i (equator j) = ((i : ℝ) - j) * (((i : ℝ) - 1) * ((j : ℝ) - 1) + 1 / 2) := by
  simp only [innerSpokeFun, lineFun, equator]
  ring

/-- The inner spoke functional does not vanish at any other equatorial vertex. -/
theorem innerSpokeFun_equator_ne_zero (i j : ℕ) (h : j ≠ i) :
    innerSpokeFun i (equator j) ≠ 0 := by
  rw [innerSpokeFun_equator]
  have h1 : (i : ℝ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.symm)
  have h2 : ((i : ℝ) - 1) * ((j : ℝ) - 1) + 1 / 2 ≠ 0 := by
    intro hc
    have h3 : ((2 * (((i : ℤ) - 1) * ((j : ℤ) - 1)) + 1 : ℤ) : ℝ) = 0 := by
      push_cast
      linarith
    have h4 : (2 * (((i : ℤ) - 1) * ((j : ℤ) - 1)) + 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  exact mul_ne_zero h1 h2

/-! ### The outer spoke line -/

/-- The outer spoke functional vanishes at the outer apex. -/
theorem outerSpokeFun_outerApex (l i : ℕ) : outerSpokeFun l i (outerApex l) = 0 := by
  simp only [outerSpokeFun, lineFun, outerApex]
  ring

/-- The outer spoke functional vanishes at its equatorial endpoint. -/
theorem outerSpokeFun_equator_self (l i : ℕ) : outerSpokeFun l i (equator i) = 0 := by
  simp only [outerSpokeFun, lineFun, equator]
  ring

/-- Value of the outer spoke functional at an equatorial vertex. -/
theorem outerSpokeFun_equator (l i j : ℕ) :
    outerSpokeFun l i (equator j) = ((j : ℝ) - i) * ((l : ℝ) ^ 2 - (i : ℝ) * j) := by
  simp only [outerSpokeFun, lineFun, equator]
  ring

/-- The outer spoke functional is positive at equatorial vertices to the right of `i`. -/
theorem outerSpokeFun_equator_pos (l i j : ℕ) (hi : i < l) (hj : j < l) (h : i < j) :
    0 < outerSpokeFun l i (equator j) := by
  rw [outerSpokeFun_equator]
  have hi' : (i : ℝ) < l := by exact_mod_cast hi
  have hj' : (j : ℝ) < l := by exact_mod_cast hj
  have h' : (i : ℝ) < j := by exact_mod_cast h
  have hij : (i : ℝ) * j < (l : ℝ) ^ 2 := by
    rw [sq]
    exact mul_lt_mul'' hi' hj' (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  exact mul_pos (by linarith) (by linarith)

/-- The outer spoke functional is negative at equatorial vertices to the left of `i`. -/
theorem outerSpokeFun_equator_neg (l i j : ℕ) (hi : i < l) (hj : j < l) (h : j < i) :
    outerSpokeFun l i (equator j) < 0 := by
  rw [outerSpokeFun_equator]
  have hi' : (i : ℝ) < l := by exact_mod_cast hi
  have hj' : (j : ℝ) < l := by exact_mod_cast hj
  have h' : (j : ℝ) < i := by exact_mod_cast h
  have hij : (i : ℝ) * j < (l : ℝ) ^ 2 := by
    rw [sq]
    exact mul_lt_mul'' hi' hj' (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

end Bipyramid

end
