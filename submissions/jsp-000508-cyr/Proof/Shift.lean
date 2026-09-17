import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise

/-!
# Erdős Problem 627: the shift graph

Tutte and Zykov proved independently that for every `k` there is a finite graph with clique number
`2` (that is, triangle-free and containing an edge) and chromatic number `k`.  This file sets up
the standard witness, the **shift graph**.

The vertices of the shift graph on `{0, …, N-1}` are the ordered pairs `(i, j)` with `i < j`, and
`(i, j)` is joined to `(j, l)`.  Three mutually adjacent pairs would force `i < j < l < i`, so the
shift graph is triangle-free.

Taking `N = 2 ^ k` it can be coloured with `k` colours: colour the vertex `(i, j)` by the position
`topDiff i j` of the **highest** binary digit in which `i` and `j` differ.  Since `i < j`, that
digit of `i` is `0` and that digit of `j` is `1`; so for adjacent vertices `(i, j)` and `(j, l)`
the common entry `j` would have to carry both a `1` (coming from `(i, j)`) and a `0` (coming from
`(j, l)`) in the same position, which is impossible.
-/

namespace Erdos627

/-- The vertices of the shift graph on `{0, …, N-1}`: ordered pairs `(i, j)` with `i < j`. -/
def ShiftVertex (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The shift graph has finitely many vertices: they form a decidable subtype of `Fin N × Fin N`. -/
instance instFintypeShiftVertex (N : ℕ) : Fintype (ShiftVertex N) :=
  Subtype.fintype (fun p : Fin N × Fin N => p.1 < p.2)

/-- Equality of shift-graph vertices is decidable. -/
instance instDecidableEqShiftVertex (N : ℕ) : DecidableEq (ShiftVertex N) :=
  fun p q => decidable_of_iff (p.1 = q.1) Subtype.ext_iff.symm

/-- The shift graph: `(i, j)` is adjacent to `(j, l)` (in either order). -/
def shiftGraph (N : ℕ) : SimpleGraph (ShiftVertex N) :=
  SimpleGraph.fromRel (fun p q => p.1.2 = q.1.1)

/-- Adjacency in the shift graph, unfolded. -/
theorem shiftGraph_adj {N : ℕ} {p q : ShiftVertex N} :
    (shiftGraph N).Adj p q ↔ p ≠ q ∧ (p.1.2 = q.1.1 ∨ q.1.2 = p.1.1) :=
  SimpleGraph.fromRel_adj _ p q

/-- The shift graph is triangle-free: three mutually adjacent pairs would force `i < j < l < i`. -/
theorem shiftGraph_cliqueFree (N : ℕ) : (shiftGraph N).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨p, q, r, hpq, hpr, hqr, -⟩ := hs
  rw [shiftGraph_adj] at hpq hpr hqr
  obtain ⟨-, hpq⟩ := hpq
  obtain ⟨-, hpr⟩ := hpr
  obtain ⟨-, hqr⟩ := hqr
  have hp : p.1.1.val < p.1.2.val := p.2
  have hq : q.1.1.val < q.1.2.val := q.2
  have hr : r.1.1.val < r.1.2.val := r.2
  rcases hpq with h1 | h1 <;> rcases hpr with h2 | h2 <;> rcases hqr with h3 | h3 <;>
    simp only [Fin.ext_iff] at h1 h2 h3 <;> omega

/-- The position of the highest binary digit in which `i` and `j` differ. -/
def topDiff (i j : ℕ) : ℕ := Nat.log 2 (i ^^^ j)

/-- For `i ≠ j` the binary digit `topDiff i j` of `i ^^^ j` is set. -/
theorem testBit_xor_topDiff {i j : ℕ} (h : i ≠ j) :
    (i ^^^ j).testBit (topDiff i j) = true := by
  have hx0 : i ^^^ j ≠ 0 := Nat.xor_ne_zero_iff.mpr h
  have hlow : 2 ^ topDiff i j ≤ i ^^^ j := Nat.pow_log_le_self 2 hx0
  have hhigh : i ^^^ j < 2 ^ (topDiff i j + 1) := Nat.lt_pow_succ_log_self (b := 2) (by omega) (i ^^^ j)
  by_contra hcon
  have hfalse : (i ^^^ j).testBit (topDiff i j) = false := by
    simpa using hcon
  have hlt : i ^^^ j < 2 ^ topDiff i j := by
    refine Nat.lt_of_testBit (topDiff i j) hfalse Nat.testBit_two_pow_self ?_
    intro b hb
    have h1 : (i ^^^ j).testBit b = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hhigh (Nat.pow_le_pow_right (by omega) hb))
    have h2 : (2 ^ topDiff i j).testBit b = false :=
      Nat.testBit_two_pow_of_ne (Nat.ne_of_lt hb)
    rw [h1, h2]
  omega

/-- Above `topDiff i j`, the numbers `i` and `j` have the same binary digits. -/
theorem testBit_eq_of_topDiff_lt {i j b : ℕ} (hb : topDiff i j < b) :
    i.testBit b = j.testBit b := by
  have hhigh : i ^^^ j < 2 ^ (topDiff i j + 1) := Nat.lt_pow_succ_log_self (b := 2) (by omega) (i ^^^ j)
  have hf : (i ^^^ j).testBit b = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hhigh (Nat.pow_le_pow_right (by omega) hb))
  rw [Nat.testBit_xor] at hf
  by_contra hne
  rw [Bool.xor_iff_ne.mpr hne] at hf
  simp at hf

/-- If `i < j` then at the highest differing binary digit `i` carries a `0` and `j` carries a `1`.
-/
theorem testBit_topDiff (i j : ℕ) (hij : i < j) :
    i.testBit (topDiff i j) = false ∧ j.testBit (topDiff i j) = true := by
  have hne : i ≠ j := Nat.ne_of_lt hij
  have hx := testBit_xor_topDiff hne
  rw [Nat.testBit_xor] at hx
  have hdiff : i.testBit (topDiff i j) ≠ j.testBit (topDiff i j) := Bool.xor_iff_ne.mp hx
  cases h1 : i.testBit (topDiff i j)
  · refine ⟨rfl, ?_⟩
    cases h2 : j.testBit (topDiff i j)
    · exact absurd (h1.trans h2.symm) hdiff
    · rfl
  · exfalso
    have h2 : j.testBit (topDiff i j) = false := by
      cases h2 : j.testBit (topDiff i j)
      · rfl
      · exact absurd (h1.trans h2.symm) hdiff
    have hji : j < i :=
      Nat.lt_of_testBit (topDiff i j) h2 h1 fun b hb => (testBit_eq_of_topDiff_lt hb).symm
    omega

/-- Distinct numbers below `2 ^ k` differ in a binary digit of position `< k`. -/
theorem topDiff_lt {i j k : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hne : i ≠ j) :
    topDiff i j < k :=
  Nat.log_lt_of_lt_pow (Nat.xor_ne_zero_iff.mpr hne) (Nat.xor_lt_two_pow hi hj)

/-- The colouring of the shift graph on `2 ^ k` points with `k` colours: the vertex `(i, j)` gets
the position of the highest binary digit in which `i` and `j` differ. -/
def shiftColour (k : ℕ) (p : ShiftVertex (2 ^ k)) : Fin k :=
  ⟨topDiff p.1.1.val p.1.2.val,
    topDiff_lt p.1.1.isLt p.1.2.isLt (Nat.ne_of_lt (show p.1.1.val < p.1.2.val from p.2))⟩

/-- `shiftColour` is a proper colouring: adjacent vertices share an endpoint, which would have to
carry both a `1` and a `0` in the same binary position. -/
theorem shiftColour_valid {k : ℕ} {p q : ShiftVertex (2 ^ k)}
    (h : (shiftGraph (2 ^ k)).Adj p q) : shiftColour k p ≠ shiftColour k q := by
  rw [shiftGraph_adj] at h
  obtain ⟨-, hr⟩ := h
  intro hcol
  have hc : topDiff p.1.1.val p.1.2.val = topDiff q.1.1.val q.1.2.val := congrArg Fin.val hcol
  obtain ⟨hp0, hp1⟩ :=
    testBit_topDiff p.1.1.val p.1.2.val (show p.1.1.val < p.1.2.val from p.2)
  obtain ⟨hq0, hq1⟩ :=
    testBit_topDiff q.1.1.val q.1.2.val (show q.1.1.val < q.1.2.val from q.2)
  rcases hr with hr | hr
  · have hval : p.1.2.val = q.1.1.val := congrArg Fin.val hr
    rw [hc, hval] at hp1
    rw [hp1] at hq0
    simp at hq0
  · have hval : q.1.2.val = p.1.1.val := congrArg Fin.val hr
    rw [hc, ← hval] at hp0
    rw [hq1] at hp0
    simp at hp0

/-- **Upper bound**: the shift graph on `2 ^ k` points is `k`-colourable. -/
theorem shiftGraph_colorable (k : ℕ) : (shiftGraph (2 ^ k)).Colorable k :=
  ⟨SimpleGraph.Coloring.mk (shiftColour k) fun {_ _} h => shiftColour_valid h⟩

end Erdos627
