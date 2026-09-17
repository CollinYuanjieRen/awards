import Proof.Defs609

/-!
# Erdős Problem 609: the Erdős–Graham colouring of `K_{2^{n+1}}`

Erdős and Graham observed that the edges of `K_{2^n}` can be `n`-coloured so that no colour class
contains an odd cycle: identify the vertices with the binary strings of length `n` and colour the
edge `{x, y}` by the least position at which `x` and `y` differ.  Every edge of colour `i` joins
two vertices whose `i`-th binary digit differs, so the `i`-th digit is a proper `Bool`-colouring of
the colour class `i`; a graph with a proper `Bool`-colouring has no odd cycle.

The statement is phrased with `n + 1` colours on `2 ^ (n + 1)` vertices, so that it holds for every
`n : ℕ`: with `0` colours there is no colouring at all, since `Sym2 (Fin 1)` is nonempty.
-/

open SimpleGraph

namespace Erdos609

variable {n : ℕ}

/-- Distinct elements of `Fin (2 ^ (n + 1))` differ in some binary digit. -/
theorem exists_diff_bit {x y : Fin (2 ^ (n + 1))} (h : x ≠ y) :
    ∃ i, x.val.testBit i ≠ y.val.testBit i := by
  by_contra hcon
  refine h (Fin.ext (Nat.eq_of_testBit_eq fun i => ?_))
  by_contra hi
  exact hcon ⟨i, hi⟩

/-- The least binary digit in which two distinct elements of `Fin (2 ^ (n + 1))` differ is smaller
than `n + 1`: above that range both binary expansions have vanished. -/
theorem find_diff_bit_lt {x y : Fin (2 ^ (n + 1))} (h : x ≠ y) :
    Nat.find (exists_diff_bit h) < n + 1 := by
  by_contra hcon
  have hle : n + 1 ≤ Nat.find (exists_diff_bit h) := Nat.not_lt.mp hcon
  have hpow : (2 : ℕ) ^ (n + 1) ≤ 2 ^ Nat.find (exists_diff_bit h) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have hx : x.val.testBit (Nat.find (exists_diff_bit h)) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt hpow)
  have hy : y.val.testBit (Nat.find (exists_diff_bit h)) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.isLt hpow)
  exact Nat.find_spec (exists_diff_bit h) (by rw [hx, hy])

/-- The least binary digit in which `x` and `y` differ, as an element of `Fin (n + 1)`
(and `0` when `x = y`). -/
def firstDiff (x y : Fin (2 ^ (n + 1))) : Fin (n + 1) :=
  if h : x = y then 0 else ⟨Nat.find (exists_diff_bit h), find_diff_bit_lt h⟩

/-- Distinct `x` and `y` do differ in the binary digit `firstDiff x y`. -/
theorem testBit_firstDiff_ne {x y : Fin (2 ^ (n + 1))} (h : x ≠ y) :
    x.val.testBit (firstDiff x y : ℕ) ≠ y.val.testBit (firstDiff x y : ℕ) := by
  simp only [firstDiff, h, ↓reduceDIte]
  exact Nat.find_spec (exists_diff_bit h)

/-- `firstDiff` is symmetric, since "differing in digit `i`" is. -/
theorem firstDiff_comm (x y : Fin (2 ^ (n + 1))) : firstDiff x y = firstDiff y x := by
  by_cases h : x = y
  · rw [h]
  · have h' : y ≠ x := fun he => h he.symm
    simp only [firstDiff, h, h', ↓reduceDIte]
    refine Fin.ext (Nat.le_antisymm ?_ ?_)
    · exact Nat.find_le (Ne.symm (Nat.find_spec (exists_diff_bit h')))
    · exact Nat.find_le (Ne.symm (Nat.find_spec (exists_diff_bit h)))

/-- The **Erdős–Graham colouring** of the edges of `K_{2^{n+1}}` with `n + 1` colours: the edge
`{x, y}` is coloured by the least binary digit in which `x` and `y` differ. -/
def egColouring (n : ℕ) : Sym2 (Fin (2 ^ (n + 1))) → Fin (n + 1) :=
  Sym2.lift ⟨fun x y => firstDiff x y, fun x y => firstDiff_comm x y⟩

/-- Two vertices joined in the colour class `i` of the Erdős–Graham colouring differ in their
`i`-th binary digit. -/
theorem colourClass_adj_testBit {i : Fin (n + 1)} {x y : Fin (2 ^ (n + 1))}
    (h : (colourClass (egColouring n) i).Adj x y) :
    x.val.testBit (i : ℕ) ≠ y.val.testBit (i : ℕ) := by
  rw [colourClass_adj] at h
  obtain ⟨hne, hc⟩ := h
  simp only [egColouring, Sym2.lift_mk] at hc
  rw [← hc]
  exact testBit_firstDiff_ne hne

/-- **Erdős–Graham**: the edges of `K_{2^{n+1}}` can be `(n + 1)`-coloured so that no colour class
contains an odd cycle. -/
theorem exists_colouring_no_oddCycle (n : ℕ) :
    ∃ c : Sym2 (Fin (2 ^ (n + 1))) → Fin (n + 1), ∀ i, ¬ HasOddCycle (colourClass c i) :=
  ⟨egColouring n, fun _ =>
    not_hasOddCycle_of_coloring _ fun _ _ huv => colourClass_adj_testBit huv⟩

end Erdos609
