/-
JSP-000991: V_3(8) = 0.

There is a 2-colouring of {1, ..., 8} containing no monochromatic
3-term arithmetic progression.  The witness colours {2,4,5,7} with
colour `true` and {1,3,6,8} with colour `false`.

Only the exact boundary value V_3(8) = 0 is formalised here; the
asymptotic constant of Graham's problem is NOT claimed.
-/
import Mathlib

namespace MonoAP

/-- The 2-colouring: true (colour B) exactly on {2,4,5,7}. -/
def col (n : ℕ) : Bool := n == 2 || n == 4 || n == 5 || n == 7

/-- No 3-term arithmetic progression inside `{1, ..., 8}` is monochromatic
for `col`.  There are only `8 * 8` pairs `(a, d)` to inspect (of which `12`
give a progression that actually fits inside the interval), so the statement
is decided by evaluation. -/
theorem no_mono_3ap :
    ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (col a = col (a + d) ∧ col (a + d) = col (a + 2 * d)) := by
  decide

/-- `V_3(8) = 0`: some 2-colouring of `{1, ..., 8}` has no monochromatic
3-term arithmetic progression. -/
theorem exists_2col_no_mono_3ap :
    ∃ c : ℕ → Bool, ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (c a = c (a + d) ∧ c (a + d) = c (a + 2 * d)) :=
  ⟨col, no_mono_3ap⟩

end MonoAP

#print axioms MonoAP.no_mono_3ap
#print axioms MonoAP.exists_2col_no_mono_3ap
