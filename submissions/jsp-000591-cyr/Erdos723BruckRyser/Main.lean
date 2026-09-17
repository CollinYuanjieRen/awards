import Mathlib

/-!
# Erdős Problem #723: Bruck–Ryser rules out projective planes of order `6` and `14`

Erdős asked whether the order of every finite projective plane must be a prime power (OPEN; not
addressed here).  The problem page records the Bruck–Ryser theorem — if a projective plane of
order `n` exists and `n ≡ 1` or `2 (mod 4)`, then `n` is a sum of two squares — and continues:
"For example, this rules out `n = 6` or `n = 14`."  This file proves the arithmetic behind that
example: `6 ≡ 2 (mod 4)` and `14 ≡ 2 (mod 4)`, and neither `6` nor `14` is a sum of two squares;
consequently, *assuming* the Bruck–Ryser theorem in exactly the shape of the formal-conjectures
statement `erdos_723.variants.bruck_ryser` (which is not proved here — it is an explicit
hypothesis of `erdos_723_bruck_ryser_rules_out_six_fourteen`), no finite projective plane has
order `6` or `14`.  The Bruck–Ryser theorem itself, the prime-power question, and the `n = 10`
computer search are not claimed.
-/

open Configuration

/-- `6` and `14` are `≡ 2 (mod 4)`. -/
theorem six_fourteen_modEq_two : 6 ≡ 2 [MOD 4] ∧ 14 ≡ 2 [MOD 4] := by
  exact ⟨by decide, by decide⟩

/-- `6` is not a sum of two squares. -/
theorem six_not_sum_two_squares : ¬ ∃ a b : ℕ, 6 = a ^ 2 + b ^ 2 := by
  rintro ⟨a, b, h⟩
  have ha : a ≤ 2 := by nlinarith
  have hb : b ≤ 2 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega

/-- `14` is not a sum of two squares. -/
theorem fourteen_not_sum_two_squares : ¬ ∃ a b : ℕ, 14 = a ^ 2 + b ^ 2 := by
  rintro ⟨a, b, h⟩
  have ha : a ≤ 3 := by nlinarith
  have hb : b ≤ 3 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega

/-- **Erdős #723, the page's example (arithmetic part)**: `6` and `14` are `≡ 2 (mod 4)` and not
sums of two squares, so the Bruck–Ryser theorem excludes them as orders of projective planes. -/
theorem erdos_723_six_fourteen_closed :
    (6 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 6 = a ^ 2 + b ^ 2) ∧
      (14 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 14 = a ^ 2 + b ^ 2) :=
  ⟨⟨six_fourteen_modEq_two.1, six_not_sum_two_squares⟩,
    ⟨six_fourteen_modEq_two.2, fourteen_not_sum_two_squares⟩⟩

/-- **The example as a consequence of Bruck–Ryser.**  *Assuming* the Bruck–Ryser theorem in the
shape of the formal-conjectures statement `erdos_723.variants.bruck_ryser` (hypothesis `hBR`; not
proved here), no finite projective plane has order `6` or `14`. -/
theorem erdos_723_bruck_ryser_rules_out_six_fourteen
    (hBR : ∀ {P L : Type} [Membership P L] [Fintype P] [Fintype L] (n : ℕ)
      (pp : ProjectivePlane P L), pp.order = n →
      (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2)
    {P L : Type} [Membership P L] [Fintype P] [Fintype L] (pp : ProjectivePlane P L) :
    pp.order ≠ 6 ∧ pp.order ≠ 14 := by
  refine ⟨fun h6 => ?_, fun h14 => ?_⟩
  · exact six_not_sum_two_squares (hBR 6 pp h6 (Or.inr six_fourteen_modEq_two.1))
  · exact fourteen_not_sum_two_squares (hBR 14 pp h14 (Or.inr six_fourteen_modEq_two.2))
