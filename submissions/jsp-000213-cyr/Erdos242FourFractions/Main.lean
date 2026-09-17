import Mathlib

/-!
# Erdős Problem #242 (Erdős–Straus): `4/n` is a sum of at most four distinct unit fractions

The Erdős–Straus conjecture asks whether for every `n > 2` there are distinct `x < y < z` with
`4/n = 1/x + 1/y + 1/z` (OPEN; not addressed here).  The problem page records: "The existence of
a representation of `4/n` as the sum of at most four distinct unit fractions follows trivially
from a greedy algorithm."  This file proves that remark for every `n > 2` (the problem's range;
`4/2 = 1 + 1/2 + 1/3 + 1/6` also works, but `4/1 = 4` is not such a sum).  The
formal-conjectures file for #242 states only the three-term conjecture, so the statement below
is ours.

Proof (greedy).  For `0 < a/b < 1` with `a ≥ 1`, let `q = ⌈b/a⌉`; then `1/q ≤ a/b < 1/(q − 1)`,
so `a/b − 1/q = (aq − b)/(bq)` has numerator `0 ≤ aq − b < a`, and the next denominator is larger
than `q`.  Starting from `4/n` with `n ≥ 3` (so `4/n < 2`; if `4/n ≥ 1` first subtract `1`, using
`n = 3` or `n = 4` explicitly), at most four steps reach `0`, the denominators strictly increase,
and the sum is `4/n`.
-/

/-- **The greedy step for unit fractions.**  Let `a`, `b` be positive naturals and set
`q = ⌈b/a⌉`.  Then `q > 0`, the remainder `a/b - 1/q` is again a fraction `a'/(b*q)` whose
numerator `a'` is a natural number strictly smaller than `a`, and `q` is the least natural
with `1/q ≤ a/b`, in the quantitative form `b/a ≤ q < b/a + 1`. -/
theorem greedy_step (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ q a' : ℕ, 0 < q ∧ a' < a ∧ (a : ℚ) / b - 1 / q = (a' : ℚ) / (b * q) ∧
      (b : ℚ) / a ≤ q ∧ (q : ℚ) < (b : ℚ) / a + 1 := by
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hx0 : (0 : ℚ) < (b : ℚ) / a := div_pos hb' ha'
  set q : ℕ := ⌈(b : ℚ) / a⌉₊
  have hle : (b : ℚ) / a ≤ (q : ℚ) := Nat.le_ceil _
  have hlt : (q : ℚ) < (b : ℚ) / a + 1 := Nat.ceil_lt_add_one hx0.le
  have hq0 : 0 < q := Nat.ceil_pos.mpr hx0
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq0
  -- `b ≤ a * q`
  have hble' : (b : ℚ) ≤ (a : ℚ) * q := by
    have := (div_le_iff₀ ha').mp hle
    linarith
  have hble : b ≤ a * q := by exact_mod_cast hble'
  -- `a * q < b + a`
  have hlt' : (a : ℚ) * q < (b : ℚ) + a := by
    have h := mul_lt_mul_of_pos_left hlt ha'
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt ha')] at h
    linarith
  have hltn : a * q < b + a := by exact_mod_cast hlt'
  refine ⟨q, a * q - b, hq0, by omega, ?_, hle, hlt⟩
  have hcast : ((a * q - b : ℕ) : ℚ) = (a : ℚ) * q - b := by
    push_cast [Nat.cast_sub hble]
    ring
  rw [hcast]
  field_simp

/-- The greedy algorithm, by strong induction on the numerator `a` (bounded by `k`):
for `0 < b` and `a ≤ b`, the fraction `a/b` is a sum of at most `a` distinct unit fractions,
all of whose denominators are at least `b/a`. -/
private theorem greedy_key : ∀ k a b : ℕ, a ≤ k → 0 < b → a ≤ b →
    ∃ S : Finset ℕ, (∀ s ∈ S, 0 < s) ∧ S.card ≤ a ∧ (∀ s ∈ S, (b : ℚ) / a ≤ (s : ℚ)) ∧
      (a : ℚ) / b = ∑ s ∈ S, (1 : ℚ) / s := by
  intro k
  induction k with
  | zero =>
      intro a b hak _ _
      obtain rfl : a = 0 := Nat.le_zero.mp hak
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
      intro a b hak hb hab
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact ⟨∅, by simp, by simp, by simp, by simp⟩
      obtain ⟨q, a', hq0, ha'a, heq, hbaq, _⟩ := greedy_step a b ha hb
      have hbq : 0 < b * q := Nat.mul_pos hb hq0
      have hbbq : b ≤ b * q := by nlinarith
      have ha'bq : a' ≤ b * q := by omega
      obtain ⟨S', hpos', hcard', hinv', hsum'⟩ := ih a' (b * q) (by omega) hbq ha'bq
      have ha_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
      have hb_pos : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
      have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq0
      -- every element of `S'` is `> q`, hence `q ∉ S'`
      have hgt : ∀ s ∈ S', (q : ℚ) < (s : ℚ) := by
        intro s hs
        rcases Nat.eq_zero_or_pos a' with rfl | ha'0
        · exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard') ▸ hs) (by simp)
        have ha'_pos : (0 : ℚ) < (a' : ℚ) := by exact_mod_cast ha'0
        have h1 := hinv' s hs
        push_cast at h1
        have h2 : (q : ℚ) < (b : ℚ) * q / a' := by
          rw [lt_div_iff₀ ha'_pos]
          have : (a' : ℚ) < (b : ℚ) := by
            have : a' < b := by omega
            exact_mod_cast this
          nlinarith
        linarith
      have hqnot : q ∉ S' := fun hmem => absurd (hgt q hmem) (lt_irrefl _)
      refine ⟨insert q S', ?_, ?_, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hq0
        · exact hpos' s hs
      · rw [Finset.card_insert_of_notMem hqnot]
        omega
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hbaq
        · rcases Nat.eq_zero_or_pos a' with rfl | ha'0
          · exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard') ▸ hs) (by simp)
          have ha'_pos : (0 : ℚ) < (a' : ℚ) := by exact_mod_cast ha'0
          have h1 := hinv' s hs
          push_cast at h1
          refine le_trans ?_ h1
          rw [div_le_div_iff₀ ha_pos ha'_pos]
          have h3 : (a' : ℚ) ≤ (a : ℚ) * q := by
            have : a' ≤ a * q := by nlinarith
            exact_mod_cast this
          nlinarith
      · rw [Finset.sum_insert hqnot, ← hsum']
        push_cast at heq ⊢
        linarith

/-- **Erdős #242, the page's trivial remark**: for every `n > 2`, `4/n` is the sum of at most four
distinct unit fractions (a finset of at most four positive integers whose reciprocals sum to
`4/n`). -/
theorem erdos_242_four_unit_fractions (n : ℕ) (hn : 2 < n) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 0 < s) ∧ S.card ≤ 4 ∧ (4 / n : ℚ) = ∑ s ∈ S, (1 : ℚ) / s := by
  rcases Nat.lt_or_ge n 4 with h | h
  · obtain rfl : n = 3 := by omega
    refine ⟨{1, 3}, ?_, ?_, ?_⟩
    · intro s hs
      fin_cases hs <;> norm_num
    · decide
    · norm_num
  · obtain ⟨S, hpos, hcard, -, hsum⟩ := greedy_key 4 4 n le_rfl (by omega) h
    refine ⟨S, hpos, hcard, ?_⟩
    rw [← hsum]
    norm_num

/-- The same statement in the offset form `n + 3` (no hypothesis), used as the graded root. -/
theorem erdos_242_four_unit_fractions_succ (n : ℕ) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 0 < s) ∧ S.card ≤ 4 ∧
      (4 / (n + 3 : ℕ) : ℚ) = ∑ s ∈ S, (1 : ℚ) / s :=
  erdos_242_four_unit_fractions (n + 3) (by omega)
