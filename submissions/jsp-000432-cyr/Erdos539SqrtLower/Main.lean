import Mathlib

/-!
# Erdős Problem #539: the lower bound `h(n) ≫ √n` (Erdős–Szemerédi)

Let `h(n)` be maximal such that for every set `A ⊆ ℕ` of size `n` the set `{a/(a,b) : a, b ∈ A}`
has size at least `h(n)`.  Erdős asked to estimate `h(n)` (OPEN; known
`√n ≪ h(n) ≪ e^{O(√log n)} √n`).  The problem page records the Erdős–Szemerédi lower bound
`n^{1/2} ≪ h(n)`.  This file proves it in the exact shape of the formal-conjectures statement
`Erdos539.erdos_539.variants.sq_isBigO` (tagged "research solved" with `sorry`), with the
definitions `IsCofactorLowerBound` and `cofactorThreshold` copied verbatim.

Proof.  For `A` of size `n` let `I` be the set of cofactors `a/(a,b)`.  The map
`(a, b) ↦ (a/(a,b), b/(a,b))` sends `A × A` into `I × I` with fibres of size at most `n` (the
pair is determined by `a` when `a/(a,b) ≠ 0`, i.e. `a ≠ 0`, since then `b = (a / u) · v`; the
only pair with `a = 0` and a given `v` is determined by `b`), so `n² ≤ n · |I|²` and `|I| ≥ √n`.
Hence `⌈√n⌉ ≤ h(n)`; the set of cofactor lower bounds is bounded by `n²`, so the supremum is a
genuine maximum.  The upper bounds and the order of `h(n)` are not addressed.
-/

open Filter
open scoped Asymptotics Finset

/-- We say that `m` is a cofactor lower bound for a given `n` if, for every set `A` of `n`
non-negative integers, there are at least `m` cofactors `a / (a, b)`, where `a, b ∈ A`
(formal-conjectures definition). -/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

/-- The cofactor threshold `h(n)` is the largest cofactor lower bound for `n`
(formal-conjectures definition). -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- For every `A` of size `n`, the cofactor set has at least `⌈√n⌉` elements. -/
theorem isCofactorLowerBound_ceil_sqrt (n : ℕ) : IsCofactorLowerBound n ⌈Real.sqrt n⌉₊ := by
  intro A hA
  set I : Finset ℕ := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b with hIdef
  have himg : ∀ a ∈ A, ∀ b ∈ A, a / a.gcd b ∈ I :=
    fun a ha b hb => Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  set F : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 / q.1.gcd q.2, q.2 / q.1.gcd q.2) with hF
  have key : ∀ (q p : ℕ × ℕ), F q = p →
      q.1 = p.1 * q.1.gcd q.2 ∧ q.2 = p.2 * q.1.gcd q.2 := by
    intro q p hq
    have h1 : q.1 / q.1.gcd q.2 = p.1 := by rw [← hq]
    have h2 : q.2 / q.1.gcd q.2 = p.2 := by rw [← hq]
    exact ⟨by rw [← h1, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)],
           by rw [← h2, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]⟩
  have hsub : (A ×ˢ A).image F ⊆ I ×ˢ I := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    refine Finset.mem_product.mpr ⟨himg _ hq1 _ hq2, ?_⟩
    have hrw : (F q).2 = q.2 / q.2.gcd q.1 := by rw [hF]; simp [Nat.gcd_comm]
    rw [hrw]
    exact himg _ hq2 _ hq1
  have hcard : #(A ×ˢ A) ≤ n * #((A ×ˢ A).image F) := by
    refine Finset.card_le_mul_card_image _ _ ?_
    intro p _
    rw [← hA]
    by_cases hp1 : p.1 = 0
    · refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq
        exact Finset.mem_coe.mpr (Finset.mem_product.mp hq.1).2
      · intro q hq q' hq' h
        simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
        have e1 := (key q p hq.2).1
        have e2 := (key q' p hq'.2).1
        rw [hp1, zero_mul] at e1 e2
        exact Prod.ext (e1.trans e2.symm) h
    · refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq
        exact Finset.mem_coe.mpr (Finset.mem_product.mp hq.1).1
      · intro q hq q' hq' h
        simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
        obtain ⟨e1, e2⟩ := key q p hq.2
        obtain ⟨e1', e2'⟩ := key q' p hq'.2
        have hg : q.1.gcd q.2 = q'.1.gcd q'.2 :=
          Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp1) (by rw [← e1, ← e1']; exact h)
        exact Prod.ext h (by rw [e2, e2', hg])
  have hmain : n * n ≤ n * (#I * #I) := by
    calc n * n = #(A ×ˢ A) := by rw [Finset.card_product, hA]
      _ ≤ n * #((A ×ˢ A).image F) := hcard
      _ ≤ n * (#I * #I) := by
          refine Nat.mul_le_mul_left _ ?_
          calc #((A ×ˢ A).image F) ≤ #(I ×ˢ I) := Finset.card_le_card hsub
            _ = #I * #I := Finset.card_product _ _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h2 : n ≤ #I * #I := Nat.le_of_mul_le_mul_left hmain hn
    rw [Nat.ceil_le]
    have hcast : (n : ℝ) ≤ (#I : ℝ) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr h2
      rw [Nat.cast_mul] at this
      rw [pow_two]
      exact this
    calc Real.sqrt n ≤ Real.sqrt ((#I : ℝ) ^ 2) := Real.sqrt_le_sqrt hcast
      _ = (#I : ℝ) := Real.sqrt_sq (Nat.cast_nonneg _)

/-- `⌈√n⌉ ≤ h(n)` for every `n`. -/
theorem ceil_sqrt_le_cofactorThreshold (n : ℕ) : ⌈Real.sqrt n⌉₊ ≤ cofactorThreshold n := by
  refine le_csSup ⟨n * n, ?_⟩ (isCofactorLowerBound_ceil_sqrt n)
  intro m hm
  refine (hm (Finset.range n) (Finset.card_range n)).trans ?_
  calc #(((Finset.range n) ×ˢ (Finset.range n)).image fun (a, b) ↦ a / a.gcd b)
      ≤ #((Finset.range n) ×ˢ (Finset.range n)) := Finset.card_image_le
    _ = n * n := by rw [Finset.card_product, Finset.card_range]

/-- **Erdős–Szemerédi lower bound (Erdős #539).**  `√n ≪ h(n)`, in the exact shape of the
formal-conjectures statement `erdos_539.variants.sq_isBigO`.  The upper bounds and the order of
`h(n)` are not claimed. -/
theorem erdos_539_sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  calc Real.sqrt n ≤ (⌈Real.sqrt n⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (cofactorThreshold n : ℝ) := by exact_mod_cast ceil_sqrt_le_cofactorThreshold n
