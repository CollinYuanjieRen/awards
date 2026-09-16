import Mathlib

/-!
# Erdős Problem #302: the lower bounds `f(N) ≥ (1/2 − o(1))N` and Cambie's `f(N) ≥ (5/8 − o(1))N`

Let `f(N)` be the size of the largest `A ⊆ {1, …, N}` with no solution to `1/a = 1/b + 1/c` in
distinct `a, b, c ∈ A`.  Erdős asked to estimate `f(N)` (OPEN; van Doorn proved
`f(N) ≤ (9/10 + o(1))N`).  The problem page records the elementary lower bounds: the odd
integers, or the integers in `[N/2, N]`, give `f(N) ≥ (1/2 + o(1))N`, and Stijn Cambie observed
that the odd integers `≤ N/4` together with all integers in `[N/2, N]` give
`f(N) ≥ (5/8 + o(1))N`.  This file proves Cambie's construction with an explicit error term,
`f(N) ≥ 5N/8 − 2` for every `N`, and derives both formal-conjectures statements
`Erdos302.erdos_302.variants.lower_half` and `lower_five_eighths` (tagged "research solved" with
`sorry`), whose definitions `NoUnitFractionTriple` and `IsMaxNoTripleCard` are copied verbatim.

Proof of the construction.  Let `A = {odd a ≤ N/4} ∪ {a : N/2 < a ≤ N}` and suppose
`1/a = 1/b + 1/c` with distinct `a, b, c ∈ A`; then `a < b, c`.  If `a > N/2` then
`1/a < 2/N ≤ 1/b + 1/c`.  If `a` is odd and one of `b, c` is odd, say `b`, then `c(b − a) = ab`
is even on the left and odd on the right.  Otherwise `b, c` are even, hence `> N/2`, and
`1/b + 1/c < 4/N ≤ 1/a`.  The set has at least `(N − 3)/8 + N/2 ≥ 5N/8 − 2` elements.  The upper bound and the true order of `f(N)`
are not addressed.
-/

open Filter Topology

/-- A finite set `A` of positive integers admits no solution to `1/a = 1/b + 1/c` with `a, b, c`
distinct elements of `A` (formal-conjectures definition). -/
def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

/-- `f N` is the size of the largest `A ⊆ {1, …, N}` containing no solution to `1/a = 1/b + 1/c`
with distinct `a, b, c ∈ A` (formal-conjectures definition). -/
def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

/-- Cambie's set: the odd integers `≤ N/4` together with all integers `a` with `N/2 < a ≤ N`
(i.e. `⌊N/2⌋ + 1 ≤ a ≤ N`, at least `N/2` of them). -/
def cambieSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N / 4)).filter Odd ∪ Finset.Icc (N / 2 + 1) N

theorem cambieSet_subset (N : ℕ) : cambieSet N ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hx
  simp only [Finset.mem_Icc]
  rcases hx with ⟨⟨hx1, hx2⟩, -⟩ | ⟨hx1, hx2⟩
  · exact ⟨hx1, hx2.trans (Nat.div_le_self _ _)⟩
  · exact ⟨by omega, hx2⟩

/-- Parity obstruction: if `x` and `y` are odd then `y * z = x * (y + z)` is impossible. -/
private lemma cambie_parity {x y z : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    y * z ≠ x * (y + z) := by
  intro h
  have h2 : (y * z) % 2 = (x * (y + z)) % 2 := by rw [h]
  rw [Nat.mul_mod, Nat.mul_mod x, Nat.add_mod y z, hx, hy] at h2
  omega

theorem cambieSet_noUnitFractionTriple (N : ℕ) : NoUnitFractionTriple (cambieSet N) := by
  intro a ha b hb c hc _hab _hac _hbc heq
  have hA := Finset.mem_Icc.mp (cambieSet_subset N ha)
  have hB := Finset.mem_Icc.mp (cambieSet_subset N hb)
  have hC := Finset.mem_Icc.mp (cambieSet_subset N hc)
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcore : (b : ℚ) * c = a * (b + c) := by
    rw [div_add_div _ _ hb0 hc0, div_eq_div_iff ha0 (mul_ne_zero hb0 hc0)] at heq
    linear_combination heq
  have hcoreN : b * c = a * (b + c) := by exact_mod_cast hcore
  simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at ha hb hc
  rcases ha with ⟨⟨_, ha4⟩, haodd⟩ | ⟨haN, -⟩
  · -- `a` is odd and `a ≤ N / 4`.
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp haodd
    rcases hb with ⟨-, hbodd⟩ | ⟨hbN, -⟩
    · exact cambie_parity ha2 (Nat.odd_iff.mp hbodd) hcoreN
    rcases hc with ⟨-, hcodd⟩ | ⟨hcN, -⟩
    · exact cambie_parity (z := b) ha2 (Nat.odd_iff.mp hcodd)
        (by rw [Nat.mul_comm c b, Nat.add_comm c b]; exact hcoreN)
    -- both `b` and `c` are even, hence `> N / 2`, while `4 * a ≤ N`.
    have h4a : 4 * a ≤ N := by omega
    have h2b : N + 1 ≤ 2 * b := by omega
    have h2c : N + 1 ≤ 2 * c := by omega
    have k1 : 4 * a * b ≤ N * b := Nat.mul_le_mul_right b h4a
    have k2 : 4 * a * c ≤ N * c := Nat.mul_le_mul_right c h4a
    have k3 : (N + 1) * b ≤ 2 * c * b := Nat.mul_le_mul_right b h2c
    have k4 : (N + 1) * c ≤ 2 * b * c := Nat.mul_le_mul_right c h2b
    linarith
  · -- `a > N / 2`, so `2 * a ≥ N + 1`, while `b, c ≤ N`.
    have h2a : N + 1 ≤ 2 * a := by omega
    have k1 : (N + 1) * b ≤ 2 * a * b := Nat.mul_le_mul_right b h2a
    have k2 : (N + 1) * c ≤ 2 * a * c := Nat.mul_le_mul_right c h2a
    have k3 : c * b ≤ N * b := Nat.mul_le_mul_right b hC.2
    have k4 : b * c ≤ N * c := Nat.mul_le_mul_right c hB.2
    linarith

theorem cambieSet_card (N : ℕ) : (5 * N : ℝ) / 8 - 2 ≤ (cambieSet N).card := by
  have hdisj : Disjoint ((Finset.Icc 1 (N / 4)).filter Odd) (Finset.Icc (N / 2 + 1) N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc] at hx'
    omega
  have hbot : (N / 4 + 1) / 2 ≤ ((Finset.Icc 1 (N / 4)).filter Odd).card := by
    have hsub : (Finset.range ((N / 4 + 1) / 2)).image (fun k => 2 * k + 1) ⊆
        (Finset.Icc 1 (N / 4)).filter Odd := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, ⟨k, by ring⟩⟩
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro x y h
      simp only at h
      omega
    calc (N / 4 + 1) / 2
        = ((Finset.range ((N / 4 + 1) / 2)).image (fun k => 2 * k + 1)).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  have htop : (Finset.Icc (N / 2 + 1) N).card = N - N / 2 := by
    rw [Nat.card_Icc]; omega
  have hcard : (N / 4 + 1) / 2 + (N - N / 2) ≤ (cambieSet N).card := by
    rw [cambieSet, Finset.card_union_of_disjoint hdisj, htop]
    omega
  have hfinal : 5 * N ≤ 8 * (cambieSet N).card + 3 := by omega
  have hR : (5 * N : ℝ) ≤ 8 * (cambieSet N).card + 3 := by exact_mod_cast hfinal
  linarith

/-- **Cambie's construction with an explicit error term (Erdős #302).**  For every `N` there is
`A ⊆ {1, …, N}` with no unit-fraction triple and `|A| ≥ 5N/8 − 2`. -/
theorem erdos_302_five_eighths_explicit (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ (5 * N : ℝ) / 8 - 2 ≤ A.card :=
  ⟨cambieSet N, cambieSet_subset N, cambieSet_noUnitFractionTriple N, cambieSet_card N⟩

/-- Formal-conjectures `erdos_302.variants.lower_five_eighths` (Cambie). -/
theorem erdos_302_lower_five_eighths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := by
  refine Filter.eventually_atTop.mpr ⟨⌈2 / ε⌉₊, fun N hN => ?_⟩
  obtain ⟨A, hAsub, hAnt, hAcard⟩ := erdos_302_five_eighths_explicit N
  have hmem : A.card ∈ {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} :=
    ⟨A, hAsub, hAnt, rfl⟩
  have hle : (A.card : ℝ) ≤ (f N : ℝ) := by exact_mod_cast (hf N).2 hmem
  have hNe : (2 : ℝ) / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  rw [div_le_iff₀ hε] at hNe
  linarith

/-- Formal-conjectures `erdos_302.variants.lower_half`. -/
theorem erdos_302_lower_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := by
  filter_upwards [erdos_302_lower_five_eighths f hf ε hε] with N hNle
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith
