import Mathlib

/-!
# Erdős Problem #36 (minimum overlap): Erdős's 1955 example, `limsup M(N)/N ≤ 1/2`

Split `{1, …, 2N}` into two sets `A, B` of size `N`, let `M(N)` be the least possible value of
`max_k #{(a, b) ∈ A × B : a − b = k}`, and let `c = lim M(N)/N`.  The exact value of `c` is OPEN
(`0.379005 ≤ c ≤ 0.380926…`).  The problem page records that the example (with `N` even)
`A = {N/2 + 1, …, 3N/2}` shows `c ≤ 1/2`.  This file proves exactly that statement, in the shape
of the formal-conjectures theorem `Erdos36.minimum_overlap.variants.upper.erdos_1955`
(`atTop.limsup MinOverlapQuotient ≤ 1/2`, tagged "research solved" with `sorry`), with the
definitions `Overlap`, `MaxOverlap`, `M`, `MinOverlapQuotient` copied verbatim.

Proof.  For every `N` take `A = [⌈N/2⌉ + 1, ⌈N/2⌉ + N]` and `B` its complement in `[1, 2N]`, two
intervals of lengths `⌈N/2⌉` and `⌊N/2⌋` separated by a gap of length `N`.  For a fixed
difference `k` the pairs `(a, b)` with `a − b = k` inject into `B ∩ (A − k)`, and the interval
`A − k` of length `N` meets at most one of the two parts of `B`; hence every overlap is at most
`⌈N/2⌉`, so `M(N) ≤ ⌈N/2⌉` and `M(N)/N ≤ 1/2 + 1/(2N)`, whose limsup is at most `1/2`.  The
sharper bounds (Motzkin–Ralston–Selfridge, Haugland, White) and the value of `c` are not
addressed.
-/

open scoped Topology
open Filter

/-- The number of solutions to the equation `a − b = k`, for `a ∈ A` and `b ∈ B`
(formal-conjectures definition). -/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ := ((A.product B).filter <| fun (a, b) => a - b = k).card

/-- The maximum overlap for a given pair of sets `A` and `B`, taken over all integer differences
`k` (formal-conjectures definition). -/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ := iSup <| Overlap A B

/-- `M n` is the minimum `MaxOverlap` over all splittings of `{1, …, 2n}` into two sets of the
same cardinality (formal-conjectures definition). -/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/-- The quotient `M(N)/N` (formal-conjectures definition). -/
noncomputable def MinOverlapQuotient (N : ℕ) := (M N : ℝ) / N

/-- Erdős's 1955 example: the interval `A = [⌈N/2⌉ + 1, ⌈N/2⌉ + N]`. -/
noncomputable def erdosInterval (N : ℕ) : Finset ℤ := Finset.Icc (((N + 1) / 2 : ℕ) + 1 : ℤ) (((N + 1) / 2 : ℕ) + N)

/-- Membership in Erdős's interval, unfolded to plain inequalities. -/
private lemma mem_erdosInterval_iff (N : ℕ) (a : ℤ) :
    a ∈ erdosInterval N ↔
      (((N + 1) / 2 : ℕ) : ℤ) + 1 ≤ a ∧ a ≤ (((N + 1) / 2 : ℕ) : ℤ) + N := by
  rw [erdosInterval, Finset.mem_Icc]

/-- Membership in the complement of Erdős's interval, unfolded to plain inequalities. -/
private lemma mem_compl_erdosInterval_iff (N : ℕ) (b : ℤ) :
    b ∈ Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N ↔
      (1 ≤ b ∧ b ≤ 2 * (N : ℤ)) ∧
        ¬ ((((N + 1) / 2 : ℕ) : ℤ) + 1 ≤ b ∧ b ≤ (((N + 1) / 2 : ℕ) : ℤ) + N) := by
  rw [Finset.mem_sdiff, Finset.mem_Icc, mem_erdosInterval_iff]

/-- For a fixed difference `k` the second coordinate determines the first, so the pairs counted by
`Overlap A B k` inject into any `Finset` containing all admissible second coordinates. -/
private lemma overlap_le_card_of_snd_mem {A B T : Finset ℤ} {k : ℤ}
    (hT : ∀ a ∈ A, ∀ b ∈ B, a - b = k → b ∈ T) : Overlap A B k ≤ T.card := by
  unfold Overlap
  refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
  · rintro ⟨a, b⟩ hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hp
    have hab : a - b = k := hp.2
    exact hT a hp.1.1 b hp.1.2 hab
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hbd
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    have hab : a - b = k := hp.2
    have hcd : c - d = k := hq.2
    have hbd' : b = d := hbd
    exact Prod.ext (by omega) hbd'

/-- Every overlap of Erdős's interval with its complement in `[1, 2N]` is at most `⌈N/2⌉`. -/
theorem overlap_erdosInterval_le (N : ℕ) (k : ℤ) :
    Overlap (erdosInterval N) (Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N) k ≤ (N + 1) / 2 := by
  by_cases hc : ∃ a ∈ erdosInterval N, ∃ b ∈ Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N,
      a - b = k ∧ b ≤ (((N + 1) / 2 : ℕ) : ℤ)
  · -- Some contributing pair has its second coordinate in the lower part `[1, ⌈N/2⌉]` of the
    -- complement.  Then all of them do, since `A - k` is an interval of length `N` and the two
    -- parts of the complement are separated by a gap of length `N`.
    obtain ⟨a₀, ha₀, b₀, hb₀, hk₀, hb₀le⟩ := hc
    rw [mem_erdosInterval_iff] at ha₀
    rw [mem_compl_erdosInterval_iff] at hb₀
    refine (overlap_le_card_of_snd_mem
      (T := Finset.Icc (1 : ℤ) ((((N + 1) / 2 : ℕ) : ℤ))) (fun a ha b hb hab => ?_)).trans ?_
    · rw [mem_erdosInterval_iff] at ha
      rw [mem_compl_erdosInterval_iff] at hb
      rw [Finset.mem_Icc]
      omega
    · rw [Int.card_Icc]
      omega
  · -- Otherwise every contributing pair has its second coordinate in the upper part
    -- `[⌈N/2⌉ + N + 1, 2N]`, which has only `⌊N/2⌋ ≤ ⌈N/2⌉` elements.
    push Not at hc
    refine (overlap_le_card_of_snd_mem
      (T := Finset.Icc ((((N + 1) / 2 : ℕ) : ℤ) + N + 1) (2 * (N : ℤ)))
      (fun a ha b hb hab => ?_)).trans ?_
    · have hlt := hc a ha b hb hab
      rw [mem_compl_erdosInterval_iff] at hb
      rw [Finset.mem_Icc]
      omega
    · rw [Int.card_Icc]
      omega

/-- Erdős's interval has exactly `N` elements. -/
private lemma card_erdosInterval (N : ℕ) : (erdosInterval N).card = N := by
  rw [erdosInterval, Int.card_Icc]
  omega

/-- Erdős's interval sits inside `[1, 2N]`. -/
private lemma erdosInterval_subset (N : ℕ) : erdosInterval N ⊆ Finset.Icc (1 : ℤ) (2 * N) := by
  intro a ha
  rw [mem_erdosInterval_iff] at ha
  rw [Finset.mem_Icc]
  omega

/-- `2 M(N) ≤ N + 1` for every `N`. -/
theorem two_mul_M_le (N : ℕ) : 2 * M N ≤ N + 1 := by
  have hsub := erdosInterval_subset N
  have hcard := card_erdosInterval N
  have hB : (Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N).card = N := by
    rw [Finset.card_sdiff_of_subset hsub, Int.card_Icc, hcard]
    omega
  have h1 : M N ≤ MaxOverlap (erdosInterval N) (Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N) := by
    refine Nat.sInf_le ⟨erdosInterval N, Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N,
      Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub, ?_, rfl⟩
    rw [hcard, hB]
  have h2 : MaxOverlap (erdosInterval N) (Finset.Icc (1 : ℤ) (2 * N) \ erdosInterval N)
      ≤ (N + 1) / 2 := ciSup_le fun k => overlap_erdosInterval_le N k
  omega

/-- **Erdős's 1955 example (Erdős #36).**  `limsup_{N→∞} M(N)/N ≤ 1/2`, in the exact shape of the
formal-conjectures theorem `minimum_overlap.variants.upper.erdos_1955`.  The value of the limit
is open and not claimed. -/
theorem minimum_overlap_upper_erdos_1955 :
    atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 := by
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop MinOverlapQuotient :=
    Filter.isCoboundedUnder_le_of_le (x := (0 : ℝ)) atTop fun N => by
      rw [MinOverlapQuotient]; positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine Filter.limsup_le_of_le hcobdd ?_
  filter_upwards [eventually_ge_atTop (⌈(1 : ℝ) / ε⌉₊ + 1)] with N hN
  have hN1 : (0 : ℕ) < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hceil : (⌈(1 : ℝ) / ε⌉₊ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (by omega : ⌈(1 : ℝ) / ε⌉₊ ≤ N)
  have hinv : (1 : ℝ) / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans hceil
  have hepsN : (1 : ℝ) ≤ (N : ℝ) * ε := (div_le_iff₀ hε).mp hinv
  have hMb : 2 * (M N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast two_mul_M_le N
  rw [MinOverlapQuotient, div_le_iff₀ hNpos]
  nlinarith [hMb, hepsN, hNpos]
