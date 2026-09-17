import Mathlib

/-!
# Erdős problem #635, scoped component: the exact maximum for `t = 1`

The problem page for Erdős problem #635 asks, for `t ≥ 1`, how large a set
`A ⊆ {1, …, N}` can be when `b - a ∤ b` holds for all `a, b ∈ A` with `b - a ≥ t`.
The page records Erdős's observation that for `t = 1` the maximum possible size is
exactly `⌊(N+1)/2⌋`, attained by taking `A` to be all the odd numbers in `{1, …, N}`.
This package proves that observation in full: both the upper bound
(`card_le_of_adm`) and the odd-number witness (`adm_odds`, `card_odds`), combined
into the exact value (`maxAdm_eq`, `isGreatest_adm_card`).

At `t = 1` the hypothesis applies to every pair `a < b` of elements of `A`, which is
what `Adm` below states. Since `1 = (a + 1) - a` divides `a + 1`, an admissible set
contains no two consecutive integers, so `a ↦ (a + 1) / 2` is injective from `A` into
`{1, …, ⌊(N+1)/2⌋}`; conversely, for odd `a < b` the difference `b - a` is even and an
even number never divides the odd number `b`.

Not claimed here: the `t = 2` construction of Erdős problem #635 with its unspecified constant `c`, the general question whether `|A| ≤ (1/2 + o_t(1)) N` and its resolution, and Elliott's inequality.
-/

namespace Erdos635

/-- `Adm N A` says that `A` is *admissible* for `N` at `t = 1`: it is a subset of
`{1, …, N}` and for all `a < b` in `A` the difference `b - a` does not divide `b`. -/
def Adm (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ (b - a) ∣ b

open Classical in
/-- `maxAdm N` is the largest cardinality of an admissible subset of `{1, …, N}`,
taken as a `Finset.sup` over the finitely many subsets of `{1, …, N}`. -/
noncomputable def maxAdm (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => Adm N A)).sup Finset.card

/-- An admissible set contains no two consecutive integers: if `a ∈ A` then `a + 1 ∉ A`,
because `(a + 1) - a = 1` divides `a + 1`. -/
theorem not_consecutive_of_adm {N : ℕ} {A : Finset ℕ} (h : Adm N A) {a : ℕ} (ha : a ∈ A) :
    a + 1 ∉ A := by
  intro hb
  refine h.2 a ha (a + 1) hb (Nat.lt_succ_self a) ?_
  have hsub : a + 1 - a = 1 := by omega
  rw [hsub]
  exact one_dvd _

/-- Upper bound: every admissible set has at most `⌊(N+1)/2⌋` elements. -/
theorem card_le_of_adm (N : ℕ) (A : Finset ℕ) (h : Adm N A) : A.card ≤ (N + 1) / 2 := by
  have key : A.card ≤ (Finset.Icc 1 ((N + 1) / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun a => (a + 1) / 2) ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe] at ha
      have hmem := h.1 ha
      rw [Finset.mem_Icc] at hmem
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      simp only at hab
      by_contra hne
      rcases lt_trichotomy a b with hlt | heq | hgt
      · have hb1 : b = a + 1 := by omega
        exact not_consecutive_of_adm h ha (hb1 ▸ hb)
      · exact hne heq
      · have ha1 : a = b + 1 := by omega
        exact not_consecutive_of_adm h hb (ha1 ▸ ha)
  have hcard : (Finset.Icc 1 ((N + 1) / 2)).card = (N + 1) / 2 := by
    rw [Nat.card_Icc]
    omega
  omega

/-- Lower bound, part 1: the odd numbers in `{1, …, N}` form an admissible set. -/
theorem adm_odds (N : ℕ) : Adm N ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro a ha b hb hlt hdvd
  simp only [Finset.mem_filter] at ha hb
  have h2 : (2 : ℕ) ∣ b - a := by
    have hoa := ha.2
    have hob := hb.2
    omega
  exact hb.2 (h2.trans hdvd)

/-- Lower bound, part 2: there are exactly `⌊(N+1)/2⌋` odd numbers in `{1, …, N}`. -/
theorem card_odds (N : ℕ) : ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card = (N + 1) / 2 := by
  have himg : (Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)
      = (Finset.range ((N + 1) / 2)).image (fun i => 2 * i + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hodd⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective _ (by intro a b hab; simp only at hab; omega),
    Finset.card_range]

/-- The set of cardinalities of admissible sets has greatest element `⌊(N+1)/2⌋`. -/
theorem isGreatest_adm_card (N : ℕ) : IsGreatest {m : ℕ | ∃ A : Finset ℕ, Adm N A ∧ A.card = m} ((N + 1) / 2) := by
  constructor
  · exact ⟨(Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n), adm_odds N, card_odds N⟩
  · rintro m ⟨A, hA, rfl⟩
    exact card_le_of_adm N A hA

/-- Erdős's observation for `t = 1`: the maximum size of an admissible subset of
`{1, …, N}` is exactly `⌊(N+1)/2⌋`. -/
theorem maxAdm_eq (N : ℕ) : maxAdm N = (N + 1) / 2 := by
  classical
  unfold maxAdm
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro A hA
    exact card_le_of_adm N A (Finset.mem_filter.1 hA).2
  · rw [← card_odds N]
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (adm_odds N).1, adm_odds N⟩)

end Erdos635
