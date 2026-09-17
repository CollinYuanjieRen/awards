import Proof.Defs

/-!
# Erdős problem #963: the greedy bound `f(n) ≥ ⌊log₃ n⌋`

The problem page asks to estimate `f(n)`, the maximal `k` such that every set `A ⊆ ℝ` of
size `n` contains a dissociated subset `B ⊆ A` with `|B| ≥ k`, and in particular whether
`f(n) ≥ ⌊log₂ n⌋`.  The page records that Erdős noted that the greedy algorithm gives
`f(n) ≥ ⌊log₃ n⌋`.  This package proves exactly that, via a maximal dissociated subset:
if `B ⊆ A` is dissociated of maximal size then every element of `A` is a `{-1, 0, 1}`-combination
of `B`, so `|A| ≤ 3 ^ |B|` and hence `⌊log₃ |A|⌋ ≤ |B|`.

Not claimed here: the question of Erdős problem #963 whether `f(n) ≥ ⌊log₂ n⌋`, and any bound better than the greedy one.

Main results:

* `Erdos963.exists_dissociated_subset` : every `A : Finset ℝ` has a dissociated subset `B`
  with `A.card ≤ 3 ^ B.card`;
* `Erdos963.exists_dissociated_subset_log` : the logarithmic form `Nat.log 3 A.card ≤ B.card`;
* `Erdos963.log_three_le_f` : `Nat.log 3 n ≤ f n`, Erdős's greedy bound;
* `Erdos963.f_le` and `Erdos963.exists_dissociated_subset_f` : `f n ≤ n`, and the supremum
  defining `f n` is attained.
-/

namespace Erdos963

open Finset

/-- Every finite set of reals has a dissociated subset `B` with `|A| ≤ 3 ^ |B|`: take `B`
dissociated of maximal size, represent each `a ∈ A` by its coefficient vector in
`{-1, 0, 1}ᴮ` using `Erdos963.exists_repr_of_maximal`, and note that the representation
determines `a`, so the assignment is injective. -/
theorem exists_dissociated_subset (A : Finset ℝ) : ∃ B ⊆ A, Dissociated B ∧ A.card ≤ 3 ^ B.card := by
  classical
  -- A dissociated subset of `A` of maximal cardinality.
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image (A.powerset.filter Dissociated) Finset.card
      ⟨∅, by simp [dissociated_empty]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hBmem
  obtain ⟨hBA, hB⟩ := hBmem
  have hmax : ∀ C ⊆ A, Dissociated C → C.card ≤ B.card := fun C hC hCd =>
    hBmax C (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hC, hCd⟩)
  refine ⟨B, hBA, hB, ?_⟩
  -- Choose, for every real, a coefficient vector that works whenever the real lies in `A`.
  have hrep : ∀ a : ℝ, ∃ ε : ℝ → ℤ, a ∈ A →
      (∀ b ∈ B, ε b = -1 ∨ ε b = 0 ∨ ε b = 1) ∧ a = ∑ b ∈ B, (ε b : ℝ) * b := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨ε, h1, h2⟩ := exists_repr_of_maximal hBA hB hmax a ha
      exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose ε hε using hrep
  -- The assignment `a ↦ (ε a restricted to B)` lands in `{-1, 0, 1}ᴮ` …
  set F : ℝ → ({x // x ∈ B} → ℤ) := fun a b => ε a (b : ℝ) with hF
  have hmaps : Set.MapsTo F (A : Set ℝ)
      ((Fintype.piFinset fun _ : {x // x ∈ B} => ({-1, 0, 1} : Finset ℤ)) : Set _) := by
    intro a ha
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro b
    have hb := (hε a (Finset.mem_coe.1 ha)).1 (b : ℝ) b.2
    simp only [hF, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- … and it is injective on `A`, since `a` is recovered as `∑ b ∈ B, ε a b * b`.
  have hinj : Set.InjOn F (A : Set ℝ) := by
    intro x hx y hy hxy
    rw [(hε x (Finset.mem_coe.1 hx)).2, (hε y (Finset.mem_coe.1 hy)).2]
    refine Finset.sum_congr rfl fun b hb => ?_
    have := congrFun hxy ⟨b, hb⟩
    simp only [hF] at this
    rw [this]
  have hthree : ({-1, 0, 1} : Finset ℤ).card = 3 := by decide
  calc A.card
      ≤ (Fintype.piFinset fun _ : {x // x ∈ B} => ({-1, 0, 1} : Finset ℤ)).card :=
        Finset.card_le_card_of_injOn F hmaps hinj
    _ = 3 ^ B.card := by
        rw [Fintype.card_piFinset]
        simp [hthree, Finset.prod_const]

/-- Logarithmic form of `Erdos963.exists_dissociated_subset`: every finite set of reals has
a dissociated subset of size at least `⌊log₃ |A|⌋`. -/
theorem exists_dissociated_subset_log (A : Finset ℝ) : ∃ B ⊆ A, Dissociated B ∧ Nat.log 3 A.card ≤ B.card := by
  obtain ⟨B, hBA, hB, hcard⟩ := exists_dissociated_subset A
  refine ⟨B, hBA, hB, ?_⟩
  calc Nat.log 3 A.card ≤ Nat.log 3 (3 ^ B.card) := Nat.log_mono_right hcard
    _ = B.card := Nat.log_pow (by norm_num) _

/-- The set of admissible lower bounds whose supremum defines `f`. -/
private def fSet (n : ℕ) : Set ℕ :=
  {k : ℕ | ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, Dissociated B ∧ k ≤ B.card}

private theorem f_eq_sSup (n : ℕ) : f n = sSup (fSet n) := rfl

/-- `n` bounds `fSet n` above: apply the defining property to an explicit `n`-element set. -/
private theorem n_mem_upperBounds_fSet (n : ℕ) : n ∈ upperBounds (fSet n) := by
  intro k hk
  have hcard : ((Finset.range n).image (Nat.cast : ℕ → ℝ)).card = n := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨B, hBA, _, hkB⟩ := hk _ hcard
  calc k ≤ B.card := hkB
    _ ≤ ((Finset.range n).image (Nat.cast : ℕ → ℝ)).card := Finset.card_le_card hBA
    _ = n := hcard

/-- `0` belongs to `fSet n`, witnessed by the empty (dissociated) subset. -/
private theorem zero_mem_fSet (n : ℕ) : 0 ∈ fSet n := fun _ _ =>
  ⟨∅, Finset.empty_subset _, dissociated_empty, Nat.zero_le _⟩

/-- `f n ≤ n`: any `n`-element set of reals has only `n` elements to offer. -/
theorem f_le (n : ℕ) : f n ≤ n := by
  rw [f_eq_sSup]
  exact csSup_le' (n_mem_upperBounds_fSet n)

/-- **Erdős's greedy bound** for problem #963: `⌊log₃ n⌋ ≤ f n`. -/
theorem log_three_le_f (n : ℕ) : Nat.log 3 n ≤ f n := by
  rw [f_eq_sSup]
  refine le_csSup ⟨n, n_mem_upperBounds_fSet n⟩ ?_
  intro A hA
  obtain ⟨B, hBA, hB, hcard⟩ := exists_dissociated_subset_log A
  refine ⟨B, hBA, hB, ?_⟩
  rw [← hA]
  exact hcard

/-- The supremum defining `f n` is attained: every `n`-element set of reals contains a
dissociated subset of size at least `f n`. -/
theorem exists_dissociated_subset_f (n : ℕ) (A : Finset ℝ) (hA : A.card = n) : ∃ B ⊆ A, Dissociated B ∧ f n ≤ B.card := by
  have hmem : f n ∈ fSet n := by
    rw [f_eq_sSup]
    exact Nat.sSup_mem ⟨0, zero_mem_fSet n⟩ ⟨n, n_mem_upperBounds_fSet n⟩
  exact hmem A hA

end Erdos963
