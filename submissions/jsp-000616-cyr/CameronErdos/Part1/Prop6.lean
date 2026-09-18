import CameronErdos.Part1.Family
import CameronErdos.Part1.Prop4
import CameronErdos.Part1.Prop5
import CameronErdos.Part1.SmallBinomial
import CameronErdos.Part1.ParamsMore

/-!
# Proposition 6 (ii): every sum-free set is covered by the container family

This file formalizes part (ii) of `Prop6_Family` from Green, *The Cameron–Erdős conjecture*
(2004), §3 (see arXiv math/0304058, pp. 6–7), and assembles parts (i),
(ii), (iii) into the eventual container statement used by the counting argument.

The covering step `CameronErdos.coverage_core` is Green's argument: given a sum-free
`A ⊆ [1, N]`, reduce it mod `p`, choose a good length `d` (Proposition 5), granularize
(Proposition 4 bounds the additive triples of `A'` by `ε p²`), and split
`A ⊆ A' ∪ (A \ A')`, where the exceptional set `A \ A'` has at most `ε p` elements
(`card_sdiff_granularization_le`).
-/

open Finset Filter

namespace CameronErdos

/-! ## Part (ii): the covering step -/

set_option linter.unusedVariables false in
/-- **`Prop6_Family` (ii)**.  If `p ∈ [2N, 4N]` is prime, `M`, `ε` satisfy the side
conditions of Proposition 4, and every nonempty subset of `ZMod p` has a nonzero good
length, then every sum-free `A ⊆ [1, N]` is contained in some member of the family `F`. -/
theorem coverage_core {N p : ℕ} [hp : Fact p.Prime] (hp1 : 2 * N ≤ p) (hp2 : p ≤ 4 * N)
    {M : ℕ} (hM : 0 < M) (hMp : M < p) (hLp : 2 * L p M - 1 ≤ p)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hεL : 24 ≤ ε * L p M)
    (hgood : ∀ A : Finset (ZMod p), A.Nonempty →
      ∃ d : ZMod p, d ≠ 0 ∧ IsGoodLength A d M ε (ε ^ 2 / 144) (ε ^ 2 / 80)) :
    ∀ A ⊆ Finset.Icc 1 N, IsSumFree A → ∃ F ∈ family N p M ε, A ⊆ F := by
  classical
  intro A hA hsf
  have hp0 : 0 < p := hp.out.pos
  have hNp : N < p := by omega
  have hεp : (0 : ℝ) ≤ ε * (p : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg p)
  have hεp2 : (0 : ℝ) ≤ ε * (p : ℝ) ^ 2 := mul_nonneg hε.le (by positivity)
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · -- the empty set is covered by the container with `d = 1`, `S = ∅`, `E = ∅`
    have hone : (1 : ZMod p) ≠ 0 := one_ne_zero
    have hUempty : containerU p (1 : ZMod p) M ∅ = (∅ : Finset (ZMod p)) := by
      simp [containerU]
    refine ⟨container N p (1 : ZMod p) M ∅ ∅, mem_family_of hone (by simp) ?_ (by simp) ?_,
      Finset.empty_subset _⟩
    · rw [hUempty]
      have hz : addTriples (∅ : Finset (ZMod p)) = 0 := by simp [addTriples]
      rw [hz, Nat.cast_zero]
      exact hεp2
    · have hz : (#(∅ : Finset ℕ) : ℝ) = 0 := by simp
      rw [hz]
      exact hεp
  · -- the main case
    set Ap : Finset (ZMod p) := A.image (Nat.cast : ℕ → ZMod p) with hApdef
    have hApne : Ap.Nonempty := hAne.image _
    have hsfp : ∀ x ∈ Ap, ∀ y ∈ Ap, x + y ∉ Ap := isSumFree_image hp1 hA hsf
    obtain ⟨d, hd0, hgd⟩ := hgood Ap hApne
    have hdu : IsUnit d := isUnit_iff_ne_zero.2 hd0
    -- Proposition 4: the granularization has at most `ε p²` additive triples
    have h4 := prop4_addTriples_le hApne hsfp hdu hM hMp hLp hε hε1 hεL hgd
    set A' : Finset (ZMod p) := granularization Ap d M ε with hA'def
    set S : Finset ℕ := denseIdx Ap d M ε with hSdef
    have hUeq : containerU p d M S = A' := by
      rw [hA'def, hSdef]
      exact (granularization_eq_containerU Ap d M ε).symm
    have hSsub : S ⊆ Finset.range M := by
      intro i hi
      rw [hSdef, mem_denseIdx] at hi
      exact Finset.mem_range.2 hi.1
    have hSt : (addTriples (containerU p d M S) : ℝ) ≤ ε * (p : ℝ) ^ 2 := by
      rw [hUeq]; exact h4
    -- the exceptional set of points of `A` lying in sparse progressions
    set E : Finset ℕ := A.filter (fun a : ℕ => (a : ZMod p) ∉ A') with hEdef
    have hEmem : ∀ a : ℕ, a ∈ E ↔ a ∈ A ∧ (a : ZMod p) ∉ A' := by
      intro a; rw [hEdef, Finset.mem_filter]
    have hEsub : E ⊆ Finset.Icc 1 N := fun a ha => hA ((hEmem a).1 ha).1
    have hEcard : (#E : ℝ) ≤ ε * (p : ℝ) := by
      have hcard : #E ≤ #(Ap \ A') := by
        refine Finset.card_le_card_of_injOn (Nat.cast : ℕ → ZMod p) ?_ ?_
        · intro a ha
          obtain ⟨haA, ha'⟩ := (hEmem a).1 ha
          exact Finset.mem_sdiff.2 ⟨Finset.mem_image_of_mem _ haA, ha'⟩
        · intro a ha b hb hab
          exact cast_injOn_Icc (N := N) (p := p) hNp
            (Finset.mem_coe.2 (hEsub (Finset.mem_coe.1 ha)))
            (Finset.mem_coe.2 (hEsub (Finset.mem_coe.1 hb))) hab
      calc (#E : ℝ) ≤ (#(Ap \ A') : ℝ) := by exact_mod_cast hcard
        _ ≤ ε * (p : ℝ) := by
            rw [hA'def]; exact card_sdiff_granularization_le hdu hM hε.le
    refine ⟨container N p d M S E, mem_family_of hd0 hSsub hSt hEsub hEcard, ?_⟩
    intro a ha
    simp only [container, Finset.mem_union, Finset.mem_filter]
    by_cases hmem : (a : ZMod p) ∈ A'
    · exact Or.inl ⟨hA ha, by rw [hUeq]; exact hmem⟩
    · exact Or.inr ((hEmem a).2 ⟨ha, hmem⟩)


/-! ## The eventual container family -/

/-- **`Prop6_Family`**, in the form used by the counting argument: for every `θ > 0` and all
large `N` there is a family `𝓕` of at most `2^{θN}` subsets of `[1, N]`, each with at most
`64 ε_N N²` additive triples, covering every sum-free subset of `[1, N]`. -/
theorem eventually_container_family (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ 𝓕 : Finset (Finset ℕ),
      (#𝓕 : ℝ) ≤ 2 ^ (θ * N) ∧
      (∀ F ∈ 𝓕, F ⊆ Finset.Icc 1 N ∧ (addTriples F : ℝ) ≤ 64 * epsN N * (N : ℝ) ^ 2) ∧
      ∀ A ⊆ Finset.Icc 1 N, IsSumFree A → ∃ F ∈ 𝓕, A ⊆ F := by
  filter_upwards [eventually_ge_atTop 1, eventually_family_bound_general θ hθ,
    eventually_exists_goodLength, eventually_prop4_side'] with N hN1 hbound hgood hside
  -- Bertrand's postulate provides a prime `p ∈ (2N, 4N]`
  obtain ⟨p, hpp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have : Fact p.Prime := ⟨hpp⟩
  have hp1 : 2 * N ≤ p := hplt.le
  have hp2 : p ≤ 4 * N := by omega
  obtain ⟨hM, hMp, hLp, hε, hε1, hεL⟩ := hside p hp1 hp2
  refine ⟨family N p (MN N) (epsN N), ?_, ?_, ?_⟩
  · calc (#(family N p (MN N) (epsN N)) : ℝ)
        ≤ (p : ℝ) * 2 ^ (MN N) *
            ∑ j ∈ Finset.range (⌊epsN N * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ) :=
          card_family_le hε.le
      _ ≤ 2 ^ (θ * N) := hbound p hp1 hp2
  · intro F hF
    exact ⟨family_subset_Icc F hF, addTriples_family_le hp1 hp2 hε.le F hF⟩
  · refine coverage_core hp1 hp2 hM hMp hLp hε hε1 hεL ?_
    intro A hA
    obtain ⟨d, hd0, hgd⟩ := hgood p hp1 hp2 A hA
    rw [eps1, eps2, eps3] at hgd
    exact ⟨d, hd0, hgd⟩

#print axioms CameronErdos.coverage_core
#print axioms CameronErdos.eventually_container_family

end CameronErdos
