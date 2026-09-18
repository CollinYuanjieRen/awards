import CameronErdos.Part1.Prop6
import CameronErdos.Part2.Prop7
import CameronErdos.Part2.Cor13Numerics
import CameronErdos.Assembly

/-!
# Proposition 12: `f(N) ≤ 2^{(1/2 + θ)N}` for every `θ > 0`

This file formalises Proposition 12 of Green, *The Cameron–Erdős conjecture* (2004)
(arXiv math/0304058), originally due to Alon and to
Calkin–Erdős–Granville: for every `θ > 0` the number of sum-free subsets of `[1, N]`
is eventually at most `2^{(1/2 + θ)N}`.

The proof combines the container family of Proposition 6 (`eventually_container_family`)
with the stability result of Proposition 7 (`prop7`):

* every sum-free `A ⊆ [1, N]` lies inside some container `F ∈ 𝓕`, and `#𝓕 ≤ 2^{θN/2}`;
* each container `F` has at most `64 ε_N N²` additive triples, so Proposition 7 applies
  (unless `#F < (1/2 − 1/120)N`, in which case there is nothing to do), and gives
  `#F ≤ (1/2 + 54 ρ_N)N + 1` where `ρ_N = (64 ε_N)^{1/8}`;
* hence `f(N) ≤ #𝓕 · 2^{(1/2 + 54ρ_N)N + 1} ≤ 2^{θN/2} · 2^{(1/2 + θ/2)N}`.

Proposition 7 is stated for `Finset ℤ`, while the container family lives in `Finset ℕ`,
so the first section transfers `addTriples`, cardinality, the containment in `[1, N]` and
the even-element count along the (injective, additive) cast `ℕ → ℤ`.

The final statement `eventually_sumFreeCount_shift_le` is the shifted form
`f(N − ⌊N/120⌋) ≤ 2^{(1/2 + θ)(N − ⌊N/120⌋)}` needed by Corollary 13.
-/

open Finset Filter Topology

namespace CameronErdos

/-! ## Transfer `ℕ → ℤ` along the cast -/

/-- The cast `ℕ → ℤ` is injective, so it preserves cardinalities of `Finset`s. -/
theorem card_image_intCast (F : Finset ℕ) :
    #(F.image (Nat.cast : ℕ → ℤ)) = #F :=
  Finset.card_image_of_injective _ (Nat.cast_injective (R := ℤ))

/-- The cast `ℕ → ℤ` sends `[1, N] ∩ ℕ` into `[1, N] ∩ ℤ`. -/
theorem image_intCast_subset {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.Icc 1 N) :
    F.image (Nat.cast : ℕ → ℤ) ⊆ Finset.Icc (1 : ℤ) (N : ℤ) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
  have h := Finset.mem_Icc.1 (hF ha)
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **Transfer of `addTriples`.**  The cast `ℕ → ℤ` is an injective additive map, so it
induces a bijection between the additive triples of `F` and those of its image. -/
theorem addTriples_image_intCast (F : Finset ℕ) :
    addTriples (F.image (Nat.cast : ℕ → ℤ)) = addTriples F := by
  symm
  simp only [addTriples]
  refine Finset.card_bij (fun t _ => ((t.1 : ℤ), (t.2.1 : ℤ), (t.2.2 : ℤ))) ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
    obtain ⟨⟨hx, hy, hz⟩, hs⟩ := h
    refine ⟨⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy,
      Finset.mem_image_of_mem _ hz⟩, ?_⟩
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hs
  · rintro ⟨x, y, z⟩ - ⟨x', y', z'⟩ - hxy
    simp only [Prod.mk.injEq, Nat.cast_inj] at hxy
    simp only [Prod.mk.injEq]
    exact ⟨hxy.1, hxy.2.1, hxy.2.2⟩
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at h
    obtain ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩⟩, hs⟩ := h
    refine ⟨(x, y, z), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hx, hy, hz⟩, by exact_mod_cast hs⟩

/-- Evenness is preserved by the cast `ℕ → ℤ`, so the even-element counts agree. -/
theorem card_filter_even_image_intCast (F : Finset ℕ) :
    #{a ∈ F.image (Nat.cast : ℕ → ℤ) | Even a} = #{a ∈ F | Even a} := by
  rw [Finset.filter_image, card_image_intCast]
  congr 1
  refine Finset.filter_congr ?_
  intro a _
  simp [Int.even_coe_nat]

/-! ## The container cardinality bound -/

/-- **Containers are not much bigger than `N/2`.**  A subset `F ⊆ [1, N]` with at most
`64 ε_N N²` additive triples has `#F ≤ (1/2 + 54 ρ_N)N + 1`, where `ρ_N = (64 ε_N)^{1/8}`.

If `#F < (1/2 − 1/120)N` there is nothing to prove; otherwise Proposition 7 applies to the
image of `F` in `ℤ` with `ε := 64 ε_N` (so that `ε^{1/8} = ρ_N`).  In alternative (i) the
set `F` is covered, up to `32 ρ_N N` exceptions, by an interval of length at most
`2N(1 + 30ρ_N) − 3#F`, whence `4#F ≤ 2N + 92ρ_N N`; in alternative (ii) at most `54 ρ_N N`
elements of `F` are even and the rest are odd elements of `[1, N]`, of which there are
`⌈N/2⌉`. -/
theorem card_container_le (N : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.Icc 1 N)
    (hρ : 0 < rho N ∧ rho N ≤ 1 / 10 ^ 4 ∧ (1000 : ℝ) ≤ rho N * N ∧
      64 * epsN N ≤ 1 / 10 ^ 32)
    (htr : (addTriples F : ℝ) ≤ 64 * epsN N * (N : ℝ) ^ 2) :
    (#F : ℝ) ≤ (1 / 2 + 54 * rho N) * N + 1 := by
  obtain ⟨hρpos, hρsmall, hρN, hε0⟩ := hρ
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hρN0 : (0 : ℝ) ≤ rho N * N := mul_nonneg (rho_nonneg N) hN0
  -- `ρ_N > 0` forces `64 ε_N > 0`
  have hrho' : rho N = Real.sqrt (Real.sqrt (Real.sqrt (64 * epsN N))) := rfl
  have hεpos : 0 < 64 * epsN N := by
    rw [hrho'] at hρpos
    exact Real.sqrt_pos.1 (Real.sqrt_pos.1 (Real.sqrt_pos.1 hρpos))
  rcases lt_or_ge (#F : ℝ) ((1 / 2 - 1 / 120 : ℝ) * N) with hsmall | hbig
  · nlinarith
  -- the main case: Proposition 7 applies
  set F' : Finset ℤ := F.image (Nat.cast : ℕ → ℤ) with hF'def
  have hF'sub : F' ⊆ Finset.Icc (1 : ℤ) (N : ℤ) := image_intCast_subset hF
  have hcard' : (#F' : ℝ) = (#F : ℝ) := by rw [hF'def, card_image_intCast]
  have h7 := prop7 hF'sub hεpos hε0 (by rw [← hrho']; exact hρN)
    (by rw [hcard']; exact hbig)
    (by rw [hF'def, addTriples_image_intCast]; exact htr)
  rcases h7 with ⟨u, len, hlen, hexc⟩ | hev
  · -- alternative (i): `F` almost lies in a short interval
    have hsplit : #{a ∈ F' | a ∈ Finset.Ico u (u + (len : ℤ))} +
        #{a ∈ F' | a ∉ Finset.Ico u (u + (len : ℤ))} = #F' :=
      Finset.card_filter_add_card_filter_not _
    have hIco : #(Finset.Ico u (u + (len : ℤ))) = len := by
      rw [Int.card_Ico]; simp
    have hinner : #{a ∈ F' | a ∈ Finset.Ico u (u + (len : ℤ))} ≤ len := by
      have h : #{a ∈ F' | a ∈ Finset.Ico u (u + (len : ℤ))} ≤
          #(Finset.Ico u (u + (len : ℤ))) :=
        Finset.card_le_card fun a ha => (Finset.mem_filter.1 ha).2
      rwa [hIco] at h
    have hinnerR : (#{a ∈ F' | a ∈ Finset.Ico u (u + (len : ℤ))} : ℝ) ≤ (len : ℝ) := by
      exact_mod_cast hinner
    have hsplitR : (#{a ∈ F' | a ∈ Finset.Ico u (u + (len : ℤ))} : ℝ) +
        (#{a ∈ F' | a ∉ Finset.Ico u (u + (len : ℤ))} : ℝ) = (#F' : ℝ) := by
      exact_mod_cast hsplit
    rw [hcard'] at hsplitR hlen
    nlinarith
  · -- alternative (ii): `F` is almost entirely odd
    have hevN : (#{a ∈ F | Even a} : ℝ) ≤ 54 * rho N * N := by
      rw [← card_filter_even_image_intCast]
      exact hev
    have hodd : #{a ∈ F | ¬ Even a} ≤ (N + 1) / 2 := by
      calc #{a ∈ F | ¬ Even a} ≤ #{x ∈ Finset.Icc 1 N | Odd x} := by
            refine Finset.card_le_card fun a ha => ?_
            rw [Finset.mem_filter] at ha ⊢
            exact ⟨hF ha.1, Nat.not_even_iff_odd.1 ha.2⟩
        _ = (N + 1) / 2 := card_filter_odd_Icc N
    have hsum : #{a ∈ F | Even a} + #{a ∈ F | ¬ Even a} = #F :=
      Finset.card_filter_add_card_filter_not _
    have hsumR : (#{a ∈ F | Even a} : ℝ) + (#{a ∈ F | ¬ Even a} : ℝ) = (#F : ℝ) := by
      exact_mod_cast hsum
    have hoddR : (#{a ∈ F | ¬ Even a} : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
      have hc : ((#{a ∈ F | ¬ Even a} : ℕ) : ℝ) ≤ (((N + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hodd
      have h := Nat.cast_div_le (α := ℝ) (m := N + 1) (n := 2)
      push_cast at h
      linarith
    linarith

/-! ## Proposition 12 -/

/-- **Proposition 12** (Alon; Calkin–Erdős–Granville; Green, Prop. 12).  For every
`θ > 0` the number of sum-free subsets of `[1, N]` is eventually at most
`2^{(1/2 + θ)N}`. -/
theorem eventually_sumFreeCount_le (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, (sumFreeCount N : ℝ) ≤ 2 ^ ((1 / 2 + θ) * (N : ℝ)) := by
  have hhalf : 0 < θ / 2 := by linarith
  -- `54 ρ_N N + 1 ≤ (θ/2) N` eventually
  have hgapE : ∀ᶠ N : ℕ in atTop, 54 * rho N * N + 1 ≤ θ / 2 * N := by
    have h1 : ∀ᶠ N : ℕ in atTop, rho N ≤ θ / 216 :=
      rho_tendsto_zero.eventually_le_const (by positivity)
    have h2 : ∀ᶠ N : ℕ in atTop, (4 / θ : ℝ) ≤ (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [h1, h2] with N ha hb
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h3 : 54 * rho N * N ≤ θ / 4 * N := by nlinarith
    have h4 : (4 : ℝ) ≤ (N : ℝ) * θ := (div_le_iff₀ hθ).1 hb
    linarith
  filter_upwards [eventually_container_family (θ / 2) hhalf, eventually_rho_small, hgapE]
    with N hfam hρ hgap
  obtain ⟨𝓕, hFcard, hFmem, hFcov⟩ := hfam
  -- every sum-free subset of `[1, N]` lies in the powerset of some container
  have hsub : {A ∈ (Finset.Icc 1 N).powerset | IsSumFree A} ⊆
      𝓕.biUnion (fun F => F.powerset) := by
    intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    obtain ⟨F, hF, hAF⟩ := hFcov A hA.1 hA.2
    exact Finset.mem_biUnion.2 ⟨F, hF, Finset.mem_powerset.2 hAF⟩
  have h1 : sumFreeCount N ≤ ∑ F ∈ 𝓕, 2 ^ #F := by
    calc sumFreeCount N ≤ #(𝓕.biUnion fun F => F.powerset) := Finset.card_le_card hsub
      _ ≤ ∑ F ∈ 𝓕, #(F.powerset) := Finset.card_biUnion_le
      _ = ∑ F ∈ 𝓕, 2 ^ #F := by simp [Finset.card_powerset]
  -- each container contributes at most `2^{(1/2 + θ/2)N}`
  have hbnd : ∀ F ∈ 𝓕, ((2 : ℝ) ^ #F) ≤ (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) := by
    intro F hF
    obtain ⟨hFsub, hFtr⟩ := hFmem F hF
    have hcc := card_container_le N F hFsub hρ hFtr
    have hexp : (1 / 2 + 54 * rho N) * (N : ℝ) + 1
        = 1 / 2 * (N : ℝ) + (54 * rho N * N + 1) := by ring
    rw [hexp] at hcc
    rw [← Real.rpow_natCast (2 : ℝ) #F]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith
  have h1R : (sumFreeCount N : ℝ) ≤ ∑ F ∈ 𝓕, ((2 : ℝ) ^ #F) := by exact_mod_cast h1
  have h2 : (sumFreeCount N : ℝ) ≤ (#𝓕 : ℝ) * (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) := by
    calc (sumFreeCount N : ℝ) ≤ ∑ F ∈ 𝓕, ((2 : ℝ) ^ #F) := h1R
      _ ≤ ∑ F ∈ 𝓕, (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) := Finset.sum_le_sum hbnd
      _ = (#𝓕 : ℝ) * (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc (sumFreeCount N : ℝ) ≤ (#𝓕 : ℝ) * (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) := h2
    _ ≤ (2 : ℝ) ^ (θ / 2 * (N : ℝ)) * (2 : ℝ) ^ ((1 / 2 + θ / 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hFcard hpos.le
    _ = (2 : ℝ) ^ ((1 / 2 + θ) * (N : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring_nf

/-- **Proposition 12, shifted form.**  The bound of `eventually_sumFreeCount_le` applied at
`N′ = N − ⌊N/120⌋`, as required by the subcase (20) of Corollary 13. -/
theorem eventually_sumFreeCount_shift_le (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop,
      (sumFreeCount (N - N / 120) : ℝ) ≤ 2 ^ ((1 / 2 + θ) * ((N - N / 120 : ℕ) : ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (eventually_sumFreeCount_le θ hθ)
  refine Filter.eventually_atTop.2 ⟨2 * N₀ + 2, fun N hN => hN₀ _ ?_⟩
  omega

end CameronErdos

/-! ## Axiom audit -/

#print axioms CameronErdos.card_image_intCast
#print axioms CameronErdos.image_intCast_subset
#print axioms CameronErdos.addTriples_image_intCast
#print axioms CameronErdos.card_filter_even_image_intCast
#print axioms CameronErdos.card_container_le
#print axioms CameronErdos.eventually_sumFreeCount_le
#print axioms CameronErdos.eventually_sumFreeCount_shift_le
