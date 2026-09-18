import CameronErdos.Part1.Prop6
import CameronErdos.Part2.Prop7
import CameronErdos.Part2.Cor13Even
import CameronErdos.Part2.Cor13Matching
import CameronErdos.Part2.Cor13Numerics
import CameronErdos.Assembly
import CameronErdos.Part2.Prop12

/-!
# `Thm_Cor13`: Green's Corollary 13 — the exceptional class has size `≤ 2^{N/2}`

Green, *The Cameron–Erdős conjecture* (2004), Corollary 13 (pp. 10–11).

Let `A ⊆ [1, N]` be sum-free, neither all-odd nor contained in the top third
`[⌈(N+1)/3⌉, N]` (`CameronErdos.exceptional`).  Proposition 6
(`eventually_container_family`) puts `A` inside a container `F ⊆ [1, N]` with few additive
triples, coming from a family `𝓕` of size at most `2^{θN}` with `θ = 1/1000`.  Writing
`ρ = ρ_N = (64 ε_N)^{1/8}`, `N' = N − ⌊N/120⌋` and `w = ⌈(1/2 − 1/30 − 60ρ)N⌉`, the four
classes

* `ClassA N 𝓕` — `A` sits in a *small* container, `|F| < (1/2 − 1/120)N`;
* `EvenPoorNotOdd N (54ρN)` — `A` has at least one but at most `54ρN` even elements;
* `ClassC N (32ρN)` — `A` has at most `32ρN` elements above `N'`;
* `SmallElemFamily N w ⌊32ρN⌋` — `A` has at most `32ρN` elements below `w` and contains a
  small element `t` with `3t ≤ N`

cover `exceptional N` (`CameronErdos.exceptional_subset`), and each has at most
`2^{0.498 N}` members (`Lem_Cor13_Numerics`, estimates `N1`–`N4`).  Adding the four and
applying `N5` gives the target

`CameronErdos.eventually_exceptional_le : ∀ᶠ N, (#(exceptional N) : ℝ) ≤ 2^{N/2}`.

The count for `ClassC` needs Proposition 12 (`sumFreeCount N ≤ 2^{(1/2 + θ)N}`) at `N'`;
that dependence is isolated in `eventually_exceptional_le_of_prop12`, which takes the
Proposition 12 bound at `N'` as a hypothesis.
-/

open Finset Filter Topology

namespace CameronErdos

/-! ## Transfer of `Finset ℕ` data along the cast `ℕ → ℤ` -/

/-- The `ℤ`-image of a finite set of naturals. -/
local notation "ι" => (Nat.castEmbedding : ℕ ↪ ℤ)

lemma natCast_mem_map {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) : (a : ℤ) ∈ A.map ι :=
  Finset.mem_map_of_mem _ ha

lemma map_natCast_subset_Icc {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    A.map ι ⊆ Finset.Icc (1 : ℤ) (N : ℤ) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
  have h := hA ha
  simp only [Finset.mem_Icc] at h
  simp only [Nat.castEmbedding_apply, Finset.mem_Icc]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Additive triples do not increase under the cast `ℕ → ℤ` (in fact they are preserved). -/
lemma addTriples_map_natCast_le (A : Finset ℕ) : addTriples (A.map ι) ≤ addTriples A := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun t : ℤ × ℤ × ℤ => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) ?_ ?_
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_map,
      Nat.castEmbedding_apply] at ht
    obtain ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩⟩, hsum⟩ := ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Int.toNat_natCast]
    exact ⟨⟨ha, hb, hc⟩, by exact_mod_cast hsum⟩
  · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_map,
      Nat.castEmbedding_apply] at ht ht'
    obtain ⟨⟨⟨a, -, rfl⟩, ⟨b, -, rfl⟩, ⟨c, -, rfl⟩⟩, -⟩ := ht
    obtain ⟨⟨⟨a', -, rfl⟩, ⟨b', -, rfl⟩, ⟨c', -, rfl⟩⟩, -⟩ := ht'
    simp only [Prod.mk.injEq, Int.toNat_natCast] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3; rfl

/-- `ρ_N` is exactly the quantity `ε^{1/8}` appearing in Proposition 7 for
`ε = 64 ε_N`. -/
lemma rho_def (N : ℕ) :
    Real.sqrt (Real.sqrt (Real.sqrt (64 * epsN N))) = rho N := rfl

/-! ## The classes `C_a` and `C_c` -/

/-- `C_a`: the sets covered by a *small* container, `|F| < (1/2 − 1/120)N`. -/
noncomputable def ClassA (N : ℕ) (𝓕 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (𝓕.filter (fun F => (#F : ℝ) < (1 / 2 - 1 / 120 : ℝ) * N)).biUnion Finset.powerset

/-- `C_c`: the sum-free subsets of `[1, N]` with at most `k` elements above
`N' = N − ⌊N/120⌋`. -/
noncomputable def ClassC (N : ℕ) (k : ℝ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun A => IsSumFree A ∧ (#(A \ Finset.Icc 1 (N - N / 120)) : ℝ) ≤ k)

lemma mem_classC {N : ℕ} {k : ℝ} {A : Finset ℕ} :
    A ∈ ClassC N k ↔ A ⊆ Finset.Icc 1 N ∧ IsSumFree A ∧
      (#(A \ Finset.Icc 1 (N - N / 120)) : ℝ) ≤ k := by
  classical
  rw [ClassC, Finset.mem_filter, Finset.mem_powerset]

/-! ## Counting `C_a` -/

lemma card_classA_le (N : ℕ) (𝓕 : Finset (Finset ℕ)) :
    (#(ClassA N 𝓕) : ℝ) ≤ (#𝓕 : ℝ) * 2 ^ ((1 / 2 - 1 / 120 : ℝ) * N) := by
  classical
  set 𝓖 : Finset (Finset ℕ) := 𝓕.filter (fun F => (#F : ℝ) < (1 / 2 - 1 / 120 : ℝ) * N)
    with h𝓖
  have h1 : #(ClassA N 𝓕) ≤ ∑ F ∈ 𝓖, 2 ^ #F := by
    refine le_trans Finset.card_biUnion_le ?_
    exact le_of_eq (Finset.sum_congr rfl fun F _ => Finset.card_powerset F)
  have h2 : ∀ F ∈ 𝓖, ((2 ^ #F : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) := by
    intro F hF
    have hF' : (#F : ℝ) < (1 / 2 - 1 / 120 : ℝ) * N := (Finset.mem_filter.1 hF).2
    calc ((2 ^ #F : ℕ) : ℝ) = (2 : ℝ) ^ ((#F : ℕ) : ℝ) := by
          push_cast
          rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hF'.le
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc (#(ClassA N 𝓕) : ℝ) ≤ ((∑ F ∈ 𝓖, 2 ^ #F : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ F ∈ 𝓖, ((2 ^ #F : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ∑ _F ∈ 𝓖, (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) := Finset.sum_le_sum h2
    _ = (#𝓖 : ℝ) * (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (#𝓕 : ℝ) * (2 : ℝ) ^ ((1 / 2 - 1 / 120 : ℝ) * N) := by
        refine mul_le_mul_of_nonneg_right ?_ h3
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ## Counting `C_c` -/

/-- Splitting `A` into `A ∩ [1, N']` (sum-free) and the at most `k` elements above `N'`
bounds `C_c` by `f(N') · ∑_{j ≤ k} C(N, j)`. -/
lemma card_classC_le (N : ℕ) (k : ℝ) :
    #(ClassC N k) ≤
      sumFreeCount (N - N / 120) * ∑ j ∈ Finset.range (⌊k⌋₊ + 1), N.choose j := by
  classical
  set N' : ℕ := N - N / 120 with hN'
  set S : Finset (Finset ℕ) := (Finset.Icc 1 N').powerset.filter IsSumFree with hS
  set T : Finset (Finset ℕ) := {E ∈ (Finset.Icc 1 N).powerset | #E ≤ ⌊k⌋₊} with hT
  have hmain : #(ClassC N k) ≤ #(S ×ˢ T) := by
    refine Finset.card_le_card_of_injOn
      (fun A => (A ∩ Finset.Icc 1 N', A \ Finset.Icc 1 N')) ?_ ?_
    · intro A hA
      rw [Finset.mem_coe, mem_classC] at hA
      obtain ⟨hAsub, hAsf, hAk⟩ := hA
      refine Finset.mem_product.2 ⟨?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.inter_subset_right, hAsf.subset Finset.inter_subset_left⟩
      · rw [hT, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.sdiff_subset.trans hAsub, Nat.le_floor hAk⟩
    · intro A _ B _ hAB
      simp only [Prod.mk.injEq] at hAB
      have hA' : A \ Finset.Icc 1 N' ∪ A ∩ Finset.Icc 1 N' = A :=
        Finset.sdiff_union_inter A (Finset.Icc 1 N')
      have hB' : B \ Finset.Icc 1 N' ∪ B ∩ Finset.Icc 1 N' = B :=
        Finset.sdiff_union_inter B (Finset.Icc 1 N')
      rw [← hA', ← hB', hAB.1, hAB.2]
  have hScard : #S = sumFreeCount N' := rfl
  have hTcard : #T ≤ ∑ j ∈ Finset.range (⌊k⌋₊ + 1), N.choose j := by
    have h := card_powerset_card_le (Finset.Icc 1 N) ⌊k⌋₊
    simpa only [hT, Nat.card_Icc, Nat.add_sub_cancel] using h
  rw [Finset.card_product, hScard] at hmain
  exact hmain.trans (Nat.mul_le_mul_left _ hTcard)


/-! ## The covering lemma -/

/-- **Green's Corollary 13, covering step.**  Every exceptional set lies in one of the four
classes `C_a`, `C_b`, `C_c`, `C_d`. -/
lemma exceptional_subset {N : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hfam : ∀ F ∈ 𝓕, F ⊆ Finset.Icc 1 N ∧ (addTriples F : ℝ) ≤ 64 * epsN N * (N : ℝ) ^ 2)
    (hcov : ∀ A ⊆ Finset.Icc 1 N, IsSumFree A → ∃ F ∈ 𝓕, A ⊆ F)
    (hρpos : 0 < rho N) (hρsmall : rho N ≤ 1 / 10 ^ 4)
    (hρN : (1000 : ℝ) ≤ rho N * N) (hεsmall : 64 * epsN N ≤ 1 / 10 ^ 32) :
    exceptional N ⊆
      ClassA N 𝓕 ∪ (EvenPoorNotOdd N (54 * rho N * N) ∪
        (ClassC N (32 * rho N * N) ∪
          SmallElemFamily N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
            ⌊32 * rho N * (N : ℝ)⌋₊)) := by
  classical
  intro A hA
  obtain ⟨hAsub, hAsf, hAodd, hAint⟩ := mem_exceptional.1 hA
  obtain ⟨F, hF𝓕, hAF⟩ := hcov A hAsub hAsf
  obtain ⟨hFsub, hFtr⟩ := hfam F hF𝓕
  by_cases hsmall : (#F : ℝ) < (1 / 2 - 1 / 120 : ℝ) * N
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.2 ⟨F, Finset.mem_filter.2 ⟨hF𝓕, hsmall⟩, Finset.mem_powerset.2 hAF⟩)
  replace hsmall : (1 / 2 - 1 / 120 : ℝ) * N ≤ (#F : ℝ) := not_lt.1 hsmall
  refine Finset.mem_union_right _ ?_
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hρnn : (0 : ℝ) ≤ rho N := rho_nonneg N
  have hρNnn : (0 : ℝ) ≤ rho N * N := mul_nonneg hρnn hNnn
  have hεpos : 0 < 64 * epsN N :=
    Real.sqrt_pos.1 (Real.sqrt_pos.1 (Real.sqrt_pos.1 hρpos))
  set F' : Finset ℤ := F.map (Nat.castEmbedding : ℕ ↪ ℤ) with hF'def
  have hcardF' : (#F' : ℝ) = (#F : ℝ) := by rw [hF'def, Finset.card_map]
  have h7 := prop7 (N := N) (A := F') (map_natCast_subset_Icc hFsub) hεpos hεsmall
    (by rw [rho_def]; exact hρN)
    (by rw [hcardF']; exact hsmall)
    (by
      refine le_trans ?_ hFtr
      exact_mod_cast addTriples_map_natCast_le F)
  rw [rho_def] at h7
  rcases h7 with ⟨u, len, hlen, hexc⟩ | heven
  · -- alternative (i): all but `32ρN` elements of `F` lie in `[u, u + len)`
    refine Finset.mem_union_right _ ?_
    by_cases hc : (#(A \ Finset.Icc 1 (N - N / 120)) : ℝ) ≤ 32 * rho N * N
    · exact Finset.mem_union_left _ (mem_classC.2 ⟨hAsub, hAsf, hc⟩)
    replace hc : 32 * rho N * (N : ℝ) < (#(A \ Finset.Icc 1 (N - N / 120)) : ℝ) := not_le.1 hc
    refine Finset.mem_union_right _ ?_
    rw [mem_smallElemFamily]
    refine ⟨hAsub, hAsf, ?_, ?_⟩
    · set N' : ℕ := N - N / 120 with hN'def
      set w : ℕ := ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊ with hwdef
      have hExists : ∃ a ∈ A \ Finset.Icc 1 N', (a : ℤ) ∈ Finset.Ico u (u + len) := by
        by_contra hcon
        have hcon' : ∀ a ∈ A \ Finset.Icc 1 N', (a : ℤ) ∉ Finset.Ico u (u + len) :=
          fun a ha hp => hcon ⟨a, ha, hp⟩
        have hle : #(A \ Finset.Icc 1 N') ≤ #{b ∈ F' | b ∉ Finset.Ico u (u + len)} := by
          refine Finset.card_le_card_of_injOn (fun a : ℕ => (a : ℤ)) ?_ ?_
          · intro a ha
            exact Finset.mem_filter.2
              ⟨natCast_mem_map (hAF (Finset.mem_sdiff.1 ha).1), hcon' a ha⟩
          · intro a _ b _ hab
            exact Nat.cast_injective hab
        have hle' : (#(A \ Finset.Icc 1 N') : ℝ)
            ≤ (#{b ∈ F' | b ∉ Finset.Ico u (u + len)} : ℝ) := by exact_mod_cast hle
        linarith
      obtain ⟨a, haD, hau⟩ := hExists
      rw [Finset.mem_sdiff] at haD
      have haA : a ∈ A := haD.1
      have haN' : N' < a := by
        have h1 := hAsub haA
        have h2 := haD.2
        simp only [Finset.mem_Icc] at h1 h2
        omega
      rw [Finset.mem_Ico] at hau
      have hexpand : 2 * (N : ℝ) * (1 + 30 * rho N) = 2 * N + 60 * (rho N * N) := by ring
      have hlen' : (len : ℝ) ≤ (1 / 2 + 1 / 40) * N + 60 * (rho N * N) := by
        rw [hcardF', hexpand] at hlen
        linarith
      have hN'R : (119 / 120 : ℝ) * N ≤ (N' : ℝ) := by
        have h1 : ((N / 120 : ℕ) : ℝ) ≤ (N : ℝ) / 120 := Nat.cast_div_le
        have h2 : ((N' : ℕ) : ℝ) = (N : ℝ) - ((N / 120 : ℕ) : ℝ) := by
          rw [hN'def, Nat.cast_sub (Nat.div_le_self N 120)]
        rw [h2]; linarith
      have hauR : (N' : ℝ) + 1 - (len : ℝ) < (u : ℝ) := by
        have h1 : ((a : ℤ) : ℝ) < (u : ℝ) + (len : ℝ) := by exact_mod_cast hau.2
        have h2 : (N' : ℝ) + 1 ≤ ((a : ℤ) : ℝ) := by exact_mod_cast haN'
        push_cast at h1 h2 ⊢
        linarith
      have hxnn : (0 : ℝ) ≤ (1 / 2 - 1 / 30 - 60 * rho N) * N := by
        refine mul_nonneg ?_ hNnn
        linarith
      have hwlt : (w : ℝ) < (1 / 2 - 1 / 30 - 60 * rho N) * N + 1 := Nat.ceil_lt_add_one hxnn
      have hexp2 : (1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)
          = (1 / 2 - 1 / 30) * N - 60 * (rho N * N) := by ring
      have hwu : (w : ℤ) ≤ u := by
        rw [hexp2] at hwlt
        have hlt : (w : ℝ) < (u : ℝ) := by linarith
        have : ((w : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have hfin : #(A \ Finset.Icc w N) ≤ #{b ∈ F' | b ∉ Finset.Ico u (u + len)} := by
        refine Finset.card_le_card_of_injOn (fun a : ℕ => (a : ℤ)) ?_ ?_
        · intro b hb
          have hb' : b ∈ A ∧ b ∉ Finset.Icc w N := Finset.mem_sdiff.1 hb
          have hb1 := hAsub hb'.1
          simp only [Finset.mem_Icc] at hb1
          have hbw' : b < w := by
            by_contra hcon
            exact hb'.2 (Finset.mem_Icc.2 ⟨by omega, hb1.2⟩)
          have hbw : (b : ℤ) < (w : ℤ) := by exact_mod_cast hbw'
          refine Finset.mem_filter.2 ⟨natCast_mem_map (hAF hb'.1), ?_⟩
          intro hmem
          have hmem' : u ≤ (b : ℤ) ∧ (b : ℤ) < u + (len : ℤ) := Finset.mem_Ico.1 hmem
          omega
        · intro a _ b _ hab
          exact Nat.cast_injective hab
      have hfinR : (#(A \ Finset.Icc w N) : ℝ) ≤ 32 * rho N * N := by
        have h := (Nat.cast_le (α := ℝ)).2 hfin
        linarith
      exact Nat.le_floor hfinR
    · obtain ⟨t, htA, htn⟩ := Finset.not_subset.1 hAint
      refine ⟨t, htA, ?_⟩
      have h1 := hAsub htA
      simp only [Finset.mem_Icc] at h1
      have htn' : t < topThird N := by
        by_contra hcon
        exact htn (Finset.mem_Icc.2 ⟨by omega, h1.2⟩)
      unfold topThird at htn'
      omega
  · -- alternative (ii): `F`, hence `A`, has few even elements
    refine Finset.mem_union_left _ ?_
    simp only [EvenPoorNotOdd, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hAsub, hAsf, ?_, ?_⟩
    · have hle : #(A.filter Even) ≤ #{b ∈ F' | Even b} := by
        refine Finset.card_le_card_of_injOn (fun a : ℕ => (a : ℤ)) ?_ ?_
        · intro a ha
          have ha' : a ∈ A ∧ Even a := Finset.mem_filter.1 ha
          refine Finset.mem_filter.2 ⟨natCast_mem_map (hAF ha'.1), ?_⟩
          show Even ((a : ℤ))
          exact_mod_cast ha'.2
        · intro a _ b _ hab
          exact Nat.cast_injective hab
      have h := (Nat.cast_le (α := ℝ)).2 hle
      linarith
    · by_contra hcon
      refine hAodd fun a ha => ?_
      rcases Nat.even_or_odd a with he | ho
      · exact absurd ⟨a, Finset.mem_filter.2 ⟨ha, he⟩⟩ hcon
      · exact ho

/-! ## `Thm_Cor13`, conditional on Proposition 12 -/

/-- **`Thm_Cor13`**, with the Proposition 12 bound at `N' = N − ⌊N/120⌋` as a hypothesis:
the exceptional class has at most `2^{N/2}` members for all large `N`. -/
theorem eventually_exceptional_le_of_prop12
    (h12 : ∀ᶠ N : ℕ in atTop,
      (sumFreeCount (N - N / 120) : ℝ)
        ≤ 2 ^ ((1 / 2 + 1 / 1000 : ℝ) * ((N - N / 120 : ℕ) : ℝ))) :
    ∀ᶠ N : ℕ in atTop, (#(exceptional N) : ℝ) ≤ 2 ^ ((N : ℝ) / 2) := by
  classical
  filter_upwards [eventually_container_family (1 / 1000) (by norm_num), eventually_rho_small,
    numerics_N1, numerics_N2, numerics_N3, numerics_N4, numerics_N5,
    eventually_small_binomial_rho 54 (1 / 1000) (by norm_num) (by norm_num),
    eventually_small_binomial_rho 32 (1 / 1000) (by norm_num) (by norm_num),
    h12, eventually_ge_atTop 100] with
    N hfam hrho hn1 hn2 hn3 hn4 hn5 hbin54 hbin32 hprop12 hN100
  obtain ⟨𝓕, h𝓕card, h𝓕mem, h𝓕cov⟩ := hfam
  obtain ⟨hρpos, hρsmall, hρN, hεsmall⟩ := hrho
  have hNR : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN100
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hρnn : (0 : ℝ) ≤ rho N := rho_nonneg N
  have hρNnn : (0 : ℝ) ≤ rho N * (N : ℝ) := mul_nonneg hρnn hNnn
  have h54nn : (0 : ℝ) ≤ 54 * rho N * (N : ℝ) := by
    have h : 54 * rho N * (N : ℝ) = 54 * (rho N * N) := by ring
    rw [h]; linarith
  have h32nn : (0 : ℝ) ≤ 32 * rho N * (N : ℝ) := by
    have h : 32 * rho N * (N : ℝ) = 32 * (rho N * N) := by ring
    rw [h]; linarith
  have hthou : (1 / 1000 : ℝ) * (N : ℝ) = (N : ℝ) / 1000 := by ring
  have hpow2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) / 1000) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  -- ### the class `C_a`
  have hCa : (#(ClassA N 𝓕) : ℝ) ≤ 2 ^ ((0.498 : ℝ) * N) := by
    refine le_trans (card_classA_le N 𝓕) ?_
    refine le_trans (mul_le_mul_of_nonneg_right h𝓕card
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))) ?_
    rw [hthou]
    exact hn1
  -- ### the class `C_b`
  have hbinsum54 :
      (∑ j ∈ Finset.range (⌊54 * rho N * (N : ℝ)⌋₊ + 1), (((N / 2).choose j : ℕ) : ℝ))
        ≤ 2 ^ ((N : ℝ) / 1000) := by
    rw [← hthou]
    exact le_trans (sum_choose_half_le N _) (hbin54 _ (Nat.floor_le h54nn))
  have hCb : (#(EvenPoorNotOdd N (54 * rho N * N)) : ℝ) ≤ 2 ^ ((0.498 : ℝ) * N) := by
    have hnat := card_evenPoorNotOdd_le N (54 * rho N * (N : ℝ)) h54nn
    have h1 : (#(EvenPoorNotOdd N (54 * rho N * N)) : ℝ)
        ≤ (∑ j ∈ Finset.range (⌊54 * rho N * (N : ℝ)⌋₊ + 1), (((N / 2).choose j : ℕ) : ℝ))
            * ((N / 2 : ℕ) : ℝ) * (3 : ℝ) ^ (N / 8) *
            (2 : ℝ) ^ ((N + 1) / 2 - 2 * (N / 8)) := by
      exact_mod_cast hnat
    refine le_trans h1 (le_trans ?_ hn2)
    have ha : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ (3 : ℝ) ^ (N / 8) := by positivity
    have hc : (0 : ℝ) ≤ (2 : ℝ) ^ ((N + 1) / 2 - 2 * (N / 8)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbinsum54 ha) hb) hc
  -- ### the class `C_c`
  have hbinsum32 :
      (∑ j ∈ Finset.range (⌊32 * rho N * (N : ℝ)⌋₊ + 1), ((N.choose j : ℕ) : ℝ))
        ≤ 2 ^ ((N : ℝ) / 1000) := by
    rw [← hthou]
    exact hbin32 _ (Nat.floor_le h32nn)
  have hCc : (#(ClassC N (32 * rho N * N)) : ℝ) ≤ 2 ^ ((0.498 : ℝ) * N) := by
    have hnat := card_classC_le N (32 * rho N * (N : ℝ))
    have h1 : (#(ClassC N (32 * rho N * N)) : ℝ)
        ≤ (sumFreeCount (N - N / 120) : ℝ) *
            ∑ j ∈ Finset.range (⌊32 * rho N * (N : ℝ)⌋₊ + 1), ((N.choose j : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine le_trans h1 (le_trans ?_ hn3)
    refine mul_le_mul hprop12 hbinsum32 (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  -- ### the class `C_d`
  have hwle : ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊ ≤ N / 2 := by
    have hxnn : (0 : ℝ) ≤ (1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ) :=
      mul_nonneg (by linarith) hNnn
    have hceil := Nat.ceil_lt_add_one hxnn
    have hexp : (1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)
        = (1 / 2 - 1 / 30) * N - 60 * (rho N * N) := by ring
    have hdiv : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      have h : N ≤ 2 * (N / 2) + 1 := by omega
      exact_mod_cast h
    have hfin : ((⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
      linarith
    exact_mod_cast hfin
  have hCd : (#(SmallElemFamily N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
      ⌊32 * rho N * (N : ℝ)⌋₊) : ℝ) ≤ 2 ^ ((0.498 : ℝ) * N) := by
    have hnat := card_smallElemFamily_le N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
      ⌊32 * rho N * (N : ℝ)⌋₊ (by omega) hwle
    have h1 : (#(SmallElemFamily N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
        ⌊32 * rho N * (N : ℝ)⌋₊) : ℝ)
        ≤ (N : ℝ) * (∑ j ∈ Finset.range (⌊32 * rho N * (N : ℝ)⌋₊ + 1), ((N.choose j : ℕ) : ℝ))
            * (3 : ℝ) ^ (N / 8 - 4) *
            (2 : ℝ) ^ ((N + 1 - ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊) -
              2 * (N / 8 - 4)) := by
      exact_mod_cast hnat
    refine le_trans h1 (le_trans ?_ hn4)
    have hstep : (N : ℝ) *
        (∑ j ∈ Finset.range (⌊32 * rho N * (N : ℝ)⌋₊ + 1), ((N.choose j : ℕ) : ℝ))
          ≤ (N : ℝ) * 2 ^ ((N : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left hbinsum32 hNnn
    have hb : (0 : ℝ) ≤ (3 : ℝ) ^ (N / 8 - 4) := by positivity
    have hc : (0 : ℝ) ≤ (2 : ℝ) ^ ((N + 1 - ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊) -
        2 * (N / 8 - 4)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hb) hc
  -- ### the union bound
  have hcover := exceptional_subset h𝓕mem h𝓕cov hρpos hρsmall hρN hεsmall
  have hcard : #(exceptional N) ≤ #(ClassA N 𝓕) + (#(EvenPoorNotOdd N (54 * rho N * N)) +
      (#(ClassC N (32 * rho N * N)) +
        #(SmallElemFamily N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
          ⌊32 * rho N * (N : ℝ)⌋₊))) := by
    refine le_trans (Finset.card_le_card hcover) ?_
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_union_le _ _) _)
  have hcardR : (#(exceptional N) : ℝ) ≤ (#(ClassA N 𝓕) : ℝ) +
      ((#(EvenPoorNotOdd N (54 * rho N * N)) : ℝ) +
        ((#(ClassC N (32 * rho N * N)) : ℝ) +
          (#(SmallElemFamily N ⌈(1 / 2 - 1 / 30 - 60 * rho N) * (N : ℝ)⌉₊
            ⌊32 * rho N * (N : ℝ)⌋₊) : ℝ))) := by
    exact_mod_cast hcard
  linarith


/-! ## `Thm_Cor13` -/

/-- **`Thm_Cor13`** (Green 2004, Corollary 13).  For all large `N` the exceptional class —
the sum-free subsets of `[1, N]` that are neither all-odd nor contained in the top third
`[⌈(N+1)/3⌉, N]` — has at most `2^{N/2}` members. -/
theorem eventually_exceptional_le :
    ∀ᶠ N : ℕ in atTop, (#(exceptional N) : ℝ) ≤ 2 ^ ((N : ℝ) / 2) :=
  eventually_exceptional_le_of_prop12
    (eventually_sumFreeCount_shift_le (1 / 1000) (by norm_num))

end CameronErdos

/-! ## Axiom audit -/

#print axioms CameronErdos.natCast_mem_map
#print axioms CameronErdos.map_natCast_subset_Icc
#print axioms CameronErdos.addTriples_map_natCast_le
#print axioms CameronErdos.rho_def
#print axioms CameronErdos.mem_classC
#print axioms CameronErdos.card_classA_le
#print axioms CameronErdos.card_classC_le
#print axioms CameronErdos.exceptional_subset
#print axioms CameronErdos.eventually_exceptional_le_of_prop12
#print axioms CameronErdos.eventually_exceptional_le
