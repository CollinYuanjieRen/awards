import CameronErdos.Part1.Granularization
import CameronErdos.Counting.Basic
import CameronErdos.Part2.Cor13Even

/-!
# The container family `F` (Green 2004, §3)

This file formalizes `Def_Family` and parts (i) and (iii) of `Prop6_Family` from Green,
*The Cameron–Erdős conjecture* (2004), §3 (see `ref/green-cameron-erdos-0304058.pdf`,
pp. 6–7).

Fix `N` and a prime `p ∈ [2N, 4N]`.  Green's family `F` consists of the sets

`container N p d M S E = {a ∈ [1, N] : a mod p ∈ ⋃_{i ∈ S} I i} ∪ E`,

where `d ≠ 0` is a common difference, `S ⊆ [0, M)` selects a union of progressions
`I i = block d M i` whose union `containerU p d M S` has at most `ε p²` additive triples,
and `E ⊆ [1, N]` is an exceptional set of size at most `ε p`.

The main results are:

* `CameronErdos.card_family_le` — part (iii): `|F| ≤ p · 2^M · ∑_{j ≤ ⌊εp⌋} C(N, j)`;
* `CameronErdos.addTriples_family_le` — part (i): every `F ∈ F` has at most `64 ε N²`
  additive triples;

together with the transfer lemmas between `[1, N] ⊆ ℕ` and `ZMod p` used in part (i)
and (later) part (ii).
-/

open Finset

namespace CameronErdos

variable {N p : ℕ} [NeZero p] {d : ZMod p} {M : ℕ} {S E : Finset ℕ} {ε : ℝ}

/-! ## Unions of progressions and containers -/

/-- `containerU p d M S = ⋃_{i ∈ S} I i`, a union of progressions of common difference `d`.
These are exactly the members of Green's family `G`. -/
def containerU (p : ℕ) [NeZero p] (d : ZMod p) (M : ℕ) (S : Finset ℕ) : Finset (ZMod p) :=
  S.biUnion (block d M)

/-- The granularization `A'` of `A` is the union of the progressions indexed by the dense
indices, hence a member of Green's family `G`. -/
lemma granularization_eq_containerU (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ : ℝ) :
    granularization A d M ε₁ = containerU p d M (denseIdx A d M ε₁) := rfl

lemma mem_containerU {x : ZMod p} :
    x ∈ containerU p d M S ↔ ∃ i ∈ S, x ∈ block d M i := by
  simp [containerU]

/-- `container N p d M S E = {a ∈ [1, N] : ā ∈ ⋃_{i ∈ S} I i} ∪ E`, a typical member of
Green's family `F`. -/
def container (N p : ℕ) [NeZero p] (d : ZMod p) (M : ℕ) (S E : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun a => (a : ZMod p) ∈ containerU p d M S) ∪ E

lemma container_subset_Icc (hE : E ⊆ Finset.Icc 1 N) :
    container N p d M S E ⊆ Finset.Icc 1 N :=
  Finset.union_subset (Finset.filter_subset _ _) hE

/-- The image of a container in `ZMod p` is contained in the corresponding union of
progressions together with the image of the exceptional set. -/
lemma image_container_subset (N p : ℕ) [NeZero p] (d : ZMod p) (M : ℕ) (S E : Finset ℕ) :
    (container N p d M S E).image (Nat.cast : ℕ → ZMod p) ⊆
      containerU p d M S ∪ E.image (Nat.cast : ℕ → ZMod p) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [container, Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact Finset.mem_union_left _ (Finset.mem_filter.1 ha).2
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)

/-! ## The family `F` -/

/-- **`Def_Family`**.  Green's family `F`: the sets `container N p d M S E` where `d ≠ 0`,
`S ⊆ [0, M)` indexes a union of progressions with at most `ε p²` additive triples, and
`E ⊆ [1, N]` has at most `ε p` elements. -/
noncomputable def family (N p : ℕ) [NeZero p] (M : ℕ) (ε : ℝ) : Finset (Finset ℕ) :=
  (((Finset.univ.erase (0 : ZMod p)) ×ˢ (Finset.range M).powerset ×ˢ
        (Finset.Icc 1 N).powerset).filter
      (fun t => (addTriples (containerU p t.1 M t.2.1) : ℝ) ≤ ε * (p : ℝ) ^ 2 ∧
        (#t.2.2 : ℝ) ≤ ε * (p : ℝ))).image
    (fun t => container N p t.1 M t.2.1 t.2.2)

lemma mem_family_iff {F : Finset ℕ} :
    F ∈ family N p M ε ↔ ∃ d : ZMod p, ∃ S E : Finset ℕ, d ≠ 0 ∧ S ⊆ Finset.range M ∧
      (addTriples (containerU p d M S) : ℝ) ≤ ε * (p : ℝ) ^ 2 ∧ E ⊆ Finset.Icc 1 N ∧
      (#E : ℝ) ≤ ε * (p : ℝ) ∧ container N p d M S E = F := by
  constructor
  · intro hF
    rw [family, Finset.mem_image] at hF
    obtain ⟨t, ht, hteq⟩ := hF
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨hd, hS, hE⟩, hSt, hEc⟩ := ht
    exact ⟨t.1, t.2.1, t.2.2, (Finset.mem_erase.1 hd).1, Finset.mem_powerset.1 hS, hSt,
      Finset.mem_powerset.1 hE, hEc, hteq⟩
  · rintro ⟨d, S, E, hd, hS, hSt, hE, hEc, rfl⟩
    rw [family, Finset.mem_image]
    refine ⟨(d, S, E), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨Finset.mem_erase.2 ⟨hd, Finset.mem_univ _⟩, Finset.mem_powerset.2 hS,
      Finset.mem_powerset.2 hE⟩, hSt, hEc⟩

/-- Every admissible triple of parameters gives a member of the family. -/
theorem mem_family_of (hd : d ≠ 0) (hS : S ⊆ Finset.range M)
    (hSt : (addTriples (containerU p d M S) : ℝ) ≤ ε * (p : ℝ) ^ 2)
    (hE : E ⊆ Finset.Icc 1 N) (hEc : (#E : ℝ) ≤ ε * (p : ℝ)) :
    container N p d M S E ∈ family N p M ε :=
  mem_family_iff.2 ⟨d, S, E, hd, hS, hSt, hE, hEc, rfl⟩

/-- Every member of the family is a subset of `[1, N]`. -/
theorem family_subset_Icc : ∀ F ∈ family N p M ε, F ⊆ Finset.Icc 1 N := by
  intro F hF
  obtain ⟨d, S, E, -, -, -, hE, -, rfl⟩ := mem_family_iff.1 hF
  exact container_subset_Icc hE

/-! ## Part (iii): the size of the family -/

set_option linter.unusedVariables false in
/-- **`Prop6_Family` (iii)**: `|F| ≤ p · 2^M · ∑_{j ≤ ⌊εp⌋} C(N, j)`. -/
theorem card_family_le (hε : 0 ≤ ε) :
    (#(family N p M ε) : ℝ) ≤
      (p : ℝ) * 2 ^ M * ∑ j ∈ Finset.range (⌊ε * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ) := by
  classical
  set m : ℕ := ⌊ε * (p : ℝ)⌋₊ with hm
  set P : Finset (ZMod p × Finset ℕ × Finset ℕ) :=
    (Finset.univ.erase (0 : ZMod p)) ×ˢ (Finset.range M).powerset ×ˢ
      {E ∈ (Finset.Icc 1 N).powerset | #E ≤ m} with hP
  have hsub :
      (((Finset.univ.erase (0 : ZMod p)) ×ˢ (Finset.range M).powerset ×ˢ
        (Finset.Icc 1 N).powerset).filter
      (fun t => (addTriples (containerU p t.1 M t.2.1) : ℝ) ≤ ε * (p : ℝ) ^ 2 ∧
        (#t.2.2 : ℝ) ≤ ε * (p : ℝ))) ⊆ P := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨hd, hS, hE⟩, -, hEc⟩ := ht
    rw [hP, Finset.mem_product, Finset.mem_product]
    exact ⟨hd, hS, Finset.mem_filter.2 ⟨hE, Nat.le_floor hEc⟩⟩
  have hcardP : #P = #(Finset.univ.erase (0 : ZMod p)) *
      (2 ^ M * #{E ∈ (Finset.Icc 1 N).powerset | #E ≤ m}) := by
    rw [hP, Finset.card_product, Finset.card_product, Finset.card_powerset,
      Finset.card_range]
  have hcard1 : #(Finset.univ.erase (0 : ZMod p)) ≤ p := by
    refine le_trans (Finset.card_erase_le) ?_
    rw [Finset.card_univ, ZMod.card]
  have hcard2 : #{E ∈ (Finset.Icc 1 N).powerset | #E ≤ m} ≤
      ∑ j ∈ Finset.range (m + 1), N.choose j := by
    have h := card_powerset_card_le (Finset.Icc 1 N) m
    rwa [Nat.card_Icc] at h
  have hnat : #(family N p M ε) ≤ p * (2 ^ M * ∑ j ∈ Finset.range (m + 1), N.choose j) := by
    refine le_trans Finset.card_image_le ?_
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [hcardP]
    exact Nat.mul_le_mul hcard1 (Nat.mul_le_mul_left _ hcard2)
  have hcast : ((p * (2 ^ M * ∑ j ∈ Finset.range (m + 1), N.choose j) : ℕ) : ℝ) =
      (p : ℝ) * 2 ^ M * ∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ) := by
    push_cast
    ring
  calc (#(family N p M ε) : ℝ)
      ≤ ((p * (2 ^ M * ∑ j ∈ Finset.range (m + 1), N.choose j) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = _ := hcast

/-! ## Transfer between `[1, N]` and `ZMod p` -/

omit [NeZero p] in
/-- Reduction mod `p` is injective on `[1, N]` when `N < p`. -/
theorem cast_injOn_Icc (hp : N < p) :
    Set.InjOn (Nat.cast : ℕ → ZMod p) (Finset.Icc 1 N) := by
  intro a ha b hb hab
  rw [Finset.coe_Icc, Set.mem_Icc] at ha hb
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_le_of_lt ha.2 hp),
    Nat.mod_eq_of_lt (lt_of_le_of_lt hb.2 hp)] at hab
  exact hab

omit [NeZero p] in
/-- If `A ⊆ [1, N]` is sum-free and `2N ≤ p`, then its image in `ZMod p` is sum-free. -/
theorem isSumFree_image {A : Finset ℕ} (hp : 2 * N ≤ p) (hA : A ⊆ Finset.Icc 1 N)
    (hsf : IsSumFree A) :
    ∀ x ∈ A.image (Nat.cast : ℕ → ZMod p), ∀ y ∈ A.image (Nat.cast : ℕ → ZMod p),
      x + y ∉ A.image (Nat.cast : ℕ → ZMod p) := by
  intro x hx y hy hxy
  rw [Finset.mem_image] at hx hy hxy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, hcast⟩ := hxy
  have ha' := Finset.mem_Icc.1 (hA ha)
  have hb' := Finset.mem_Icc.1 (hA hb)
  have hc' := Finset.mem_Icc.1 (hA hc)
  have key : ((a + b : ℕ) : ZMod p) = (c : ZMod p) := by push_cast; exact hcast.symm
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show c < p by omega)] at key
  rcases eq_or_lt_of_le (show a + b ≤ p by omega) with h | h
  · rw [h, Nat.mod_self] at key; omega
  · rw [Nat.mod_eq_of_lt h] at key
    exact hsf a ha b hb (by rw [key]; exact hc)

/-- `addTriples` is monotone under inclusion. -/
theorem addTriples_mono {G : Type*} [Add G] [DecidableEq G] {A B : Finset G} (h : A ⊆ B) :
    addTriples A ≤ addTriples B :=
  Finset.card_le_card
    (Finset.filter_subset_filter _
      (Finset.product_subset_product h (Finset.product_subset_product h h)))

omit [NeZero p] in
/-- Reduction mod `p` does not decrease the number of additive triples of a subset of
`[1, N]` when `N < p`. -/
theorem addTriples_le_addTriples_image {F : Finset ℕ} (hp : N < p) (hF : F ⊆ Finset.Icc 1 N) :
    addTriples F ≤ addTriples (F.image (Nat.cast : ℕ → ZMod p)) := by
  classical
  have hinj := cast_injOn_Icc (N := N) (p := p) hp
  refine Finset.card_le_card_of_injOn
    (fun t => ((t.1 : ZMod p), (t.2.1 : ZMod p), (t.2.2 : ZMod p))) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, heq⟩ := ht
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2,
      Finset.mem_image_of_mem _ h3⟩, ?_⟩
    show ((t.1 : ZMod p) + (t.2.1 : ZMod p)) = (t.2.2 : ZMod p)
    rw [← Nat.cast_add, heq]
  · intro s hs t ht hst
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hs ht
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hs
    obtain ⟨⟨g1, g2, g3⟩, -⟩ := ht
    simp only [Prod.mk.injEq] at hst
    exact Prod.ext_iff.2 ⟨hinj (Finset.mem_coe.2 (hF h1)) (Finset.mem_coe.2 (hF g1)) hst.1,
      Prod.ext_iff.2 ⟨hinj (Finset.mem_coe.2 (hF h2)) (Finset.mem_coe.2 (hF g2)) hst.2.1,
        hinj (Finset.mem_coe.2 (hF h3)) (Finset.mem_coe.2 (hF g3)) hst.2.2⟩⟩

/-! ## Adjoining a small set creates few new triples -/

private lemma triple_ext {G : Type*} [Add G] {s t : G × G × G}
    (hs : s.1 + s.2.1 = s.2.2) (ht : t.1 + t.2.1 = t.2.2)
    (h1 : s.1 = t.1) (h2 : s.2.1 = t.2.1) : s = t :=
  Prod.ext_iff.2 ⟨h1, Prod.ext_iff.2 ⟨h2, by rw [← hs, ← ht, h1, h2]⟩⟩

/-- Adjoining `V` to `U` creates at most `3 |V| |G|` new additive triples. -/
theorem addTriples_union_le {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (U V : Finset G) :
    addTriples (U ∪ V) ≤ addTriples U + 3 * #V * Fintype.card G := by
  classical
  set W : Finset G := U ∪ V with hW
  set T0 : Finset (G × G × G) := {t ∈ U ×ˢ U ×ˢ U | t.1 + t.2.1 = t.2.2} with hT0
  set T1 : Finset (G × G × G) := {t ∈ W ×ˢ W ×ˢ W | t.1 + t.2.1 = t.2.2 ∧ t.1 ∈ V} with hT1
  set T2 : Finset (G × G × G) := {t ∈ W ×ˢ W ×ˢ W | t.1 + t.2.1 = t.2.2 ∧ t.2.1 ∈ V} with hT2
  set T3 : Finset (G × G × G) := {t ∈ W ×ˢ W ×ˢ W | t.1 + t.2.1 = t.2.2 ∧ t.2.2 ∈ V} with hT3
  have hcardUniv : #(V ×ˢ (Finset.univ : Finset G)) = #V * Fintype.card G := by
    rw [Finset.card_product, Finset.card_univ]
  have hsub : {t ∈ W ×ˢ W ×ˢ W | t.1 + t.2.1 = t.2.2} ⊆ T0 ∪ T1 ∪ T2 ∪ T3 := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, heq⟩ := ht
    have hmem : t ∈ W ×ˢ W ×ˢ W :=
      Finset.mem_product.2 ⟨h1, Finset.mem_product.2 ⟨h2, h3⟩⟩
    by_cases hv1 : t.1 ∈ V
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hmem, heq, hv1⟩)))
    by_cases hv2 : t.2.1 ∈ V
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hmem, heq, hv2⟩))
    by_cases hv3 : t.2.2 ∈ V
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hmem, heq, hv3⟩)
    · have u1 : t.1 ∈ U := by rw [hW, Finset.mem_union] at h1; tauto
      have u2 : t.2.1 ∈ U := by rw [hW, Finset.mem_union] at h2; tauto
      have u3 : t.2.2 ∈ U := by rw [hW, Finset.mem_union] at h3; tauto
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨u1, Finset.mem_product.2 ⟨u2, u3⟩⟩, heq⟩)))
  have hb1 : #T1 ≤ #V * Fintype.card G := by
    rw [← hcardUniv]
    refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, hT1, Finset.mem_filter] at ht
      exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨ht.2.2, Finset.mem_univ _⟩)
    · intro s hs t ht hst
      rw [Finset.mem_coe, hT1, Finset.mem_filter] at hs ht
      simp only [Prod.mk.injEq] at hst
      exact triple_ext hs.2.1 ht.2.1 hst.1 hst.2
  have hb2 : #T2 ≤ #V * Fintype.card G := by
    rw [← hcardUniv]
    refine Finset.card_le_card_of_injOn (fun t => (t.2.1, t.1)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, hT2, Finset.mem_filter] at ht
      exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨ht.2.2, Finset.mem_univ _⟩)
    · intro s hs t ht hst
      rw [Finset.mem_coe, hT2, Finset.mem_filter] at hs ht
      simp only [Prod.mk.injEq] at hst
      exact triple_ext hs.2.1 ht.2.1 hst.2 hst.1
  have hb3 : #T3 ≤ #V * Fintype.card G := by
    rw [← hcardUniv]
    refine Finset.card_le_card_of_injOn (fun t => (t.2.2, t.1)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, hT3, Finset.mem_filter] at ht
      exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨ht.2.2, Finset.mem_univ _⟩)
    · intro s hs t ht hst
      rw [Finset.mem_coe, hT3, Finset.mem_filter] at hs ht
      simp only [Prod.mk.injEq] at hst
      have hmid : s.2.1 = t.2.1 := by
        have : s.1 + s.2.1 = s.1 + t.2.1 := by
          rw [hs.2.1, hst.1, ← ht.2.1, hst.2]
        exact add_left_cancel this
      exact triple_ext hs.2.1 ht.2.1 hst.2 hmid
  have hchain : #(T0 ∪ T1 ∪ T2 ∪ T3) ≤ #T0 + #T1 + #T2 + #T3 :=
    le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_right (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
  have hT0eq : #T0 = addTriples U := rfl
  have hmain : addTriples W ≤ #(T0 ∪ T1 ∪ T2 ∪ T3) := Finset.card_le_card hsub
  have hgoal : #T0 + #T1 + #T2 + #T3 ≤ addTriples U + 3 * #V * Fintype.card G := by
    rw [hT0eq, mul_assoc]
    omega
  exact le_trans hmain (le_trans hchain hgoal)

/-! ## Part (i): members of the family have few additive triples -/

/-- **`Prop6_Family` (i)**: every member of `F` has at most `64 ε N²` additive triples. -/
theorem addTriples_family_le (hp1 : 2 * N ≤ p) (hp2 : p ≤ 4 * N) (hε : 0 ≤ ε) :
    ∀ F ∈ family N p M ε, (addTriples F : ℝ) ≤ 64 * ε * (N : ℝ) ^ 2 := by
  classical
  intro F hF
  obtain ⟨d, S, E, -, -, hSt, hE, hEc, rfl⟩ := mem_family_iff.1 hF
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hNp : N < p := by omega
  have hFsub : container N p d M S E ⊆ Finset.Icc 1 N := container_subset_Icc hE
  -- step 1: pass to `ZMod p`
  have h1 : addTriples (container N p d M S E) ≤
      addTriples ((container N p d M S E).image (Nat.cast : ℕ → ZMod p)) :=
    addTriples_le_addTriples_image hNp hFsub
  -- step 2: enlarge to `containerU ∪ π E`
  have h2 : addTriples ((container N p d M S E).image (Nat.cast : ℕ → ZMod p)) ≤
      addTriples (containerU p d M S ∪ E.image (Nat.cast : ℕ → ZMod p)) :=
    addTriples_mono (image_container_subset N p d M S E)
  -- step 3: the union bound
  have h3 : addTriples (containerU p d M S ∪ E.image (Nat.cast : ℕ → ZMod p)) ≤
      addTriples (containerU p d M S) +
        3 * #(E.image (Nat.cast : ℕ → ZMod p)) * Fintype.card (ZMod p) :=
    addTriples_union_le _ _
  have hcardZ : Fintype.card (ZMod p) = p := ZMod.card p
  have himg : #(E.image (Nat.cast : ℕ → ZMod p)) ≤ #E := Finset.card_image_le
  -- combine in ℕ, then in ℝ
  have hnat : addTriples (container N p d M S E) ≤
      addTriples (containerU p d M S) + 3 * #E * p := by
    refine le_trans h1 (le_trans h2 (le_trans h3 ?_))
    rw [hcardZ]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ himg)) _
  have hpR : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hreal : (addTriples (container N p d M S E) : ℝ) ≤
      ε * (p : ℝ) ^ 2 + 3 * (ε * (p : ℝ)) * (p : ℝ) := by
    calc (addTriples (container N p d M S E) : ℝ)
        ≤ ((addTriples (containerU p d M S) + 3 * #E * p : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (addTriples (containerU p d M S) : ℝ) + 3 * (#E : ℝ) * (p : ℝ) := by push_cast; ring
      _ ≤ ε * (p : ℝ) ^ 2 + 3 * (ε * (p : ℝ)) * (p : ℝ) := by
          have : 3 * (#E : ℝ) * (p : ℝ) ≤ 3 * (ε * (p : ℝ)) * (p : ℝ) := by
            have h3E : 3 * (#E : ℝ) ≤ 3 * (ε * (p : ℝ)) := by linarith
            exact mul_le_mul_of_nonneg_right h3E hpR
          linarith
  have hfinal : ε * (p : ℝ) ^ 2 + 3 * (ε * (p : ℝ)) * (p : ℝ) ≤ 64 * ε * (N : ℝ) ^ 2 := by
    have hple : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp2
    have h16 : (p : ℝ) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hε (sub_nonneg.2 h16)]
  linarith

#print axioms CameronErdos.granularization_eq_containerU
#print axioms CameronErdos.mem_containerU
#print axioms CameronErdos.container_subset_Icc
#print axioms CameronErdos.image_container_subset
#print axioms CameronErdos.mem_family_iff
#print axioms CameronErdos.mem_family_of
#print axioms CameronErdos.family_subset_Icc
#print axioms CameronErdos.card_family_le
#print axioms CameronErdos.cast_injOn_Icc
#print axioms CameronErdos.isSumFree_image
#print axioms CameronErdos.addTriples_mono
#print axioms CameronErdos.addTriples_le_addTriples_image
#print axioms CameronErdos.addTriples_union_le
#print axioms CameronErdos.addTriples_family_le

end CameronErdos
