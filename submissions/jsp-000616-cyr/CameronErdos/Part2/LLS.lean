import CameronErdos.Counting.Basic

/-!
# Lev–Łuczak–Schoen: popular differences (Proposition 1)

This file formalises Proposition 1 of Lev–Łuczak–Schoen, *Sum-free sets in abelian groups*,
Israel J. Math. **125** (2001) 347–367, §4 (Israel J. Math. 125 (2001), pp. 5–6), together with the
set-theoretic form of the graph-theoretic Lemma 6 that it relies on.  It is Green's Lemma 10
in the Cameron–Erdős campaign (plan node `Lem10_LevLuczakSchoen`).

The statement is: for a finite subset `A` of an abelian group `G` and an integer `K ≥ 1`,
writing `D = D_K(A)` for the set of `K`-popular differences (`CameronErdos.popularDiff`),
if `|D| ≤ 2|A| - 5√(K|A - A|)` then there is `X ⊆ A` with `|A \ X| ≤ √(K|A - A|)` and
`X - X ⊆ D`.

Rather than going through graphs we work directly with the *`D`-neighbourhoods*
`popNbhd A K a = {b ∈ A | a - b ∈ D}`; `lls_lemma6` is the set-theoretic content of LLS
Lemma 6 (the vertices of large degree span a large, high-minimum-degree subgraph).

## Main results

* `CameronErdos.popNbhd` — the `D`-neighbourhood of a point of `A`;
* `CameronErdos.sum_card_popNbhd_ge` — the degree sum bound (LLS: "the average degree of `Γ`
  is at least `|A|(1 - K|A - A|/|A|²)`");
* `CameronErdos.lls_lemma6` — LLS Lemma 6 in set form;
* `CameronErdos.lls_prop1` — LLS Proposition 1 for an integer threshold `K : ℕ`;
* `CameronErdos.popularDiff_ceil` — `D_K(A) = D_{⌈K⌉}(A)` for real thresholds `K > 0`;
* `CameronErdos.lls_prop1_real` — the real-threshold wrapper used downstream (Green's
  Lemma 10 applies it with `K = 8√ε·N`).
-/

open Finset
open scoped Pointwise

namespace CameronErdos

section LLS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## The `D`-neighbourhoods -/

/-- `popNbhd A K a = {b ∈ A | a - b ∈ D_K(A)}` is the neighbourhood of `a` in the graph on
vertex set `A` in which `a₁ ~ a₂` iff `a₁ - a₂` is a `K`-popular difference of `A`. -/
noncomputable def popNbhd (A : Finset G) (K : ℝ) (a : G) : Finset G :=
  {b ∈ A | a - b ∈ popularDiff A K}

lemma popNbhd_subset (A : Finset G) (K : ℝ) (a : G) : popNbhd A K a ⊆ A :=
  Finset.filter_subset _ _

lemma mem_popNbhd {A : Finset G} {K : ℝ} {a b : G} :
    b ∈ popNbhd A K a ↔ b ∈ A ∧ a - b ∈ popularDiff A K :=
  Finset.mem_filter

lemma card_popNbhd_le (A : Finset G) (K : ℝ) (a : G) : #(popNbhd A K a) ≤ #A :=
  Finset.card_le_card (popNbhd_subset A K a)

/-! ## Step 1: the degree sum -/

/-- The number of ordered pairs `(a, b) ∈ A × A` whose difference is *not* `K`-popular is at
most `(K - 1)|A - A|`: each such difference lies in `A - A` and has fewer than `K`
representations. -/
lemma card_unpopular_pairs_le (A : Finset G) (K : ℕ) (hK : 1 ≤ K) :
    (#{q ∈ A ×ˢ A | q.1 - q.2 ∉ popularDiff A (K : ℝ)} : ℝ)
      ≤ ((K : ℝ) - 1) * (#(A - A) : ℝ) := by
  classical
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  set bad : Finset (G × G) := {q ∈ A ×ˢ A | q.1 - q.2 ∉ popularDiff A (K : ℝ)} with hbad
  have hrange : ∀ q ∈ bad, q.1 - q.2 ∈ A - A := by
    intro q hq
    rw [hbad, Finset.mem_filter, Finset.mem_product] at hq
    exact Finset.mem_sub.2 ⟨q.1, hq.1.1, q.2, hq.1.2, rfl⟩
  have hfib : #bad = ∑ c ∈ A - A, #{q ∈ bad | q.1 - q.2 = c} :=
    Finset.card_eq_sum_card_fiberwise hrange
  have hfibsmall : ∀ c ∈ A - A, (#{q ∈ bad | q.1 - q.2 = c} : ℝ) ≤ (K : ℝ) - 1 := by
    intro c _
    by_cases hcD : c ∈ popularDiff A (K : ℝ)
    · have hempty : {q ∈ bad | q.1 - q.2 = c} = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        rw [hbad, Finset.mem_filter, hq2] at hq1
        exact hq1.2 hcD
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      linarith
    · have hlt : (diffReps A c : ℝ) < (K : ℝ) := by
        by_contra hcon
        exact hcD ((mem_popularDiff_iff hKpos c).2 (not_lt.1 hcon))
      have hltN : diffReps A c < K := by exact_mod_cast hlt
      have hsub : {q ∈ bad | q.1 - q.2 = c} ⊆ {q ∈ A ×ˢ A | q.1 - q.2 = c} := by
        intro q hq
        rw [Finset.mem_filter, hbad, Finset.mem_filter] at hq
        exact Finset.mem_filter.2 ⟨hq.1.1, hq.2⟩
      have h1 : #{q ∈ bad | q.1 - q.2 = c} ≤ diffReps A c := Finset.card_le_card hsub
      have h2 : #{q ∈ bad | q.1 - q.2 = c} + 1 ≤ K := by omega
      have h3 : ((#{q ∈ bad | q.1 - q.2 = c} + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
  calc (#bad : ℝ) = ∑ c ∈ A - A, (#{q ∈ bad | q.1 - q.2 = c} : ℝ) := by
        rw [hfib]; push_cast; ring
    _ ≤ ∑ _c ∈ A - A, ((K : ℝ) - 1) := Finset.sum_le_sum hfibsmall
    _ = (#(A - A) : ℝ) * ((K : ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((K : ℝ) - 1) * (#(A - A) : ℝ) := by ring

/-- The degree sum bound: `∑_{a ∈ A} |N(a)| ≥ |A|² - (K - 1)|A - A|`.  (LLS: the average
degree of `Γ` is at least `|A| - (K-1)|A - A|/|A|`.) -/
lemma sum_card_popNbhd_ge (A : Finset G) (K : ℕ) (hK : 1 ≤ K) :
    (#A : ℝ) * (#A : ℝ) - ((K : ℝ) - 1) * (#(A - A) : ℝ)
      ≤ ∑ a ∈ A, (#(popNbhd A (K : ℝ) a) : ℝ) := by
  classical
  set bad : Finset (G × G) := {q ∈ A ×ˢ A | q.1 - q.2 ∉ popularDiff A (K : ℝ)} with hbad
  have hdegsum : #bad = ∑ a ∈ A, #{b ∈ A | a - b ∉ popularDiff A (K : ℝ)} := by
    rw [hbad, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm
  have hpera : ∀ a : G,
      #(popNbhd A (K : ℝ) a) + #{b ∈ A | a - b ∉ popularDiff A (K : ℝ)} = #A := fun a =>
    Finset.card_filter_add_card_filter_not _
  have hnat : (∑ a ∈ A, #(popNbhd A (K : ℝ) a)) + #bad = #A * #A := by
    rw [hdegsum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun a _ => hpera a),
      Finset.sum_const, smul_eq_mul]
  have hR : (∑ a ∈ A, (#(popNbhd A (K : ℝ) a) : ℝ)) + (#bad : ℝ) = (#A : ℝ) * (#A : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this
    exact this
  have hbadle := card_unpopular_pairs_le A K hK
  rw [← hbad] at hbadle
  linarith

/-! ## Step 2: LLS Lemma 6, in set form -/

/-- **LLS Lemma 6** (set form).  If the degree sum of the `D`-neighbourhoods is at least
`|A|² - s²`, then the set `X` of vertices of degree `> |A| - s` has `|X| ≥ |A| - s`. -/
lemma lls_lemma6 (A : Finset G) (K : ℝ) {s : ℝ} (hs : 0 < s)
    (hsum : (#A : ℝ) * (#A : ℝ) - s * s ≤ ∑ a ∈ A, (#(popNbhd A K a) : ℝ)) :
    (#A : ℝ) - s ≤ (#{a ∈ A | (#A : ℝ) - s < (#(popNbhd A K a) : ℝ)} : ℝ) := by
  classical
  set X : Finset G := {a ∈ A | (#A : ℝ) - s < (#(popNbhd A K a) : ℝ)} with hX
  set Y : Finset G := {a ∈ A | ¬ ((#A : ℝ) - s < (#(popNbhd A K a) : ℝ))} with hY
  have hcards : #X + #Y = #A := Finset.card_filter_add_card_filter_not _
  have hsplit : (∑ a ∈ X, (#(popNbhd A K a) : ℝ)) + (∑ a ∈ Y, (#(popNbhd A K a) : ℝ))
      = ∑ a ∈ A, (#(popNbhd A K a) : ℝ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hXbound : (∑ a ∈ X, (#(popNbhd A K a) : ℝ)) ≤ (#X : ℝ) * (#A : ℝ) := by
    calc (∑ a ∈ X, (#(popNbhd A K a) : ℝ)) ≤ ∑ _a ∈ X, (#A : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact_mod_cast card_popNbhd_le A K a
      _ = (#X : ℝ) * (#A : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hYR : (#Y : ℝ) = (#A : ℝ) - (#X : ℝ) := by
    have h : ((#X + #Y : ℕ) : ℝ) = (#A : ℝ) := by exact_mod_cast hcards
    push_cast at h
    linarith
  have hYbound : (∑ a ∈ Y, (#(popNbhd A K a) : ℝ)) ≤ ((#A : ℝ) - (#X : ℝ)) * ((#A : ℝ) - s) := by
    calc (∑ a ∈ Y, (#(popNbhd A K a) : ℝ)) ≤ ∑ _a ∈ Y, ((#A : ℝ) - s) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [hY, Finset.mem_filter] at ha
          exact not_lt.1 ha.2
      _ = (#Y : ℝ) * ((#A : ℝ) - s) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((#A : ℝ) - (#X : ℝ)) * ((#A : ℝ) - s) := by rw [hYR]
  have hchain : (#A : ℝ) * (#A : ℝ) - s * s
      ≤ (#X : ℝ) * (#A : ℝ) + ((#A : ℝ) - (#X : ℝ)) * ((#A : ℝ) - s) := by
    linarith
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [hchain, hs, hcon]

/-! ## Step 3: Proposition 1 -/

/-- **Lev–Łuczak–Schoen, Proposition 1** (= Green's Lemma 10).  Let `A` be a finite subset of
an abelian group and let `K ≥ 1` be an integer.  If the set `D_K(A)` of `K`-popular
differences satisfies `|D_K(A)| ≤ 2|A| - 5√(K|A - A|)`, then there is `X ⊆ A` with
`|A \ X| ≤ √(K|A - A|)` and `X - X ⊆ D_K(A)`. -/
theorem lls_prop1 (A : Finset G) (K : ℕ) (hK : 1 ≤ K)
    (hD : (#(popularDiff A K) : ℝ) ≤ 2 * #A - 5 * Real.sqrt (K * #(A - A))) :
    ∃ X ⊆ A, (#(A \ X) : ℝ) ≤ Real.sqrt (K * #(A - A)) ∧ X - X ⊆ popularDiff A K := by
  classical
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsnn : (0 : ℝ) ≤ Real.sqrt ((K : ℝ) * (#(A - A) : ℝ)) := Real.sqrt_nonneg _
  -- Trivial case: `|A| ≤ √(K|A - A|)`, where `X = ∅` works.
  by_cases htriv : (#A : ℝ) ≤ Real.sqrt ((K : ℝ) * (#(A - A) : ℝ))
  · exact ⟨∅, Finset.empty_subset _, by simpa using htriv, by simp⟩
  rw [not_le] at htriv
  set s : ℝ := Real.sqrt ((K : ℝ) * (#(A - A) : ℝ)) with hsdef
  have hs2 : s * s = (K : ℝ) * (#(A - A) : ℝ) := Real.mul_self_sqrt (by positivity)
  -- `A` is nonempty, so `|A| ≤ |A - A|`, and `K ≤ s`.
  have hAcard : 0 < #A := by
    have h : (0 : ℝ) < (#A : ℝ) := lt_of_le_of_lt hsnn htriv
    exact_mod_cast h
  have hApos : (0 : ℝ) < (#A : ℝ) := by exact_mod_cast hAcard
  have hmR : (#A : ℝ) ≤ (#(A - A) : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sub_self : #A ≤ #(A - A))
  have hKle : (K : ℝ) ≤ (#(A - A) : ℝ) := by nlinarith
  have hKs : (K : ℝ) ≤ s := by nlinarith
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le hKpos hKs
  -- Steps 1 and 2.
  have hsum : (#A : ℝ) * (#A : ℝ) - s * s ≤ ∑ a ∈ A, (#(popNbhd A (K : ℝ) a) : ℝ) := by
    have h := sum_card_popNbhd_ge A K hK
    have hnn : (0 : ℝ) ≤ (#(A - A) : ℝ) := by positivity
    nlinarith
  have hX := lls_lemma6 A (K : ℝ) hspos hsum
  set X : Finset G := {a ∈ A | (#A : ℝ) - s < (#(popNbhd A (K : ℝ) a) : ℝ)} with hXdef
  have hXA : X ⊆ A := Finset.filter_subset _ _
  have hXleA : #X ≤ #A := Finset.card_le_card hXA
  have hAXR : (#(A \ X) : ℝ) = (#A : ℝ) - (#X : ℝ) := by
    have h : ((#(A \ X) + #X : ℕ) : ℝ) = (#A : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hXA
    push_cast at h
    linarith
  have hAXcard : (#(A \ X) : ℝ) ≤ s := by rw [hAXR]; linarith
  -- Inside `X` every neighbourhood is still large.
  have hnbX : ∀ a ∈ X, (#A : ℝ) - 2 * s < (#(popNbhd A (K : ℝ) a ∩ X) : ℝ) := by
    intro a ha
    have hdeg : (#A : ℝ) - s < (#(popNbhd A (K : ℝ) a) : ℝ) := by
      rw [hXdef, Finset.mem_filter] at ha; exact ha.2
    have hsplit : #(popNbhd A (K : ℝ) a \ X) + #(popNbhd A (K : ℝ) a ∩ X)
        = #(popNbhd A (K : ℝ) a) := Finset.card_sdiff_add_card_inter _ _
    have hsub : popNbhd A (K : ℝ) a \ X ⊆ A \ X :=
      Finset.sdiff_subset_sdiff (popNbhd_subset A (K : ℝ) a) (le_refl X)
    have hle : (#(popNbhd A (K : ℝ) a \ X) : ℝ) ≤ (#(A \ X) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hsplitR : (#(popNbhd A (K : ℝ) a \ X) : ℝ) + (#(popNbhd A (K : ℝ) a ∩ X) : ℝ)
        = (#(popNbhd A (K : ℝ) a) : ℝ) := by exact_mod_cast hsplit
    linarith
  refine ⟨X, hXA, hAXcard, ?_⟩
  -- Step 3: the contradiction argument.
  by_contra hcon
  rw [Finset.not_subset] at hcon
  obtain ⟨d, hdX, hdD⟩ := hcon
  obtain ⟨a₂, ha₂, a₁, ha₁, hd⟩ := Finset.mem_sub.1 hdX
  have hdlt : (diffReps A d : ℝ) < (K : ℝ) := by
    by_contra hc
    exact hdD ((mem_popularDiff_iff hKpos d).2 (not_lt.1 hc))
  have hdltN : diffReps A d < K := by exact_mod_cast hdlt
  set N₁ : Finset G := popNbhd A (K : ℝ) a₁ ∩ X with hN₁
  set N₂ : Finset G := popNbhd A (K : ℝ) a₂ ∩ X with hN₂
  set S₁ : Finset G := N₁.image (fun b => a₁ - b) with hS₁
  set S₂ : Finset G := N₂.image (fun b => a₂ - b) with hS₂
  have hinj : ∀ c : G, Function.Injective (fun b : G => c - b) := fun _ => sub_right_injective
  have hS₁card : #S₁ = #N₁ := Finset.card_image_of_injective _ (hinj a₁)
  have hS₂card : #S₂ = #N₂ := Finset.card_image_of_injective _ (hinj a₂)
  have hS₁D : S₁ ⊆ popularDiff A (K : ℝ) := by
    intro c hc
    rw [hS₁, Finset.mem_image] at hc
    obtain ⟨b, hb, hbc⟩ := hc
    rw [hN₁, Finset.mem_inter] at hb
    have := (mem_popNbhd.1 hb.1).2
    rwa [hbc] at this
  have hS₂D : S₂ ⊆ popularDiff A (K : ℝ) := by
    intro c hc
    rw [hS₂, Finset.mem_image] at hc
    obtain ⟨b, hb, hbc⟩ := hc
    rw [hN₂, Finset.mem_inter] at hb
    have := (mem_popNbhd.1 hb.1).2
    rwa [hbc] at this
  have hcardU : #(S₁ ∪ S₂) ≤ #(popularDiff A (K : ℝ)) :=
    Finset.card_le_card (Finset.union_subset hS₁D hS₂D)
  -- The two translated neighbourhoods overlap in at most `K - 1` elements.
  have hinter : #(S₁ ∩ S₂) ≤ diffReps A d := by
    show #(S₁ ∩ S₂) ≤ #{q ∈ A ×ˢ A | q.1 - q.2 = d}
    refine Finset.card_le_card_of_injOn (fun c => (a₂ - c, a₁ - c)) ?_ ?_
    · intro c hc
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hc
      obtain ⟨hc1, hc2⟩ := hc
      rw [hS₁, Finset.mem_image] at hc1
      rw [hS₂, Finset.mem_image] at hc2
      obtain ⟨b₁, hb₁, hb₁e⟩ := hc1
      obtain ⟨b₂, hb₂, hb₂e⟩ := hc2
      have hb₁A : b₁ ∈ A := by
        rw [hN₁, Finset.mem_inter] at hb₁
        exact (mem_popNbhd.1 hb₁.1).1
      have hb₂A : b₂ ∈ A := by
        rw [hN₂, Finset.mem_inter] at hb₂
        exact (mem_popNbhd.1 hb₂.1).1
      have h₁ : a₁ - c = b₁ := by rw [← hb₁e]; abel
      have h₂ : a₂ - c = b₂ := by rw [← hb₂e]; abel
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨by rw [h₂]; exact hb₂A, by rw [h₁]; exact hb₁A⟩, ?_⟩
      show a₂ - c - (a₁ - c) = d
      rw [← hd]
      abel
    · intro c₁ _ c₂ _ h
      simp only [Prod.mk.injEq] at h
      exact sub_right_injective h.1
  -- Putting the counts together contradicts the hypothesis on `|D_K(A)|`.
  have hUI : (#(S₁ ∪ S₂) : ℝ) + (#(S₁ ∩ S₂) : ℝ) = (#S₁ : ℝ) + (#S₂ : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter S₁ S₂
  have hN₁big : (#A : ℝ) - 2 * s < (#N₁ : ℝ) := hnbX a₁ ha₁
  have hN₂big : (#A : ℝ) - 2 * s < (#N₂ : ℝ) := hnbX a₂ ha₂
  have hS₁R : (#S₁ : ℝ) = (#N₁ : ℝ) := by exact_mod_cast hS₁card
  have hS₂R : (#S₂ : ℝ) = (#N₂ : ℝ) := by exact_mod_cast hS₂card
  have hinterR : (#(S₁ ∩ S₂) : ℝ) + 1 ≤ (K : ℝ) := by
    have h : #(S₁ ∩ S₂) + 1 ≤ K := by omega
    have h' : ((#(S₁ ∩ S₂) + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hcardUR : (#(S₁ ∪ S₂) : ℝ) ≤ (#(popularDiff A (K : ℝ)) : ℝ) := by exact_mod_cast hcardU
  linarith

/-! ## The real-threshold wrapper -/

/-- Since `diffReps` is `ℕ`-valued, the popular-difference set only depends on `⌈K⌉₊`. -/
lemma popularDiff_ceil (A : Finset G) {K : ℝ} (hK : 0 < K) :
    popularDiff A K = popularDiff A (⌈K⌉₊ : ℝ) := by
  have hcposN : 0 < ⌈K⌉₊ := Nat.ceil_pos.2 hK
  have hcpos : (0 : ℝ) < ((⌈K⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcposN
  ext d
  rw [mem_popularDiff_iff hK d, mem_popularDiff_iff hcpos d]
  constructor
  · intro h
    exact_mod_cast Nat.ceil_le.2 h
  · intro h
    exact le_trans (Nat.le_ceil K) h

/-- **Proposition 1 for a real threshold.**  The form used downstream: Green's Lemma 10
applies it with `K = 8√ε·N`.  Replacing `K` by `⌈K⌉₊ ≤ K + 1 ≤ 2K` costs only the factor `2`
under the square root. -/
theorem lls_prop1_real (A : Finset G) {K : ℝ} (hK : 1 ≤ K)
    (hD : (#(popularDiff A K) : ℝ) ≤ 2 * #A - 5 * Real.sqrt (2 * K * #(A - A))) :
    ∃ X ⊆ A, (#(A \ X) : ℝ) ≤ Real.sqrt (2 * K * #(A - A)) ∧ X - X ⊆ popularDiff A K := by
  have hKpos : (0 : ℝ) < K := by linarith
  have hceq := popularDiff_ceil A hKpos
  have hc1 : 1 ≤ ⌈K⌉₊ := Nat.one_le_ceil_iff.2 hKpos
  have hcle : ((⌈K⌉₊ : ℕ) : ℝ) ≤ 2 * K := by
    have h : ((⌈K⌉₊ : ℕ) : ℝ) < K + 1 := Nat.ceil_lt_add_one hKpos.le
    linarith
  have hnn : (0 : ℝ) ≤ (#(A - A) : ℝ) := by positivity
  have hsqle : Real.sqrt (((⌈K⌉₊ : ℕ) : ℝ) * (#(A - A) : ℝ))
      ≤ Real.sqrt (2 * K * (#(A - A) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hD' : (#(popularDiff A ((⌈K⌉₊ : ℕ) : ℝ)) : ℝ)
      ≤ 2 * (#A : ℝ) - 5 * Real.sqrt (((⌈K⌉₊ : ℕ) : ℝ) * (#(A - A) : ℝ)) := by
    rw [← hceq]; linarith
  obtain ⟨X, hXA, hXcard, hXD⟩ := lls_prop1 A ⌈K⌉₊ hc1 hD'
  refine ⟨X, hXA, le_trans hXcard hsqle, ?_⟩
  rwa [← hceq] at hXD

end LLS

/-! ## Axiom audit -/

#print axioms popNbhd_subset
#print axioms mem_popNbhd
#print axioms card_popNbhd_le
#print axioms card_unpopular_pairs_le
#print axioms sum_card_popNbhd_ge
#print axioms lls_lemma6
#print axioms lls_prop1
#print axioms popularDiff_ceil
#print axioms lls_prop1_real

end CameronErdos
