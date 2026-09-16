/-
Copyright (c) 2026 MerLean. All rights reserved.
Released under Apache 2.0 license.
-/
import JSP518.External.Erdos637
import JSP518.JKLY.Turan

/-!
# Diversity extraction for the JKLY distinct-degrees argument

A finset `U` of vertices is `δ`-diverse when the ambient neighbourhoods of any two of its
members differ in at least `δ * |V|` vertices.  The Bukh--Sudakov argument produces such a
set from a *rich* induced subgraph: richness bounds the number of vertices "close" to a fixed
vertex, and Turán's theorem applied to the resulting bounded-degree "closeness graph" extracts
a large pairwise-far set.

The Erdős 637 development only records the `α = 1/2` instance of this (`SqrtDiverse`); here we
record the `α`-generic bound and the Turán extraction, and assemble the Theorem 1 preamble of
Jenssen--Keevash--Long--Yepremyan at `α = 1/4`.
-/

open scoped BigOperators symmDiff
open SimpleGraph

universe u

namespace JKLY

/-- Pairwise ambient diversity of a vertex set. -/
def Diverse {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (δ : ℝ)
    (U : Finset V) : Prop :=
  ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' →
    δ * Fintype.card V ≤ ((Erdos637.neighborhoodDiff G u u').card : ℝ)

/-- The closeness graph: two distinct vertices are adjacent when their ambient neighbourhoods
differ in fewer than `c * |V|` vertices. -/
def closeGraph {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : ℝ) :
    SimpleGraph V where
  Adj u u' := u ≠ u' ∧ ((Erdos637.neighborhoodDiff G u u').card : ℝ) < c * Fintype.card V
  symm := ⟨by
    intro u u' h
    refine ⟨h.1.symm, ?_⟩
    rw [Erdos637.neighborhoodDiff_comm]
    exact h.2⟩
  loopless := ⟨fun u h ↦ h.1 rfl⟩

/-- `α`-generic replacement for `Erdos637.rich_implies_sqrtDiverse`: in a `Rich G δ ρ α` graph
every vertex has at most `|V| ^ α` vertices closer than `(ρ / 4) * |V|`. -/
lemma rich_implies_close_bound {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {δ ρ α : ℝ} (hδ : δ ≤ 1 / 4) (hρ : 0 ≤ ρ) (hRich : Erdos88.Rich G δ ρ α)
    (x : V) :
    ((Erdos637.closeVertices G (ρ / 4) x).card : ℝ) ≤ (Fintype.card V : ℝ) ^ α := by
  classical
  let M := Fintype.card V
  let NX := Erdos88.neighborsIn G x Finset.univ
  let NZ := (Finset.univ : Finset V) \ NX
  have hpartition : NX.card + NZ.card = M := by
    dsimp [NZ, M]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ NX)]
    have hNXcard : NX.card ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ NX)
    simp only [Finset.card_univ] at hNXcard ⊢
    omega
  have hlarge : M ≤ 2 * NX.card ∨ M ≤ 2 * NZ.card := by omega
  rcases hlarge with hlarge | hlarge
  · have hNXtest : δ * (M : ℝ) ≤ (NX.card : ℝ) := by
      have hδ' : δ * (M : ℝ) ≤ (1 / 4 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
      have hMNX : (M : ℝ) ≤ 2 * NX.card := by exact_mod_cast hlarge
      nlinarith
    have hsub : Erdos637.closeVertices G (ρ / 4) x ⊆
        Erdos88.exceptionalVertices G NX ρ := by
      intro y hy
      rw [Erdos637.mem_closeVertices] at hy
      rw [Erdos88.mem_exceptionalVertices]
      right
      have hcardSub : (NX \ Erdos88.neighborsIn G y NX).card ≤
          (Erdos637.neighborhoodDiff G x y).card := by
        apply Finset.card_le_card
        intro z hz
        have hzNX : z ∈ NX := (Finset.mem_sdiff.mp hz).1
        have hznotNY : z ∉ Erdos88.neighborsIn G y NX := (Finset.mem_sdiff.mp hz).2
        have hzx : z ∈ Erdos88.neighborsIn G x Finset.univ := by simpa [NX] using hzNX
        have hznoty : z ∉ Erdos88.neighborsIn G y Finset.univ := by
          intro hzy
          apply hznotNY
          rw [Erdos88.mem_neighborsIn] at hzy ⊢
          exact ⟨hzNX, hzy.2⟩
        rw [Erdos637.neighborhoodDiff, Finset.mem_symmDiff]
        exact Or.inl ⟨hzx, hznoty⟩
      have hcardReal : ((NX \ Erdos88.neighborsIn G y NX).card : ℝ) ≤
          (Erdos637.neighborhoodDiff G x y).card := by exact_mod_cast hcardSub
      have hMNX : (M : ℝ) ≤ 2 * NX.card := by exact_mod_cast hlarge
      have hclose : ((Erdos637.neighborhoodDiff G x y).card : ℝ) < (ρ / 4) * M := by
        simpa [M] using hy
      nlinarith
    have hcard := Finset.card_le_card hsub
    have hrich := hRich NX (by simpa [M] using hNXtest)
    have hreal : ((Erdos637.closeVertices G (ρ / 4) x).card : ℝ) ≤
        ((Erdos88.exceptionalVertices G NX ρ).card : ℝ) := by exact_mod_cast hcard
    exact hreal.trans (by simpa [M] using hrich)
  · have hNZtest : δ * (M : ℝ) ≤ (NZ.card : ℝ) := by
      have hδ' : δ * (M : ℝ) ≤ (1 / 4 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
      have hMNZ : (M : ℝ) ≤ 2 * NZ.card := by exact_mod_cast hlarge
      nlinarith
    have hsub : Erdos637.closeVertices G (ρ / 4) x ⊆
        Erdos88.exceptionalVertices G NZ ρ := by
      intro y hy
      rw [Erdos637.mem_closeVertices] at hy
      rw [Erdos88.mem_exceptionalVertices]
      left
      have hcardSub : (Erdos88.neighborsIn G y NZ).card ≤
          (Erdos637.neighborhoodDiff G x y).card := by
        apply Finset.card_le_card
        intro z hz
        have hzNZ : z ∈ NZ := (Erdos88.mem_neighborsIn.mp hz).1
        have hzyAdj : G.Adj y z := (Erdos88.mem_neighborsIn.mp hz).2
        have hznotNX : z ∉ NX := (Finset.mem_sdiff.mp hzNZ).2
        have hzy : z ∈ Erdos88.neighborsIn G y Finset.univ := by
          rw [Erdos88.mem_neighborsIn]
          exact ⟨Finset.mem_univ _, hzyAdj⟩
        have hznotx : z ∉ Erdos88.neighborsIn G x Finset.univ := by simpa [NX] using hznotNX
        rw [Erdos637.neighborhoodDiff, Finset.mem_symmDiff]
        exact Or.inr ⟨hzy, hznotx⟩
      have hcardReal : ((Erdos88.neighborsIn G y NZ).card : ℝ) ≤
          (Erdos637.neighborhoodDiff G x y).card := by exact_mod_cast hcardSub
      have hMNZ : (M : ℝ) ≤ 2 * NZ.card := by exact_mod_cast hlarge
      have hclose : ((Erdos637.neighborhoodDiff G x y).card : ℝ) < (ρ / 4) * M := by
        simpa [M] using hy
      nlinarith
    have hcard := Finset.card_le_card hsub
    have hrich := hRich NZ (by simpa [M] using hNZtest)
    have hreal : ((Erdos637.closeVertices G (ρ / 4) x).card : ℝ) ≤
        ((Erdos88.exceptionalVertices G NZ ρ).card : ℝ) := by exact_mod_cast hcard
    exact hreal.trans (by simpa [M] using hrich)

/-- From a per-vertex bound on the number of close vertices, Turán extracts a diverse set. -/
lemma exists_diverse_of_close_bound {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {c D : ℝ} (hD0 : 0 ≤ D)
    (hclose : ∀ x : V, ((Erdos637.closeVertices G c x).card : ℝ) ≤ D) :
    ∃ U : Finset V, Diverse G c U ∧ (Fintype.card V : ℝ) / (1 + 2 * D) ≤ U.card := by
  classical
  have : DecidableRel (closeGraph G c).Adj := Classical.decRel _
  have hdeg : ∀ v : V, ((closeGraph G c).degree v : ℝ) ≤ D := by
    intro v
    refine le_trans ?_ (hclose v)
    have hsub : (closeGraph G c).neighborFinset v ⊆ Erdos637.closeVertices G c v := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact Erdos637.mem_closeVertices.mpr hy.2
    have := Finset.card_le_card hsub
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast this
  obtain ⟨I, hIind, hIcard⟩ := exists_indepSet_card_ge_of_maxDegree (closeGraph G c) hdeg hD0
  refine ⟨I, ?_, hIcard⟩
  intro u hu u' hu' hne
  have hnot : ¬ (closeGraph G c).Adj u u' :=
    hIind (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hu') hne
  exact not_lt.mp fun hlt ↦ hnot ⟨hne, hlt⟩

/-- **Theorem 1 preamble** (JKLY §2.3 via Kwan--Sah--Sauermann--Sawhney Lemma 4.4 at `α = 1/4`).
Every `C`-Ramsey graph on `n ≥ N₀` vertices has an induced subgraph on `U₀` with
`|U₀| ≥ lam * n`, containing a `(ρ/4)`-diverse set of size at least
`|U₀| / (1 + 2 |U₀| ^ (1/4))`. -/
theorem exists_diverse_subgraph_of_ramseyFree (C : ℝ) (hC : 0 < C) :
    ∃ ρ lam : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < lam ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ G : SimpleGraph (Fin n),
        Erdos88.RamseyFree C G →
        ∃ U₀ : Finset (Fin n), lam * n ≤ U₀.card ∧
          ∃ U : Finset ↥U₀, Diverse (G.induce (↑U₀ : Set (Fin n))) (ρ / 4) U ∧
            (U₀.card : ℝ) / (1 + 2 * (U₀.card : ℝ) ^ ((1 : ℝ) / 4)) ≤ U.card := by
  classical
  obtain ⟨ρ, hρ, hρone, Nrich, hrichness⟩ := Erdos88.ksssLemma44 C (1 / 4) hC (by norm_num)
  obtain ⟨lam, hlam, hlamρ, hlampow⟩ := Erdos637.exists_richness_scale ρ hρ
  obtain ⟨Nsqrt, hNsqrt⟩ := exists_nat_ge ((lam ^ 2)⁻¹)
  refine ⟨ρ, lam, hρ, hρone, hlam, max Nrich (max 1 Nsqrt), ?_⟩
  intro n hn G hG
  have hnrich : Nrich ≤ n := le_trans (le_max_left _ _) hn
  have hnone : 1 ≤ n :=
    le_trans (le_max_left 1 Nsqrt) (le_trans (le_max_right Nrich _) hn)
  have hnsqrt : Nsqrt ≤ n :=
    le_trans (le_max_right 1 Nsqrt) (le_trans (le_max_right Nrich _) hn)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hnone
  have hNsqrtR : (lam ^ 2)⁻¹ ≤ (n : ℝ) := hNsqrt.trans (by exact_mod_cast hnsqrt)
  have hunit : (1 : ℝ) ≤ lam ^ 2 * n := by
    have hmul := mul_le_mul_of_nonneg_left hNsqrtR (sq_nonneg lam)
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hlam.ne')] at hmul
    simpa [mul_comm] using hmul
  set m : ℝ := lam * n with hm
  have hsqrtm : Real.sqrt n ≤ m := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by rw [hm]; positivity, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hunit hnR
    rw [hm]
    nlinarith
  have hmupper : m ≤ ρ * n := by
    rw [hm]
    exact mul_le_mul_of_nonneg_right hlamρ hnR
  obtain ⟨U, hUcard, hRich⟩ := hrichness n hnrich m hsqrtm hmupper G hG
  refine ⟨U, hUcard, ?_⟩
  have hratio : m / (n : ℝ) = lam := by
    rw [hm]
    field_simp
  have hdelta : (m / (n : ℝ)) ^ ρ ≤ (1 / 4 : ℝ) := by
    rw [hratio]
    exact hlampow
  have hclose : ∀ x : ↥U, ((Erdos637.closeVertices (G.induce (↑U : Set (Fin n)))
      (ρ / 4) x).card : ℝ) ≤ (U.card : ℝ) ^ ((1 : ℝ) / 4) := by
    intro x
    have hx := rich_implies_close_bound (G.induce (↑U : Set (Fin n))) hdelta hρ.le hRich x
    rwa [Erdos88.card_subtype_coe_finset] at hx
  obtain ⟨W, hWdiv, hWcard⟩ :=
    exists_diverse_of_close_bound (G.induce (↑U : Set (Fin n))) (c := ρ / 4)
      (D := (U.card : ℝ) ^ ((1 : ℝ) / 4)) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hclose
  exact ⟨W, hWdiv, by rwa [Erdos88.card_subtype_coe_finset] at hWcard⟩

end JKLY
