/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import JSP518.JKLY.Counting
import JSP518.JKLY.Turan

/-!
# The random probability vector (Jenssen--Keevash--Lichev--Yepremyan, Lemma 7)

Given a `δ`-diverse set `U` of vertices and a disjoint set `W₀` of `N` vertices, we build a
probability vector `p ∈ [0.1, 0.9]^{W₀}` and a large subset `U' ⊆ U` on which the expected
degrees `expDeg' G U W₀ p` are pairwise `1`-separated.

The vector `p` is itself random: uniform integers `m_u ∈ [-K, K]` are chosen independently
for `u` in a shrunken set `U₁` of size `K`, and `p_v := 1/2 + N⁻¹ ∑_u m_u σ_u(v)`, truncated
to `[0.1, 0.9]`; here `σ_u(v) = ±1` records adjacency.  The randomness is the uniform counting
measure on the finite product `V → Fin (2K+1)`, so every probability estimate below is a plain
`Finset` cardinality bound.
-/

open scoped BigOperators symmDiff

namespace JKLY

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Expected degrees -/

/-- The expected degree of `u` in `G[U ∪ W]`, where `W` keeps each `v ∈ W₀` with
probability `p v`. -/
noncomputable def expDeg' (G : SimpleGraph V) (U W₀ : Finset V) (p : V → ℝ) (u : V) : ℝ :=
  ((Erdos88.neighborsIn G u U).card : ℝ) + ∑ v ∈ W₀, (if G.Adj u v then p v else 0)

/-- The `±1` sign recording whether `u` and `v` are adjacent. -/
noncomputable def adjSign (G : SimpleGraph V) (u v : V) : ℝ := if G.Adj u v then 1 else -1

omit [Fintype V] [DecidableEq V] in
/-- The adjacency sign has absolute value one. -/
lemma abs_adjSign (G : SimpleGraph V) (u v : V) : |adjSign G u v| = 1 := by
  by_cases h : G.Adj u v <;> simp [adjSign, h]

/-- The difference of adjacency indicators of `u` and `u'` is the indicator of the
symmetric difference of their neighbourhoods, signed by `adjSign G u`. -/
lemma sub_ite_eq_ite_mul_adjSign (G : SimpleGraph V) (u u' v : V) :
    (if G.Adj u v then (1 : ℝ) else 0) - (if G.Adj u' v then (1 : ℝ) else 0) =
      (if v ∈ Erdos637.neighborhoodDiff G u u' then (1 : ℝ) else 0) * adjSign G u v := by
  have hmem : v ∈ Erdos637.neighborhoodDiff G u u' ↔
      (G.Adj u v ∧ ¬ G.Adj u' v) ∨ (G.Adj u' v ∧ ¬ G.Adj u v) := by
    simp [Erdos637.neighborhoodDiff, Finset.mem_symmDiff]
  by_cases h1 : G.Adj u v <;> by_cases h2 : G.Adj u' v <;>
    simp [adjSign, h1, h2, hmem]

/-! ## Truncation to `[0.1, 0.9]` -/

/-- Truncation of a real number to the interval `[0.1, 0.9]`. -/
def clamp09 (x : ℝ) : ℝ := max 0.1 (min 0.9 x)

/-- Truncation is monotone. -/
lemma clamp09_mono : Monotone clamp09 := fun _ _ h ↦ max_le_max le_rfl (min_le_min le_rfl h)

/-- Truncation takes values in `[0.1, 0.9]`. -/
lemma clamp09_mem (x : ℝ) : 0.1 ≤ clamp09 x ∧ clamp09 x ≤ 0.9 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Truncation fixes the points of `[0.1, 0.9]`. -/
lemma clamp09_eq_self {x : ℝ} (h1 : 0.1 ≤ x) (h2 : x ≤ 0.9) : clamp09 x = x := by
  rw [clamp09, min_eq_right h2, max_eq_right h1]

/-! ## The one-coordinate family of probability vectors -/

/-- The truncated probability vector obtained from the contribution `q` of the other
coordinates by setting the `u`-coordinate of the random vector to `i`. -/
noncomputable def pAt (G : SimpleGraph V) (W₀ : Finset V) (q : V → ℝ) (u : V) (N : ℝ)
    (i : ℤ) (v : V) : ℝ :=
  if v ∈ W₀ then clamp09 (q v + (i : ℝ) * adjSign G u v / N) else 0

/-- The difference of the expected degrees of `u` and `u'`, as a function of the
`u`-coordinate `i` of the random vector. -/
noncomputable def diffAt (G : SimpleGraph V) (U W₀ : Finset V) (q : V → ℝ) (u u' : V)
    (N : ℝ) (i : ℤ) : ℝ :=
  expDeg' G U W₀ (pAt G W₀ q u N i) u - expDeg' G U W₀ (pAt G W₀ q u N i) u'

/-- **The step bound.**  Increasing the `u`-coordinate by one increases the expected degree
difference by at least `δ / 2`, provided that at most `δ N / 2` coordinates of `q` are
outside `[0.2, 0.8]`, that `|N(u) ∆ N(u') ∩ W₀| ≥ δ N`, and that the coordinate stays in a
range where no truncation happens at the good coordinates. -/
lemma add_le_diffAt_succ (G : SimpleGraph V) (U W₀ : Finset V) (q : V → ℝ) {u u' : V}
    {N δ : ℝ} (hN : 0 < N) {V₀ : Finset V}
    (hq : ∀ v ∈ W₀, v ∉ V₀ → 0.2 ≤ q v ∧ q v ≤ 0.8)
    (hV₀ : ((V₀).card : ℝ) ≤ δ * N / 2)
    (hD : δ * N ≤ ((Erdos637.neighborhoodDiff G u u' ∩ W₀).card : ℝ))
    {i : ℤ} (hi : |(i : ℝ)| ≤ N / 10) (hi' : |((i : ℝ) + 1)| ≤ N / 10) :
    diffAt G U W₀ q u u' N i + δ / 2 ≤ diffAt G U W₀ q u u' N (i + 1) := by
  classical
  have hdivmono : ∀ a b : ℝ, a ≤ b → a / N ≤ b / N := by
    intro a b hab
    have h1 : 0 ≤ (b - a) / N := div_nonneg (by linarith) hN.le
    have h2 : (b - a) / N = b / N - a / N := by ring
    linarith
  set D : Finset V := Erdos637.neighborhoodDiff G u u' ∩ W₀ with hDdef
  set S : Finset V := D \ V₀ with hSdef
  have hterm : ∀ v ∈ W₀, (if v ∈ S then 1 / N else 0) ≤
      ((if G.Adj u v then (1 : ℝ) else 0) - (if G.Adj u' v then (1 : ℝ) else 0)) *
        (pAt G W₀ q u N (i + 1) v - pAt G W₀ q u N i v) := by
    intro v hv
    have hpi : pAt G W₀ q u N i v = clamp09 (q v + (i : ℝ) * adjSign G u v / N) := by
      simp [pAt, hv]
    have hpi' : pAt G W₀ q u N (i + 1) v =
        clamp09 (q v + ((i : ℝ) + 1) * adjSign G u v / N) := by
      simp [pAt, hv]
    have habs : |(i : ℝ) * adjSign G u v / N| ≤ 1 / 10 := by
      rw [abs_div, abs_mul, abs_adjSign, abs_of_pos hN, mul_one, div_le_iff₀ hN]
      linarith [abs_le.mp hi]
    have habs' : |((i : ℝ) + 1) * adjSign G u v / N| ≤ 1 / 10 := by
      rw [abs_div, abs_mul, abs_adjSign, abs_of_pos hN, mul_one, div_le_iff₀ hN]
      linarith [abs_le.mp hi']
    rw [hpi, hpi', sub_ite_eq_ite_mul_adjSign G u u' v]
    by_cases hvD : v ∈ Erdos637.neighborhoodDiff G u u'
    · have hD1 : (if v ∈ Erdos637.neighborhoodDiff G u u' then (1 : ℝ) else 0) = 1 := by
        simp [hvD]
      rw [hD1, one_mul]
      by_cases hvV : v ∈ V₀
      · have hS0 : (if v ∈ S then (1 : ℝ) / N else 0) = 0 := by
          have hvS : v ∉ S := by simp [hSdef, hvV]
          simp [hvS]
        rw [hS0]
        by_cases hadj : G.Adj u v
        · have hsg : adjSign G u v = 1 := by simp [adjSign, hadj]
          rw [hsg]
          have hm : clamp09 (q v + (i : ℝ) * 1 / N) ≤ clamp09 (q v + ((i : ℝ) + 1) * 1 / N) :=
            clamp09_mono (by linarith [hdivmono ((i : ℝ) * 1) (((i : ℝ) + 1) * 1) (by linarith)])
          linarith
        · have hsg : adjSign G u v = -1 := by simp [adjSign, hadj]
          rw [hsg]
          have hm : clamp09 (q v + ((i : ℝ) + 1) * (-1) / N) ≤
              clamp09 (q v + (i : ℝ) * (-1) / N) :=
            clamp09_mono
              (by linarith [hdivmono (((i : ℝ) + 1) * (-1)) ((i : ℝ) * (-1)) (by linarith)])
          nlinarith [hm]
      · have hS1 : (if v ∈ S then (1 : ℝ) / N else 0) = 1 / N := by
          have hvS : v ∈ S := by
            simp only [hSdef, Finset.mem_sdiff, hDdef, Finset.mem_inter]
            exact ⟨⟨hvD, hv⟩, hvV⟩
          simp [hvS]
        rw [hS1]
        obtain ⟨hq1, hq2⟩ := hq v hv hvV
        have hb1 := abs_le.mp habs
        have hb2 := abs_le.mp habs'
        have hc1 : clamp09 (q v + (i : ℝ) * adjSign G u v / N) =
            q v + (i : ℝ) * adjSign G u v / N := by
          refine clamp09_eq_self ?_ ?_
          · norm_num
            linarith [hb1.1]
          · norm_num
            linarith [hb1.2]
        have hc2 : clamp09 (q v + ((i : ℝ) + 1) * adjSign G u v / N) =
            q v + ((i : ℝ) + 1) * adjSign G u v / N := by
          refine clamp09_eq_self ?_ ?_
          · norm_num
            linarith [hb2.1]
          · norm_num
            linarith [hb2.2]
        have hsq : adjSign G u v * adjSign G u v = 1 := by
          by_cases hadj : G.Adj u v <;> simp [adjSign, hadj]
        have hexp : (q v + ((i : ℝ) + 1) * adjSign G u v / N) -
            (q v + (i : ℝ) * adjSign G u v / N) = adjSign G u v / N := by
          field_simp
          ring
        rw [hc1, hc2, hexp, ← mul_div_assoc, hsq]
    · have hS0 : (if v ∈ S then (1 : ℝ) / N else 0) = 0 := by
        have hvS : v ∉ S := by
          simp only [hSdef, Finset.mem_sdiff, hDdef, Finset.mem_inter]
          tauto
        simp [hvS]
      have hD0 : (if v ∈ Erdos637.neighborhoodDiff G u u' then (1 : ℝ) else 0) = 0 := by
        simp [hvD]
      rw [hS0, hD0]
      simp
  have hcard : δ * N / 2 ≤ (S.card : ℝ) := by
    have hsub : D ⊆ S ∪ V₀ := by
      intro x hx
      by_cases hxV : x ∈ V₀
      · exact Finset.mem_union_right _ hxV
      · exact Finset.mem_union_left _ (by simp [hSdef, hx, hxV])
    have h1 : D.card ≤ S.card + V₀.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h1' : (D.card : ℝ) ≤ (S.card : ℝ) + (V₀.card : ℝ) := by exact_mod_cast h1
    linarith
  have hsum : δ / 2 ≤ ∑ v ∈ W₀, (if v ∈ S then 1 / N else 0) := by
    have hSW : S ⊆ W₀ := by
      intro x hx
      simp only [hSdef, Finset.mem_sdiff, hDdef, Finset.mem_inter] at hx
      exact hx.1.2
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSW, Finset.sum_const, nsmul_eq_mul,
      mul_one_div, le_div_iff₀ hN]
    linarith
  have hterm2 : ∀ v : V,
      ((if G.Adj u v then (1 : ℝ) else 0) - (if G.Adj u' v then (1 : ℝ) else 0)) *
        (pAt G W₀ q u N (i + 1) v - pAt G W₀ q u N i v) =
      (((if G.Adj u v then pAt G W₀ q u N (i + 1) v else 0) -
          (if G.Adj u' v then pAt G W₀ q u N (i + 1) v else 0)) -
        ((if G.Adj u v then pAt G W₀ q u N i v else 0) -
          (if G.Adj u' v then pAt G W₀ q u N i v else 0))) := by
    intro v
    by_cases h1 : G.Adj u v <;> by_cases h2 : G.Adj u' v <;>
      simp only [h1, h2, ite_true, ite_false] <;> ring
  have hdiff : diffAt G U W₀ q u u' N (i + 1) - diffAt G U W₀ q u u' N i =
      ∑ v ∈ W₀, ((if G.Adj u v then (1 : ℝ) else 0) - (if G.Adj u' v then (1 : ℝ) else 0)) *
        (pAt G W₀ q u N (i + 1) v - pAt G W₀ q u N i v) := by
    rw [Finset.sum_congr rfl (fun v _ ↦ hterm2 v)]
    simp only [Finset.sum_sub_distrib, diffAt, expDeg']
    ring
  have hmono := Finset.sum_le_sum hterm
  linarith [hdiff, hsum, hmono]

/-- A version of `card_filter_mem_Icc_of_step` where the step bound is only assumed inside
the window `[-K, K]`. -/
lemma card_filter_mem_Icc_of_step_on {K : ℕ} (f : ℤ → ℝ) {s : ℝ} (hs : 0 < s)
    (hstep : ∀ i : ℤ, -(K : ℤ) ≤ i → i + 1 ≤ (K : ℤ) → f i + s ≤ f (i + 1))
    (a L : ℝ) (hL : 0 ≤ L) :
    (((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
        fun i ↦ a ≤ f i ∧ f i ≤ a + L).card : ℝ) ≤ L / s + 1 := by
  classical
  set c : ℤ → ℤ := fun i ↦ max (-(K : ℤ)) (min (K : ℤ) i) with hc
  set g : ℤ → ℝ := fun i ↦ f (c i) + s * ((i : ℝ) - (c i : ℝ)) with hg
  have hgstep : ∀ i : ℤ, g i + s ≤ g (i + 1) := by
    intro i
    rcases (by simp only [hc]; omega :
        c (i + 1) = c i ∨ (c (i + 1) = c i + 1 ∧ -(K : ℤ) ≤ c i ∧ c i + 1 ≤ (K : ℤ))) with
      h | ⟨h, h1, h2⟩
    · simp only [hg, h]
      push_cast
      ring_nf
      linarith
    · have hfs := hstep (c i) h1 h2
      simp only [hg, h]
      push_cast
      linarith
  have hfilter : (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i ↦ a ≤ f i ∧ f i ≤ a + L) =
      (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i ↦ a ≤ g i ∧ g i ≤ a + L) := by
    refine Finset.filter_congr ?_
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hci : c i = i := by simp only [hc]; omega
    simp [hg, hci]
  rw [hfilter]
  exact card_filter_mem_Icc_of_step g hs hgstep a L hL

/-! ## The uniform counting measure on a finite product -/

section Coordinates

variable {M : ℕ}

/-- Updating the `u`-coordinate identifies the fibres of the `u`-coordinate map. -/
lemma sum_filter_coord_update (u : V) (F : (V → Fin M) → ℝ) (x y : Fin M) :
    ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = y), F (Function.update ω u x) =
      ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = x), F ω := by
  refine Finset.sum_nbij' (fun ω ↦ Function.update ω u x) (fun ω ↦ Function.update ω u y)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a _
    simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [Function.update_idem, ← ha.2, Function.update_eq_self]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [Function.update_idem, ← ha.2, Function.update_eq_self]
  · intro a _
    rfl

/-- The full sum of a function shifted in the `u`-coordinate is `M` times a fibre sum. -/
lemma sum_update_eq (u : V) (F : (V → Fin M) → ℝ) (x : Fin M) :
    ∑ ω : V → Fin M, F (Function.update ω u x) =
      (M : ℝ) * ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = x), F ω := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ω : V → Fin M ↦ ω u)
      (fun ω ↦ F (Function.update ω u x)),
    Finset.sum_congr rfl (fun y _ ↦ sum_filter_coord_update u F x y), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- For a function not depending on the `u`-coordinate, every fibre carries the same share. -/
lemma mul_sum_filter_coord (u : V) (F : (V → Fin M) → ℝ)
    (hinv : ∀ (ω : V → Fin M) (x : Fin M), F (Function.update ω u x) = F ω) (x : Fin M) :
    (M : ℝ) * ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = x), F ω =
      ∑ ω : V → Fin M, F ω := by
  rw [← sum_update_eq u F x]
  exact Finset.sum_congr rfl (fun ω _ ↦ hinv ω x)

/-- Independence of the `u`-coordinate from the remaining ones. -/
lemma sum_coord_mul (u : V) (g : Fin M → ℝ) (F : (V → Fin M) → ℝ)
    (hinv : ∀ (ω : V → Fin M) (x : Fin M), F (Function.update ω u x) = F ω) :
    (M : ℝ) * ∑ ω : V → Fin M, g (ω u) * F ω =
      (∑ x : Fin M, g x) * ∑ ω : V → Fin M, F ω := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ω : V → Fin M ↦ ω u) (fun ω ↦ g (ω u) * F ω),
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  have h1 : ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = x), g (ω u) * F ω =
      g x * ∑ ω ∈ Finset.univ.filter (fun ω : V → Fin M ↦ ω u = x), F ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω hω ↦ ?_)
    rw [(Finset.mem_filter.mp hω).2]
  rw [h1, ← mul_assoc, mul_comm (M : ℝ) (g x), mul_assoc, mul_sum_filter_coord u F hinv x]

/-- Counting form of the one-coordinate bound: if for every choice of the other coordinates
at most `b` values of the `u`-coordinate satisfy `P`, then `P` holds on at most a `b / M`
fraction of the product. -/
lemma mul_card_filter_le_of_coord (u : V) (P : (V → Fin M) → Prop) [DecidablePred P] {b : ℝ}
    (hb : ∀ ω : V → Fin M,
      ((Finset.univ.filter fun x : Fin M ↦ P (Function.update ω u x)).card : ℝ) ≤ b) :
    (M : ℝ) * ((Finset.univ.filter P).card : ℝ) ≤ (Fintype.card (V → Fin M) : ℝ) * b := by
  classical
  have hind : ∀ ω : V → Fin M,
      ((Finset.univ.filter fun x : Fin M ↦ P (Function.update ω u x)).card : ℝ) =
        ∑ x : Fin M, (if P (Function.update ω u x) then (1 : ℝ) else 0) := by
    intro ω
    rw [Finset.sum_boole]
  have hkey : (M : ℝ) * ((Finset.univ.filter P).card : ℝ) =
      ∑ ω : V → Fin M, ∑ x : Fin M, (if P (Function.update ω u x) then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun x _ ↦ sum_update_eq u (fun ω ↦ if P ω then (1 : ℝ) else 0) x),
      ← Finset.mul_sum,
      Finset.sum_fiberwise Finset.univ (fun ω : V → Fin M ↦ ω u)
        (fun ω ↦ if P ω then (1 : ℝ) else 0), Finset.sum_boole]
  rw [hkey]
  calc ∑ ω : V → Fin M, ∑ x : Fin M, (if P (Function.update ω u x) then (1 : ℝ) else 0)
      = ∑ ω : V → Fin M,
          ((Finset.univ.filter fun x : Fin M ↦ P (Function.update ω u x)).card : ℝ) :=
        Finset.sum_congr rfl (fun ω _ ↦ (hind ω).symm)
    _ ≤ ∑ _ω : V → Fin M, b := Finset.sum_le_sum (fun ω _ ↦ hb ω)
    _ = (Fintype.card (V → Fin M) : ℝ) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Coordinates

/-- Markov's inequality in counting form. -/
lemma mul_card_filter_le_sum {α : Type*} [Fintype α] (Y : α → ℝ) (hY : ∀ a, 0 ≤ Y a) {t : ℝ}
    (P : α → Prop) [DecidablePred P] (hP : ∀ a, P a → t ≤ Y a) :
    t * ((Finset.univ.filter P).card : ℝ) ≤ ∑ a, Y a := by
  calc t * ((Finset.univ.filter P).card : ℝ) = ∑ _a ∈ Finset.univ.filter P, t := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.filter P, Y a :=
        Finset.sum_le_sum fun a ha ↦ hP a (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a, Y a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ ↦ hY a

/-! ## Moments of the uniform coordinates -/

/-- Gauss' sum. -/
lemma sum_range_cast (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The sum of the first squares. -/
lemma sum_range_cast_sq (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- A uniform coordinate in `[-K, K]` has mean zero. -/
lemma sum_coordVal (K : ℕ) : ∑ x : Fin (2 * K + 1), (((x : ℕ) : ℝ) - K) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ ((j : ℝ) - K)) (2 * K + 1), Finset.sum_sub_distrib,
    sum_range_cast, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- A uniform coordinate in `[-K, K]` has second moment `K (K + 1) (2K + 1) / 3`. -/
lemma sum_coordVal_sq (K : ℕ) :
    ∑ x : Fin (2 * K + 1), (((x : ℕ) : ℝ) - K) ^ 2 = K * (K + 1) * (2 * K + 1) / 3 := by
  have hexp : ∀ j : ℕ, ((j : ℝ) - K) ^ 2 = (j : ℝ) ^ 2 - 2 * K * (j : ℝ) + K ^ 2 := by
    intro j
    ring
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ ((j : ℝ) - K) ^ 2) (2 * K + 1)]
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_cast,
    sum_range_cast_sq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The second moment of a signed sum of independent uniform coordinates. -/
lemma sum_sq_coordSum_le {K : ℕ} (T : Finset V) (c : V → ℝ) (hc : ∀ w, c w ^ 2 ≤ 1) :
    ∑ ω : V → Fin (2 * K + 1), (∑ w ∈ T, (((ω w : ℕ) : ℝ) - K) * c w) ^ 2 ≤
      (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (T.card * (K * (K + 1) / 3)) := by
  classical
  have hM : (0 : ℝ) < ((2 * K + 1 : ℕ) : ℝ) := by positivity
  have hdiag : ∀ w : V, ∑ ω : V → Fin (2 * K + 1), (((ω w : ℕ) : ℝ) - K) ^ 2 =
      (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (K * (K + 1) / 3) := by
    intro w
    have h := sum_coord_mul (M := 2 * K + 1) w (fun x ↦ (((x : ℕ) : ℝ) - K) ^ 2)
      (fun _ ↦ (1 : ℝ)) (fun _ _ ↦ rfl)
    rw [sum_coordVal_sq] at h
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    have h2 : ((2 * K + 1 : ℕ) : ℝ) *
        ∑ ω : V → Fin (2 * K + 1), (((ω w : ℕ) : ℝ) - K) ^ 2 =
        ((2 * K + 1 : ℕ) : ℝ) *
          ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (K * (K + 1) / 3)) := by
      rw [h]
      push_cast
      ring
    exact mul_left_cancel₀ (ne_of_gt hM) h2
  have hcross : ∀ w : V, ∀ w' : V, w ≠ w' → ∑ ω : V → Fin (2 * K + 1),
      ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w' : ℕ) : ℝ) - K) * c w') = 0 := by
    intro w w' hne
    have hinv : ∀ (ω : V → Fin (2 * K + 1)) (x : Fin (2 * K + 1)),
        ((((Function.update ω w x) w' : ℕ) : ℝ) - K) * c w' =
          ((((ω w' : ℕ) : ℝ) - K) * c w') := by
      intro ω x
      rw [Function.update_of_ne (Ne.symm hne)]
    have h := sum_coord_mul (M := 2 * K + 1) w (fun x ↦ (((x : ℕ) : ℝ) - K) * c w)
      (fun ω ↦ ((((ω w' : ℕ) : ℝ) - K) * c w')) hinv
    have hz : ∑ x : Fin (2 * K + 1), ((((x : ℕ) : ℝ) - K) * c w) = 0 := by
      rw [← Finset.sum_mul, sum_coordVal, zero_mul]
    rw [hz, zero_mul] at h
    exact mul_left_cancel₀ (ne_of_gt hM) (by rw [h, mul_zero])
  have hterm : ∀ w ∈ T, ∀ w' ∈ T, ∑ ω : V → Fin (2 * K + 1),
      ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w' : ℕ) : ℝ) - K) * c w') ≤
      (if w = w' then (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (K * (K + 1) / 3) else 0) := by
    intro w _ w' _
    by_cases hww : w = w'
    · subst hww
      have hle : ∀ ω : V → Fin (2 * K + 1),
          ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w : ℕ) : ℝ) - K) * c w) ≤
            (((ω w : ℕ) : ℝ) - K) ^ 2 := by
        intro ω
        nlinarith [hc w, sq_nonneg ((((ω w : ℕ) : ℝ) - K)), sq_nonneg (c w)]
      calc ∑ ω : V → Fin (2 * K + 1),
            ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w : ℕ) : ℝ) - K) * c w)
          ≤ ∑ ω : V → Fin (2 * K + 1), (((ω w : ℕ) : ℝ) - K) ^ 2 :=
            Finset.sum_le_sum (fun ω _ ↦ hle ω)
        _ = _ := by rw [hdiag w]
        _ = _ := by simp
    · rw [hcross w w' hww]
      simp [hww]
  have hexpand : ∀ ω : V → Fin (2 * K + 1),
      (∑ w ∈ T, (((ω w : ℕ) : ℝ) - K) * c w) ^ 2 =
        ∑ w ∈ T, ∑ w' ∈ T,
          ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w' : ℕ) : ℝ) - K) * c w') := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  calc ∑ ω : V → Fin (2 * K + 1), (∑ w ∈ T, (((ω w : ℕ) : ℝ) - K) * c w) ^ 2
      = ∑ w ∈ T, ∑ w' ∈ T, ∑ ω : V → Fin (2 * K + 1),
          ((((ω w : ℕ) : ℝ) - K) * c w) * ((((ω w' : ℕ) : ℝ) - K) * c w') := by
        rw [Finset.sum_congr rfl (fun ω _ ↦ hexpand ω), Finset.sum_comm]
        exact Finset.sum_congr rfl (fun w _ ↦ Finset.sum_comm)
    _ ≤ ∑ w ∈ T, ∑ w' ∈ T,
          (if w = w' then (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (K * (K + 1) / 3)
            else 0) :=
        Finset.sum_le_sum (fun w hw ↦ Finset.sum_le_sum (fun w' hw' ↦ hterm w hw w' hw'))
    _ = (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (T.card * (K * (K + 1) / 3)) := by
        rw [Finset.sum_congr rfl (fun w _ ↦ Finset.sum_ite_eq T w
            (fun _ ↦ (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (K * (K + 1) / 3))),
          Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
        ring

omit [Fintype V] [DecidableEq V] in
/-- The adjacency sign squares to one. -/
lemma adjSign_sq (G : SimpleGraph V) (u v : V) : adjSign G u v ^ 2 = 1 := by
  by_cases h : G.Adj u v <;> simp [adjSign, h]

/-! ## Lemma 7 -/

set_option maxHeartbeats 800000 in
/-- **JKLY Lemma 7.**  If `U` is `δ`-diverse relative to `W₀` and `|U| ≤ |W₀| ^ (2/3)`, there
is a probability vector `p` supported on `W₀` with values in `[0.1, 0.9]` and a subset
`U' ⊆ U` with `|U'| ≥ δ² |U| / 1460` whose expected degrees are pairwise `1`-separated. -/
theorem lemma7 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (G : SimpleGraph V) (U W₀ : Finset V) (_hUW : Disjoint U W₀)
    (hdiv : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' →
      δ * W₀.card ≤ (((Erdos637.neighborhoodDiff G u u') ∩ W₀).card : ℝ))
    (hUsize : (U.card : ℝ) ≤ (W₀.card : ℝ) ^ ((2 : ℝ) / 3)) (hN : 1 ≤ W₀.card) :
    ∃ (p : V → ℝ) (U' : Finset V), U' ⊆ U ∧
      (∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9) ∧ (∀ v ∉ W₀, p v = 0) ∧
      (δ ^ 2 / 1460) * U.card ≤ U'.card ∧
      ∀ u ∈ U', ∀ u' ∈ U', u ≠ u' → 1 ≤ |expDeg' G U W₀ p u - expDeg' G U W₀ p u'| := by
  classical
  have hN0 : (0 : ℝ) < (W₀.card : ℝ) := by
    have h : 0 < W₀.card := lt_of_lt_of_le Nat.zero_lt_one hN
    exact_mod_cast h
  have hUnn : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
  by_cases hsmall : (δ ^ 2 / 1460) * U.card ≤ 1
  · have hp1 : ∀ v ∈ W₀, (0.1 : ℝ) ≤ (if v ∈ W₀ then (1 : ℝ) / 2 else 0) ∧
        (if v ∈ W₀ then (1 : ℝ) / 2 else 0) ≤ 0.9 := by
      intro v hv
      have h : (if v ∈ W₀ then (1 : ℝ) / 2 else 0) = 1 / 2 := by simp [hv]
      rw [h]
      constructor <;> norm_num
    have hp0 : ∀ v ∉ W₀, (if v ∈ W₀ then (1 : ℝ) / 2 else 0) = 0 := by
      intro v hv
      simp [hv]
    rcases U.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
    · exact ⟨fun v ↦ if v ∈ W₀ then 1 / 2 else 0, ∅, Finset.Subset.refl _, hp1, hp0,
        by simp, by simp⟩
    · refine ⟨fun v ↦ if v ∈ W₀ then 1 / 2 else 0, {u₀},
        Finset.singleton_subset_iff.mpr hu₀, hp1, hp0, ?_, ?_⟩
      · simpa using hsmall
      · intro u hu u' hu' hne
        rw [Finset.mem_singleton] at hu hu'
        exact absurd (hu.trans hu'.symm) hne
  replace hsmall := not_le.mp hsmall
  -- numerical preliminaries
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hUn : (1460 : ℝ) < δ ^ 2 * (U.card : ℝ) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 1460)] at hsmall
    linarith
  have hUbig : (1460 : ℝ) < δ * (U.card : ℝ) := by
    nlinarith [mul_nonneg (mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)) hUnn]
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌊δ * (U.card : ℝ) / 5⌋₊ := ⟨_, rfl⟩
  have hKle : (K : ℝ) ≤ δ * (U.card : ℝ) / 5 := by
    rw [hKdef]
    exact Nat.floor_le (div_nonneg (mul_nonneg hδ0.le hUnn) (by norm_num))
  have hKgt : δ * (U.card : ℝ) / 5 - 1 < (K : ℝ) := by
    rw [hKdef]
    exact Nat.sub_one_lt_floor _
  have hKge : δ * (U.card : ℝ) / 10 ≤ (K : ℝ) := by linarith
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by linarith
  have hKU : K ≤ U.card := by
    have h : (K : ℝ) ≤ (U.card : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hUnn]
    exact_mod_cast h
  have hcube : ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (W₀.card : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast (W₀.card : ℝ) 2]
    norm_num
  have hK3 : (K : ℝ) ^ 3 ≤ δ ^ 3 * (W₀.card : ℝ) ^ 2 / 125 := by
    have h1 : (K : ℝ) ≤ δ * ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) / 5 := by
      have h2 : δ * (U.card : ℝ) ≤ δ * ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hUsize hδ0.le
      linarith
    have h3 : (K : ℝ) ^ 3 ≤ (δ * ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) / 5) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3
    calc (K : ℝ) ^ 3 ≤ (δ * ((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) / 5) ^ 3 := h3
      _ = δ ^ 3 * (((W₀.card : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ)) / 125 := by ring
      _ = δ ^ 3 * (W₀.card : ℝ) ^ 2 / 125 := by rw [hcube]
  have h125 : 125 * (K : ℝ) ^ 2 ≤ (W₀.card : ℝ) ^ 2 := by
    have hd3 : δ ^ 3 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ((K : ℝ))) (sub_nonneg.mpr hK1), sq_nonneg ((W₀.card : ℝ))]
  have hKN : 10 * (K : ℝ) ≤ (W₀.card : ℝ) := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hN0.le ?_
    calc (10 * (K : ℝ)) ^ 2 = 100 * (K : ℝ) ^ 2 := by ring
      _ ≤ 125 * (K : ℝ) ^ 2 := by nlinarith [sq_nonneg ((K : ℝ))]
      _ ≤ (W₀.card : ℝ) ^ 2 := h125
  obtain ⟨U₁, hU₁U, hU₁card⟩ := Finset.exists_subset_card_eq hKU
  -- the probability space
  have hΩpos : 0 < Fintype.card (V → Fin (2 * K + 1)) :=
    Fintype.card_pos_iff.mpr ⟨fun _ ↦ ⟨0, by omega⟩⟩
  have hΩ0 : (0 : ℝ) < (Fintype.card (V → Fin (2 * K + 1)) : ℝ) := by exact_mod_cast hΩpos
  obtain ⟨q, hqdef⟩ : ∃ q : (V → Fin (2 * K + 1)) → V → V → ℝ, q = fun ω u v ↦
      1 / 2 + (∑ w ∈ U₁.erase u, (((ω w : ℕ) : ℝ) - K) * adjSign G w v) / (W₀.card : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨pr, hprdef⟩ : ∃ pr : (V → Fin (2 * K + 1)) → V → ℝ, pr = fun ω v ↦
      if v ∈ W₀ then
        clamp09 (1 / 2 + (∑ w ∈ U₁, (((ω w : ℕ) : ℝ) - K) * adjSign G w v) / (W₀.card : ℝ))
      else 0 := ⟨_, rfl⟩
  have hpr_eq : ∀ (ω : V → Fin (2 * K + 1)) (u : V), u ∈ U₁ →
      pr ω = pAt G W₀ (q ω u) u (W₀.card : ℝ) (((ω u : ℕ) : ℤ) - (K : ℤ)) := by
    intro ω u hu
    funext v
    simp only [hprdef, hqdef, pAt]
    split_ifs with hv
    · congr 1
      rw [← Finset.sum_erase_add U₁ _ hu]
      push_cast
      ring
    · rfl
  have hq_inv : ∀ (ω : V → Fin (2 * K + 1)) (u : V) (x : Fin (2 * K + 1)) (v : V),
      q (Function.update ω u x) u v = q ω u v := by
    intro ω u x v
    simp only [hqdef]
    congr 2
    refine Finset.sum_congr rfl (fun w hw ↦ ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  obtain ⟨V₀, hV₀def⟩ : ∃ V₀ : (V → Fin (2 * K + 1)) → V → Finset V, V₀ = fun ω u ↦
      W₀.filter (fun v ↦ 0.3 < |q ω u v - 1 / 2|) := ⟨_, rfl⟩
  obtain ⟨good, hgooddef⟩ : ∃ good : (V → Fin (2 * K + 1)) → V → Prop,
      good = fun ω u ↦ ((V₀ ω u).card : ℝ) ≤ δ * W₀.card / 2 := ⟨_, rfl⟩
  have hgood_inv : ∀ (ω : V → Fin (2 * K + 1)) (u : V) (x : Fin (2 * K + 1)),
      good (Function.update ω u x) u = good ω u := by
    intro ω u x
    have h : V₀ (Function.update ω u x) u = V₀ ω u := by
      simp only [hV₀def]
      refine Finset.filter_congr (fun v _ ↦ ?_)
      rw [hq_inv ω u x v]
    simp only [hgooddef, h]
  -- Chebyshev for a single coordinate
  have hcheb : ∀ u v : V,
      ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦ 0.3 < |q ω u v - 1 / 2|).card : ℝ) ≤
        (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9) := by
    intro u v
    have hmark := mul_card_filter_le_sum
      (fun ω : V → Fin (2 * K + 1) ↦ (q ω u v - 1 / 2) ^ 2) (fun ω ↦ sq_nonneg _)
      (t := 0.09) (fun ω ↦ 0.3 < |q ω u v - 1 / 2|) (by
        intro ω h
        nlinarith [sq_abs (q ω u v - 1 / 2), abs_nonneg (q ω u v - 1 / 2)])
    have hid : ∀ ω : V → Fin (2 * K + 1), (q ω u v - 1 / 2) ^ 2 =
        (∑ w ∈ U₁.erase u, (((ω w : ℕ) : ℝ) - K) * adjSign G w v) ^ 2 /
          (W₀.card : ℝ) ^ 2 := by
      intro ω
      simp only [hqdef]
      field_simp
      ring
    have hsq := sum_sq_coordSum_le (K := K) (U₁.erase u) (fun w ↦ adjSign G w v)
      (fun w ↦ le_of_eq (adjSign_sq G w v))
    have hcard : ((U₁.erase u).card : ℝ) ≤ (K : ℝ) := by
      have h : (U₁.erase u).card ≤ U₁.card := Finset.card_erase_le
      rw [hU₁card] at h
      exact_mod_cast h
    have hmoment : ∑ ω : V → Fin (2 * K + 1), (q ω u v - 1 / 2) ^ 2 ≤
        (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * δ * (2 / 375) := by
      rw [Finset.sum_congr rfl (fun ω _ ↦ hid ω), ← Finset.sum_div]
      rw [div_le_iff₀ (pow_pos hN0 2)]
      have hstep1 : (Fintype.card (V → Fin (2 * K + 1)) : ℝ) *
          (((U₁.erase u).card : ℝ) * ((K : ℝ) * ((K : ℝ) + 1) / 3)) ≤
          (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * ((2 / 3) * (K : ℝ) ^ 3) := by
        have hEnn : (0 : ℝ) ≤ ((U₁.erase u).card : ℝ) := Nat.cast_nonneg _
        have h1 : ((U₁.erase u).card : ℝ) * ((K : ℝ) * ((K : ℝ) + 1) / 3) ≤
            (2 / 3) * (K : ℝ) ^ 3 := by nlinarith [hcard, hK1, hEnn]
        exact mul_le_mul_of_nonneg_left h1 hΩ0.le
      have hstep2 : (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * ((2 / 3) * (K : ℝ) ^ 3) ≤
          (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * δ * (2 / 375) * (W₀.card : ℝ) ^ 2 := by
        have hd : δ ^ 3 ≤ δ := by nlinarith
        have hN2 : (0 : ℝ) ≤ (W₀.card : ℝ) ^ 2 := sq_nonneg _
        have h1 : (2 / 3) * (K : ℝ) ^ 3 ≤ δ * (2 / 375) * (W₀.card : ℝ) ^ 2 := by
          linarith [hK3, mul_le_mul_of_nonneg_right hd hN2]
        linarith [mul_le_mul_of_nonneg_left h1 hΩ0.le]
      linarith [hsq, hstep1, hstep2]
    have hfin : (0.09 : ℝ) * ((Finset.univ.filter
        fun ω : V → Fin (2 * K + 1) ↦ 0.3 < |q ω u v - 1 / 2|).card : ℝ) ≤
        (0.09 : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9)) := by
      refine le_trans (le_trans hmark hmoment) ?_
      linarith [mul_nonneg hΩ0.le hδ0.le]
    exact le_of_mul_le_mul_left hfin (by norm_num)
  -- a fixed vertex is bad with probability at most 2/9
  have hbadu : ∀ u : V,
      ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦ ¬ good ω u).card : ℝ) ≤
        (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9) := by
    intro u
    have hmark := mul_card_filter_le_sum
      (fun ω : V → Fin (2 * K + 1) ↦ ((V₀ ω u).card : ℝ)) (fun ω ↦ Nat.cast_nonneg _)
      (t := δ * W₀.card / 2) (fun ω ↦ ¬ good ω u) (by
        intro ω h
        simp only [hgooddef] at h
        exact le_of_lt (not_le.mp h))
    have hsum : ∑ ω : V → Fin (2 * K + 1), ((V₀ ω u).card : ℝ) =
        ∑ v ∈ W₀, ((Finset.univ.filter
          fun ω : V → Fin (2 * K + 1) ↦ 0.3 < |q ω u v - 1 / 2|).card : ℝ) := by
      simp only [hV₀def]
      rw [Finset.sum_congr rfl (fun ω _ ↦ (Finset.sum_boole _ _).symm),
        Finset.sum_congr rfl (fun v _ ↦ (Finset.sum_boole _ _).symm), Finset.sum_comm]
    have hle : ∑ ω : V → Fin (2 * K + 1), ((V₀ ω u).card : ℝ) ≤
        (W₀.card : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9)) := by
      rw [hsum]
      calc ∑ v ∈ W₀, ((Finset.univ.filter
            fun ω : V → Fin (2 * K + 1) ↦ 0.3 < |q ω u v - 1 / 2|).card : ℝ)
          ≤ ∑ _v ∈ W₀, (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9) :=
            Finset.sum_le_sum (fun v _ ↦ hcheb u v)
        _ = (W₀.card : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : (0 : ℝ) < δ * (W₀.card : ℝ) / 2 := div_pos (mul_pos hδ0 hN0) (by norm_num)
    refine le_of_mul_le_mul_left ?_ hpos
    calc δ * (W₀.card : ℝ) / 2 * ((Finset.univ.filter
          fun ω : V → Fin (2 * K + 1) ↦ ¬ good ω u).card : ℝ)
        ≤ ∑ ω : V → Fin (2 * K + 1), ((V₀ ω u).card : ℝ) := hmark
      _ ≤ (W₀.card : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (δ / 9)) := hle
      _ ≤ δ * (W₀.card : ℝ) / 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9)) :=
          le_of_eq (by ring)
  -- with probability more than 1/2 at least half of U₁ is good
  have hE1 : ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
      ¬ ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ))).card : ℝ) ≤
      (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (4 / 9) := by
    have hsplit : ∀ ω : V → Fin (2 * K + 1),
        ((U₁.filter fun u ↦ good ω u).card : ℝ) +
          ((U₁.filter fun u ↦ ¬ good ω u).card : ℝ) = (K : ℝ) := by
      intro ω
      have h := Finset.card_filter_add_card_filter_not (s := U₁) (fun u ↦ good ω u)
      rw [hU₁card] at h
      exact_mod_cast h
    have hmark := mul_card_filter_le_sum
      (fun ω : V → Fin (2 * K + 1) ↦ ((U₁.filter fun u ↦ ¬ good ω u).card : ℝ))
      (fun ω ↦ Nat.cast_nonneg _) (t := (K : ℝ) / 2)
      (fun ω ↦ ¬ ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ))) (by
        intro ω h
        have := hsplit ω
        have h2 := not_le.mp h
        linarith)
    have hsum : ∑ ω : V → Fin (2 * K + 1), ((U₁.filter fun u ↦ ¬ good ω u).card : ℝ) =
        ∑ u ∈ U₁, ((Finset.univ.filter
          fun ω : V → Fin (2 * K + 1) ↦ ¬ good ω u).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun ω _ ↦ (Finset.sum_boole _ _).symm),
        Finset.sum_congr rfl (fun u _ ↦ (Finset.sum_boole _ _).symm), Finset.sum_comm]
    have hle : ∑ ω : V → Fin (2 * K + 1), ((U₁.filter fun u ↦ ¬ good ω u).card : ℝ) ≤
        (K : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9)) := by
      rw [hsum]
      calc ∑ u ∈ U₁, ((Finset.univ.filter
            fun ω : V → Fin (2 * K + 1) ↦ ¬ good ω u).card : ℝ)
          ≤ ∑ _u ∈ U₁, (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9) :=
            Finset.sum_le_sum (fun u _ ↦ hbadu u)
        _ = (K : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hU₁card]
    have hpos : (0 : ℝ) < (K : ℝ) / 2 := by linarith
    refine le_of_mul_le_mul_left ?_ hpos
    calc (K : ℝ) / 2 * ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          ¬ ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ))).card : ℝ)
        ≤ ∑ ω : V → Fin (2 * K + 1), ((U₁.filter fun u ↦ ¬ good ω u).card : ℝ) := hmark
      _ ≤ (K : ℝ) * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (2 / 9)) := hle
      _ ≤ (K : ℝ) / 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (4 / 9)) :=
          le_of_eq (by ring)
  -- the expected degree difference as a function of the coordinate at `u`
  have hdiffx : ∀ (ρ : V → Fin (2 * K + 1)) (u u₂ : V), u ∈ U₁ → ∀ x : Fin (2 * K + 1),
      expDeg' G U W₀ (pr (Function.update ρ u x)) u -
          expDeg' G U W₀ (pr (Function.update ρ u x)) u₂ =
        diffAt G U W₀ (q ρ u) u u₂ (W₀.card : ℝ) (((x : ℕ) : ℤ) - (K : ℤ)) := by
    intro ρ u u₂ hu x
    have hup : (Function.update ρ u x) u = x := by simp
    have hqq : q (Function.update ρ u x) u = q ρ u := funext (fun v ↦ hq_inv ρ u x v)
    have h1 : pr (Function.update ρ u x) =
        pAt G W₀ (q ρ u) u (W₀.card : ℝ) (((x : ℕ) : ℤ) - (K : ℤ)) := by
      rw [hpr_eq (Function.update ρ u x) u hu, hqq, hup]
    rw [h1, diffAt]
  -- for a fixed good vertex and fixed other coordinates, few coordinates are bad
  have hpair : ∀ u ∈ U₁, ∀ u' ∈ U₁, u ≠ u' →
      ((2 * K + 1 : ℕ) : ℝ) * ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
        good ω u ∧ |expDeg' G U W₀ (pr ω) u - expDeg' G U W₀ (pr ω) u'| ≤ 1).card : ℝ) ≤
      (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ) := by
    intro u hu u' hu' hne
    refine mul_card_filter_le_of_coord u _ ?_
    intro ρ
    by_cases hgρ : good ρ u
    · have hgρ' : ((V₀ ρ u).card : ℝ) ≤ δ * (W₀.card : ℝ) / 2 := by
        simpa only [hgooddef] using hgρ
      have hstep : ∀ i : ℤ, -(K : ℤ) ≤ i → i + 1 ≤ (K : ℤ) →
          diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) i + δ / 2 ≤
            diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) (i + 1) := by
        intro i hi1 hi2
        have hA : -((K : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
        have hB : (i : ℝ) + 1 ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hi2
        refine add_le_diffAt_succ G U W₀ (q ρ u) hN0 (V₀ := V₀ ρ u) ?_ hgρ' ?_ ?_ ?_
        · intro v hv hvV
          have hvV2 : ¬ (v ∈ W₀ ∧ 0.3 < |q ρ u v - 1 / 2|) := by
            simpa only [hV₀def, Finset.mem_filter] using hvV
          have h : |q ρ u v - 1 / 2| ≤ 0.3 := not_lt.mp (fun hc ↦ hvV2 ⟨hv, hc⟩)
          have h2 := abs_le.mp h
          constructor
          · linarith [h2.1]
          · linarith [h2.2]
        · exact hdiv u (hU₁U hu) u' (hU₁U hu') hne
        · rw [abs_le]
          constructor
          · linarith [hKN]
          · linarith [hKN]
        · rw [abs_le]
          constructor
          · linarith [hKN]
          · linarith [hKN]
      have hmaps : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 * K + 1) ↦
          good (Function.update ρ u x) u ∧
            |expDeg' G U W₀ (pr (Function.update ρ u x)) u -
              expDeg' G U W₀ (pr (Function.update ρ u x)) u'| ≤ 1),
          ((x : ℕ) : ℤ) - (K : ℤ) ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
            (fun i ↦ (-1 : ℝ) ≤ diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) i ∧
              diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) i ≤ -1 + 2) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hxb : (x : ℕ) < 2 * K + 1 := x.isLt
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨by omega, ?_⟩
        have habs := hx.2.2
        rw [hdiffx ρ u u' hu x] at habs
        have h2 := abs_le.mp habs
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have hinj : Set.InjOn (fun x : Fin (2 * K + 1) ↦ ((x : ℕ) : ℤ) - (K : ℤ))
          ↑(Finset.univ.filter (fun x : Fin (2 * K + 1) ↦
            good (Function.update ρ u x) u ∧
              |expDeg' G U W₀ (pr (Function.update ρ u x)) u -
                expDeg' G U W₀ (pr (Function.update ρ u x)) u'| ≤ 1)) := by
        intro a _ b _ hab
        have hab' : ((a : ℕ) : ℤ) - (K : ℤ) = ((b : ℕ) : ℤ) - (K : ℤ) := hab
        have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by omega
        have h2 : (a : ℕ) = (b : ℕ) := by exact_mod_cast this
        exact Fin.ext h2
      have hle := Finset.card_le_card_of_injOn _ hmaps hinj
      have hwin := card_filter_mem_Icc_of_step_on (K := K)
        (diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ)) (by linarith : (0 : ℝ) < δ / 2) hstep
        (-1) 2 (by norm_num)
      have hle' : ((Finset.univ.filter (fun x : Fin (2 * K + 1) ↦
          good (Function.update ρ u x) u ∧
            |expDeg' G U W₀ (pr (Function.update ρ u x)) u -
              expDeg' G U W₀ (pr (Function.update ρ u x)) u'| ≤ 1)).card : ℝ) ≤
          (((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
            (fun i ↦ (-1 : ℝ) ≤ diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) i ∧
              diffAt G U W₀ (q ρ u) u u' (W₀.card : ℝ) i ≤ -1 + 2)).card : ℝ) := by
        exact Nat.cast_le.mpr hle
      have hfinal : (2 : ℝ) / (δ / 2) + 1 ≤ 5 / δ := by
        have h1 : (2 : ℝ) / (δ / 2) = 4 / δ := by
          rw [div_div_eq_mul_div]
          norm_num
        have h2 : (1 : ℝ) ≤ 1 / δ := by
          rw [le_div_iff₀ hδ0]
          linarith
        have h3 : (4 : ℝ) / δ + 1 / δ = 5 / δ := by
          rw [← add_div]
          norm_num
        linarith
      exact le_trans hle' (le_trans hwin hfinal)
    · have hempty : (Finset.univ.filter (fun x : Fin (2 * K + 1) ↦
          good (Function.update ρ u x) u ∧
            |expDeg' G U W₀ (pr (Function.update ρ u x)) u -
              expDeg' G U W₀ (pr (Function.update ρ u x)) u'| ≤ 1)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro x _
        rw [hgood_inv ρ u x]
        exact fun h ↦ hgρ h.1
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact le_of_lt (div_pos (by norm_num) hδ0)
  -- the bad pairs
  obtain ⟨badPairs, hbpdef⟩ : ∃ badPairs : (V → Fin (2 * K + 1)) → Finset (V × V),
      badPairs = fun ω ↦ (U₁ ×ˢ U₁).filter (fun z ↦ z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
        |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1) := ⟨_, rfl⟩
  have hbpsum : ((2 * K + 1 : ℕ) : ℝ) *
      (∑ ω : V → Fin (2 * K + 1), ((badPairs ω).card : ℝ)) * δ ≤
      (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * 5) := by
    have hsum : ∑ ω : V → Fin (2 * K + 1), ((badPairs ω).card : ℝ) =
        ∑ z ∈ U₁ ×ˢ U₁, ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
          |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1).card : ℝ) := by
      simp only [hbpdef]
      rw [Finset.sum_congr rfl (fun ω _ ↦ (Finset.sum_boole _ _).symm),
        Finset.sum_congr rfl (fun z _ ↦ (Finset.sum_boole _ _).symm), Finset.sum_comm]
    have hz : ∀ z ∈ U₁ ×ˢ U₁, ((2 * K + 1 : ℕ) : ℝ) *
        ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
          |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1).card : ℝ) ≤
        (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ) := by
      intro z hzmem
      rw [Finset.mem_product] at hzmem
      by_cases hz12 : z.1 = z.2
      · have hempty : (Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
            z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
            |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun ω _ h ↦ h.1 hz12)
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
        exact mul_nonneg hΩ0.le (le_of_lt (div_pos (by norm_num) hδ0))
      · refine le_trans ?_ (hpair z.1 hzmem.1 z.2 hzmem.2 hz12)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsub : (Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
            z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
            |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1) ⊆
            (Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
              good ω z.1 ∧ |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1) := by
          intro ω hω
          rw [Finset.mem_filter] at hω ⊢
          exact ⟨hω.1, hω.2.2.1, hω.2.2.2.2⟩
        exact_mod_cast Finset.card_le_card hsub
    have hmain : ((2 * K + 1 : ℕ) : ℝ) *
        (∑ ω : V → Fin (2 * K + 1), ((badPairs ω).card : ℝ)) ≤
        (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ)) := by
      rw [hsum, Finset.mul_sum]
      calc ∑ z ∈ U₁ ×ˢ U₁, ((2 * K + 1 : ℕ) : ℝ) *
            ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
              z.1 ≠ z.2 ∧ good ω z.1 ∧ good ω z.2 ∧
              |expDeg' G U W₀ (pr ω) z.1 - expDeg' G U W₀ (pr ω) z.2| ≤ 1).card : ℝ)
          ≤ ∑ _z ∈ U₁ ×ˢ U₁, (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ) :=
            Finset.sum_le_sum hz
        _ = (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ)) := by
            rw [Finset.sum_const, Finset.card_product, hU₁card, nsmul_eq_mul]
            push_cast
            ring
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    calc ((2 * K + 1 : ℕ) : ℝ) *
          (∑ ω : V → Fin (2 * K + 1), ((badPairs ω).card : ℝ)) * δ
        ≤ (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / δ)) * δ :=
          mul_le_mul_of_nonneg_right hmain hδ0.le
      _ = (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * 5) := by
          field_simp
  -- Markov for the bad pairs
  have hBbound : ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
      6 * (K : ℝ) < δ * ((badPairs ω).card : ℝ)).card : ℝ) ≤
      (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / 12) := by
    have hmark := mul_card_filter_le_sum
      (fun ω : V → Fin (2 * K + 1) ↦ δ * ((badPairs ω).card : ℝ))
      (fun ω ↦ mul_nonneg hδ0.le (Nat.cast_nonneg _)) (t := 6 * (K : ℝ))
      (fun ω ↦ 6 * (K : ℝ) < δ * ((badPairs ω).card : ℝ)) (fun ω h ↦ le_of_lt h)
    rw [← Finset.mul_sum] at hmark
    have hM : 2 * (K : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hSnn : (0 : ℝ) ≤ ∑ ω : V → Fin (2 * K + 1), ((badPairs ω).card : ℝ) :=
      Finset.sum_nonneg (fun ω _ ↦ Nat.cast_nonneg _)
    have key : ∀ C S : ℝ, 0 ≤ C → 0 ≤ S → 6 * (K : ℝ) * C ≤ δ * S →
        ((2 * K + 1 : ℕ) : ℝ) * S * δ ≤
          (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * 5) →
        C ≤ (Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / 12) := by
      intro C S hC hS h1 h2
      have h6KC : (0 : ℝ) ≤ 6 * (K : ℝ) * C := mul_nonneg (by linarith) hC
      have hstep1 : 2 * (K : ℝ) * (6 * (K : ℝ) * C) ≤ ((2 * K + 1 : ℕ) : ℝ) * (6 * (K : ℝ) * C) :=
        mul_le_mul_of_nonneg_right hM h6KC
      have hstep2 : ((2 * K + 1 : ℕ) : ℝ) * (6 * (K : ℝ) * C) ≤
          ((2 * K + 1 : ℕ) : ℝ) * (δ * S) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hstep3 : ((2 * K + 1 : ℕ) : ℝ) * (δ * S) = ((2 * K + 1 : ℕ) : ℝ) * S * δ := by ring
      have hkey : 12 * (K : ℝ) ^ 2 * C ≤
          5 * (K : ℝ) ^ 2 * (Fintype.card (V → Fin (2 * K + 1)) : ℝ) := by
        nlinarith [hstep1, hstep2, hstep3, h2]
      have hK2pos : (0 : ℝ) < 12 * (K : ℝ) ^ 2 := by nlinarith
      refine le_of_mul_le_mul_left ?_ hK2pos
      calc 12 * (K : ℝ) ^ 2 * C ≤
          5 * (K : ℝ) ^ 2 * (Fintype.card (V → Fin (2 * K + 1)) : ℝ) := hkey
        _ = 12 * (K : ℝ) ^ 2 * ((Fintype.card (V → Fin (2 * K + 1)) : ℝ) * (5 / 12)) := by ring
    exact key _ _ (Nat.cast_nonneg _) hSnn hmark hbpsum
  -- a good outcome exists
  have hexists : ∃ ω : V → Fin (2 * K + 1),
      ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ)) ∧
      δ * ((badPairs ω).card : ℝ) ≤ 6 * (K : ℝ) := by
    by_contra hcon
    have hall : ∀ ω : V → Fin (2 * K + 1),
        ¬ (((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ)) ∧
          δ * ((badPairs ω).card : ℝ) ≤ 6 * (K : ℝ)) := fun ω h ↦ hcon ⟨ω, h⟩
    have hsub : (Finset.univ : Finset (V → Fin (2 * K + 1))) ⊆
        (Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          ¬ ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ))) ∪
        (Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          6 * (K : ℝ) < δ * ((badPairs ω).card : ℝ)) := by
      intro ω _
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : (K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ)
      · exact Or.inr ⟨Finset.mem_univ _, not_le.mp (fun h ↦ hall ω ⟨h1, h⟩)⟩
      · exact Or.inl ⟨Finset.mem_univ _, h1⟩
    have hcard : (Fintype.card (V → Fin (2 * K + 1)) : ℝ) ≤
        ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          ¬ ((K : ℝ) / 2 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ))).card : ℝ) +
        ((Finset.univ.filter fun ω : V → Fin (2 * K + 1) ↦
          6 * (K : ℝ) < δ * ((badPairs ω).card : ℝ)).card : ℝ) := by
      have h := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      rw [Finset.card_univ] at h
      exact_mod_cast h
    linarith [hE1, hBbound, hΩ0]
  obtain ⟨ω, hω1, hω2⟩ := hexists
  -- the conflict graph
  obtain ⟨J, hJadj⟩ : ∃ J : SimpleGraph V, ∀ a b : V, J.Adj a b ↔
      (a ≠ b ∧ a ∈ U₁.filter (fun u ↦ good ω u) ∧ b ∈ U₁.filter (fun u ↦ good ω u) ∧
        |expDeg' G U W₀ (pr ω) a - expDeg' G U W₀ (pr ω) b| ≤ 1) := by
    refine ⟨SimpleGraph.fromRel (fun a b ↦ a ∈ U₁.filter (fun u ↦ good ω u) ∧
      b ∈ U₁.filter (fun u ↦ good ω u) ∧
      |expDeg' G U W₀ (pr ω) a - expDeg' G U W₀ (pr ω) b| ≤ 1), fun a b ↦ ?_⟩
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
      · exact ⟨hne, h1, h2, h3⟩
      · refine ⟨hne, h2, h1, ?_⟩
        rw [abs_sub_comm]
        exact h3
    · rintro ⟨hne, h1, h2, h3⟩
      exact ⟨hne, Or.inl ⟨h1, h2, h3⟩⟩
  have hJedge : 2 * (inducedEdges J (U₁.filter fun u ↦ good ω u)) ≤ (badPairs ω).card := by
    have h1 : inducedEdges J (U₁.filter fun u ↦ good ω u) ≤ J.edgeFinset.card :=
      Finset.card_filter_le _ _
    have h3 : 2 * J.edgeFinset.card ≤ (badPairs ω).card := by
      rw [SimpleGraph.two_mul_card_edgeFinset]
      refine Finset.card_le_card ?_
      intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨z1, z2⟩ := z
      have hadj : J.Adj z1 z2 := hz.2
      rw [hJadj] at hadj
      obtain ⟨hne, ha, hb, hab⟩ := hadj
      simp only [hbpdef, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp hb).1⟩, hne,
        (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab⟩
    omega
  obtain ⟨I, hIUg, hIind, hIcard⟩ :=
    exists_indepSet_subset_card_ge_of_edges J (U₁.filter fun u ↦ good ω u)
  refine ⟨pr ω, I, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans hIUg (le_trans (Finset.filter_subset _ _) hU₁U)
  · intro v hv
    have hval : pr ω v = clamp09 (1 / 2 +
        (∑ w ∈ U₁, (((ω w : ℕ) : ℝ) - K) * adjSign G w v) / (W₀.card : ℝ)) := by
      simp [hprdef, hv]
    rw [hval]
    exact clamp09_mem _
  · intro v hv
    simp [hprdef, hv]
  · -- the cardinality bound
    have hUgcard : ((U₁.filter fun u ↦ good ω u).card : ℝ) ≤ (K : ℝ) := by
      have h : (U₁.filter fun u ↦ good ω u).card ≤ U₁.card := Finset.card_filter_le _ _
      rw [hU₁card] at h
      exact_mod_cast h
    have hUgnn : (0 : ℝ) ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ) := Nat.cast_nonneg _
    have hEnn : (0 : ℝ) ≤ (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ) :=
      Nat.cast_nonneg _
    have hEbound : δ * (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ) ≤ 3 * (K : ℝ) := by
      have h : (2 : ℝ) * (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ) ≤
          ((badPairs ω).card : ℝ) := by exact_mod_cast hJedge
      nlinarith [hω2, hδ0]
    have hpos : (0 : ℝ) < ((U₁.filter fun u ↦ good ω u).card : ℝ) +
        4 * (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ) := by linarith
    refine le_trans ?_ hIcard
    rw [le_div_iff₀ hpos]
    have hA : δ * (U.card : ℝ) ≤ 10 * (K : ℝ) := by linarith
    have hB : δ * (((U₁.filter fun u ↦ good ω u).card : ℝ) +
        4 * (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ)) ≤ 13 * (K : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hUgnn]
    have hprod : (δ * (U.card : ℝ)) * (δ * (((U₁.filter fun u ↦ good ω u).card : ℝ) +
        4 * (inducedEdges J (U₁.filter fun u ↦ good ω u) : ℝ))) ≤
        (10 * (K : ℝ)) * (13 * (K : ℝ)) :=
      mul_le_mul hA hB (mul_nonneg hδ0.le hpos.le) (by linarith)
    have h3 : (K : ℝ) ^ 2 / 4 ≤ ((U₁.filter fun u ↦ good ω u).card : ℝ) ^ 2 := by
      nlinarith [hω1, hUgnn, hK1]
    nlinarith [hprod, h3]
  · intro a ha b hb hne
    have hJ : ¬ J.Adj a b := hIind ha hb hne
    rw [hJadj] at hJ
    have ha' : a ∈ U₁.filter (fun u ↦ good ω u) := hIUg ha
    have hb' : b ∈ U₁.filter (fun u ↦ good ω u) := hIUg hb
    have h : ¬ (|expDeg' G U W₀ (pr ω) a - expDeg' G U W₀ (pr ω) b| ≤ 1) :=
      fun hc ↦ hJ ⟨hne, ha', hb', hc⟩
    exact le_of_lt (not_le.mp h)

end JKLY
