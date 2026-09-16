/-
Copyright (c) 2026 MerLean. All rights reserved.
Released under Apache 2.0 license.
-/
import JSP518.JKLY.Anticoncentration
import JSP518.JKLY.Relaxation
import JSP518.JKLY.RandomVector
import JSP518.JKLY.Diversity

/-!
# Jenssen–Keevash–Long–Yepremyan: many distinct degrees in a Ramsey graph

This file assembles the JKLY strengthening of Erdős problem 637.  `jkly_theorem2` is the
δ-diverse form: a `δ`-diverse set of at least `|V| ^ (2/3)` vertices forces an induced
subgraph with `c |V| ^ (2/3)` distinct degrees.  `jkly_distinct_degrees` combines it with
the Kwan–Sah–Sauermann–Sawhney richness extraction of `Diversity.lean` to get the main
theorem for `C`-Ramsey graphs, and `jkly_distinct_degrees_nat` is the frozen root with the
Ramsey constant presented as `k + 1` for a natural number `k`.
-/

namespace JKLY

attribute [local instance] Classical.propDecidable

universe u

/-! ## Real-power bookkeeping -/

/-- A natural power of an `n`-th root is the corresponding real power. -/
lemma pow_rpow_one_div {b : ℝ} (hb : 0 ≤ b) {k : ℝ} (m : ℕ) :
    (b ^ ((1 : ℝ) / k)) ^ m = b ^ ((m : ℝ) / k) := by
  rw [← Real.rpow_natCast (b ^ ((1 : ℝ) / k)) m, ← Real.rpow_mul hb]
  congr 1
  ring

/-- Monotonicity of the `k`-th root: `a ^ m ≤ b` forces `a ≤ b ^ (1 / k)` when `(m : ℝ) = k`. -/
lemma le_rpow_one_div_of_pow_le {a b k : ℝ} {m : ℕ} (ha : 0 ≤ a) (hk : (m : ℝ) = k)
    (hk0 : k ≠ 0) (hab : a ^ m ≤ b) : a ≤ b ^ ((1 : ℝ) / k) := by
  have hkpos : (0 : ℝ) ≤ k := hk ▸ Nat.cast_nonneg m
  have h1 : ((a ^ m : ℝ)) ^ ((1 : ℝ) / k) ≤ b ^ ((1 : ℝ) / k) :=
    Real.rpow_le_rpow (by positivity) hab (by positivity)
  rwa [← Real.rpow_natCast a m, hk, ← Real.rpow_mul ha, mul_one_div, div_self hk0,
    Real.rpow_one] at h1

/-! ## Theorem 2 -/

/-- **JKLY Theorem 2.**  For every `δ ∈ (0, 1]` there is `c > 0` such that every graph on a
large enough vertex type carrying a `δ`-diverse set of at least `|V| ^ (2/3)` vertices has a
vertex set `W` with at least `c |V| ^ (2/3)` distinct degrees inside `W`. -/
theorem jkly_theorem2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
        ∀ (G : SimpleGraph V) (U : Finset V), Diverse G δ U →
          (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ U.card →
            ∃ W : Finset V, c * (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤
              Erdos637.numDistinctDegrees G W := by
  classical
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδ20 : (0 : ℝ) < δ / 2 := by linarith
  have hδ21 : δ / 2 ≤ 1 := by linarith
  have hantic : AnticBound.{u} anticConst :=
    fun p hp P Q hPQ hq t ↦ antic_bound p hp P Q hPQ hq t
  have hCpos : (0 : ℝ) < anticConst := anticConst_pos
  have hDpos : (0 : ℝ) < 4 + 160 * anticConst / Real.sqrt (δ / 2) := by
    have h := div_nonneg (by linarith : (0 : ℝ) ≤ 160 * anticConst)
      (Real.sqrt_nonneg (δ / 2))
    linarith
  have hinv0 : (0 : ℝ) < 1 / (4 + 160 * anticConst / Real.sqrt (δ / 2)) :=
    one_div_pos.mpr hDpos
  refine ⟨1 / (4 + 160 * anticConst / Real.sqrt (δ / 2)) * ((δ / 2) ^ 2 / 1460) / 8,
    div_pos (mul_pos hinv0 (by positivity)) (by norm_num), ⌈(1 / δ + 4) ^ 3⌉₊, ?_⟩
  intro V _ _ hN G U hdiv hUcard
  have hMnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; exact Real.rpow_nonneg hMnn _
  have hx3 : x ^ 3 = (Fintype.card V : ℝ) := by
    rw [hxdef, pow_rpow_one_div hMnn 3]
    norm_num
  have hx2 : x ^ 2 = (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hxdef, pow_rpow_one_div hMnn 2]
    norm_num
  have hKnn : (0 : ℝ) ≤ 1 / δ + 4 := by positivity
  have hMK : ((1 / δ + 4) ^ 3 : ℝ) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hxK : 1 / δ + 4 ≤ x := by
    rw [hxdef]
    exact le_rpow_one_div_of_pow_le hKnn (by norm_num) (by norm_num) hMK
  have hδinv : (0 : ℝ) < 1 / δ := by positivity
  have hx4 : (4 : ℝ) ≤ x := by linarith
  have hx16 : (16 : ℝ) ≤ x ^ 2 := by nlinarith
  have hδx : (1 : ℝ) ≤ δ * x := by
    have h : δ * (1 / δ + 4) ≤ δ * x := mul_le_mul_of_nonneg_left hxK hδ0.le
    have hinv : δ * (1 / δ + 4) = 1 + 4 * δ := by field_simp
    rw [hinv] at h
    linarith
  have hδx3 : x ^ 2 ≤ δ * x ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hδx (sq_nonneg x)]
  -- the small set `U₂` of size about `|V| ^ (2/3) / 8`
  have hceilnn : (0 : ℝ) ≤ x ^ 2 / 8 := by positivity
  have hmle : (⌈x ^ 2 / 8⌉₊ : ℝ) ≤ x ^ 2 / 8 + 1 := (Nat.ceil_lt_add_one hceilnn).le
  have hmge : x ^ 2 / 8 ≤ (⌈x ^ 2 / 8⌉₊ : ℝ) := Nat.le_ceil _
  have hx2U : x ^ 2 ≤ (U.card : ℝ) := by rw [hx2]; exact hUcard
  have hmU : ⌈x ^ 2 / 8⌉₊ ≤ U.card := by
    have h : (⌈x ^ 2 / 8⌉₊ : ℝ) ≤ (U.card : ℝ) := by linarith
    exact_mod_cast h
  obtain ⟨U₂, hU₂U, hU₂card⟩ := Finset.exists_subset_card_eq hmU
  have hU₂R : (U₂.card : ℝ) = (⌈x ^ 2 / 8⌉₊ : ℝ) := by rw [hU₂card]
  have hU₂le : (U₂.card : ℝ) ≤ x ^ 2 / 8 + 1 := by rw [hU₂R]; exact hmle
  have hU₂ge : x ^ 2 / 8 ≤ (U₂.card : ℝ) := by rw [hU₂R]; exact hmge
  have hU₂M : (U₂.card : ℝ) ≤ (Fintype.card V : ℝ) := by nlinarith
  -- the reservoir
  have hdisj : Disjoint U₂ U₂ᶜ := disjoint_compl_right
  have hW₀card : ((U₂ᶜ : Finset V).card : ℝ) = (Fintype.card V : ℝ) - (U₂.card : ℝ) := by
    have hle : U₂.card ≤ Fintype.card V := by exact_mod_cast hU₂M
    rw [Finset.card_compl, Nat.cast_sub hle]
  have hW₀half : (Fintype.card V : ℝ) / 2 ≤ ((U₂ᶜ : Finset V).card : ℝ) := by
    rw [hW₀card, ← hx3]
    nlinarith
  have hW₀le : ((U₂ᶜ : Finset V).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    rw [hW₀card]
    have : (0 : ℝ) ≤ (U₂.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hW₀pos : 1 ≤ (U₂ᶜ : Finset V).card := by
    have h : (1 : ℝ) ≤ ((U₂ᶜ : Finset V).card : ℝ) := by
      rw [← hx3] at hW₀half
      nlinarith
    exact_mod_cast h
  -- diversity transfers to the reservoir with the halved constant
  have hmMhalf : (U₂.card : ℝ) ≤ δ / 2 * (Fintype.card V : ℝ) := by
    rw [← hx3]
    linarith
  have hdivW : ∀ u ∈ U₂, ∀ u' ∈ U₂, u ≠ u' →
      δ / 2 * ((U₂ᶜ : Finset V).card : ℝ) ≤
        (((Erdos637.neighborhoodDiff G u u') ∩ U₂ᶜ).card : ℝ) := by
    intro u hu u' hu' hne
    have hND : δ * (Fintype.card V : ℝ) ≤ ((Erdos637.neighborhoodDiff G u u').card : ℝ) :=
      hdiv u (hU₂U hu) u' (hU₂U hu') hne
    have hinter : (Erdos637.neighborhoodDiff G u u') ∩ U₂ᶜ =
        (Erdos637.neighborhoodDiff G u u') \ U₂ := by
      ext v
      simp
    have hsplit : (Erdos637.neighborhoodDiff G u u').card ≤
        ((Erdos637.neighborhoodDiff G u u') \ U₂).card + U₂.card :=
      Nat.sub_le_iff_le_add.mp (Finset.le_card_sdiff U₂ _)
    have hsplitR : ((Erdos637.neighborhoodDiff G u u').card : ℝ) ≤
        (((Erdos637.neighborhoodDiff G u u') \ U₂).card : ℝ) + (U₂.card : ℝ) := by
      exact_mod_cast hsplit
    have hmul : δ / 2 * ((U₂ᶜ : Finset V).card : ℝ) ≤ δ / 2 * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hW₀le hδ20.le
    rw [hinter]
    linarith
  -- the sizes fit the hypothesis of Lemma 7
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = ((U₂ᶜ : Finset V).card : ℝ) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hy2 : y ^ 2 = ((U₂ᶜ : Finset V).card : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hydef, pow_rpow_one_div (Nat.cast_nonneg _) 2]
    norm_num
  have hyx : x / 2 ≤ y := by
    rw [hydef]
    refine le_rpow_one_div_of_pow_le (m := 3) (by linarith) (by norm_num) (by norm_num) ?_
    have hx3nn : (0 : ℝ) ≤ x ^ 3 := pow_nonneg hx0 3
    have h : x ^ 3 / 2 ≤ ((U₂ᶜ : Finset V).card : ℝ) := by rw [← hx3] at hW₀half; linarith
    nlinarith
  have hUsize : (U₂.card : ℝ) ≤ ((U₂ᶜ : Finset V).card : ℝ) ^ ((2 : ℝ) / 3) := by
    have hyq : x ^ 2 / 4 ≤ y ^ 2 :=
      le_of_le_of_eq (le_of_eq_of_le (by ring)
        (mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ x / 2) hyx)) (by ring)
    rw [← hy2]
    linarith only [hU₂le, hx16, hyq]
  -- Lemma 7 produces the separated probability vector
  obtain ⟨p, U', hU'sub, hp, hp0, hU'card, hsep⟩ :=
    lemma7 hδ20 hδ21 G U₂ U₂ᶜ hdisj hdivW hUsize hW₀pos
  -- Lemma 4 turns separation into distinct degrees
  obtain ⟨W, _hWsub, hWcard⟩ :=
    lemma4 hCpos hantic hδ20 hδ21 G U₂ U₂ᶜ U' hdisj hU'sub hW₀pos p hp hp0
      (fun u hu u' hu' hne ↦ hsep u hu u' hu' hne)
      (fun u hu u' hu' hne ↦ hdivW u (hU'sub hu) u' (hU'sub hu') hne)
  refine ⟨U₂ ∪ W, le_trans ?_ hWcard⟩
  have hstep : (δ / 2) ^ 2 / 1460 * (x ^ 2 / 8) ≤ (U'.card : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hU₂ge (by positivity)) hU'card
  calc 1 / (4 + 160 * anticConst / Real.sqrt (δ / 2)) * ((δ / 2) ^ 2 / 1460) / 8 *
        (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3)
      = 1 / (4 + 160 * anticConst / Real.sqrt (δ / 2)) * ((δ / 2) ^ 2 / 1460 * (x ^ 2 / 8)) := by
        rw [← hx2]; ring
    _ ≤ 1 / (4 + 160 * anticConst / Real.sqrt (δ / 2)) * (U'.card : ℝ) :=
        mul_le_mul_of_nonneg_left hstep hinv0.le

/-! ## Theorem 1 -/

/-- The Ramsey-freeness condition is monotone in the constant: a `C`-Ramsey graph is also
`C'`-Ramsey for every `C' ≥ C`. -/
theorem ramseyFree_mono {n : ℕ} {C C' : ℝ} {G : SimpleGraph (Fin n)}
    (hG : Erdos88.RamseyFree C G) (hCC' : C ≤ C') : Erdos88.RamseyFree C' G := by
  intro S hS
  refine lt_of_lt_of_le (hG S hS) (mul_le_mul_of_nonneg_right hCC' ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

/-- **JKLY Theorem 1.**  For every `C > 0` there is `β > 0` such that every `C`-Ramsey graph
on `n ≥ N₀` vertices has a vertex set `W` inducing at least `β n ^ (2/3)` distinct degrees. -/
theorem jkly_distinct_degrees (C : ℝ) (hC : 0 < C) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
      ∃ W : Finset (Fin n), β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W := by
  classical
  obtain ⟨ρ, lam, hρ0, hρ1, hlam0, N₁, hdiverse⟩ := exists_diverse_subgraph_of_ramseyFree C hC
  obtain ⟨c, hc0, N₂, hthm2⟩ := jkly_theorem2.{0} (ρ / 4) (by positivity) (by linarith)
  refine ⟨c * lam ^ ((2 : ℝ) / 3), mul_pos hc0 (Real.rpow_pos_of_pos hlam0 _),
    max N₁ ⌈((N₂ : ℝ) + 531441) / lam⌉₊, ?_⟩
  intro n hn G hG
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈((N₂ : ℝ) + 531441) / lam⌉₊ ≤ n := le_trans (le_max_right _ _) hn
  have hnlam : (N₂ : ℝ) + 531441 ≤ lam * n := by
    have h1 : ((N₂ : ℝ) + 531441) / lam ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
    rw [div_le_iff₀ hlam0] at h1
    linarith
  obtain ⟨U₀, hU₀card, U, hUdiv, hUcard⟩ := hdiverse n hn1 G hG
  have hMcard : Fintype.card ↥U₀ = U₀.card := Fintype.card_coe U₀
  have hMnn : (0 : ℝ) ≤ (U₀.card : ℝ) := Nat.cast_nonneg _
  have hMR : (N₂ : ℝ) + 531441 ≤ (U₀.card : ℝ) := le_trans hnlam hU₀card
  have hN₂M : N₂ ≤ Fintype.card ↥U₀ := by
    rw [hMcard]
    have h : (N₂ : ℝ) ≤ (U₀.card : ℝ) := by linarith
    exact_mod_cast h
  -- reparametrise by the twelfth root of `|U₀|`
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = (U₀.card : ℝ) ^ ((1 : ℝ) / 12) := ⟨_, rfl⟩
  have hz0 : (0 : ℝ) ≤ z := by rw [hzdef]; exact Real.rpow_nonneg hMnn _
  have hz12 : z ^ 12 = (U₀.card : ℝ) := by
    rw [hzdef, pow_rpow_one_div hMnn 12]
    norm_num
  have hz8 : z ^ 8 = (U₀.card : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hzdef, pow_rpow_one_div hMnn 8]
    norm_num
  have hz3 : z ^ 3 = (U₀.card : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hzdef, pow_rpow_one_div hMnn 3]
    norm_num
  have hz3ge : (3 : ℝ) ≤ z := by
    rw [hzdef]
    refine le_rpow_one_div_of_pow_le (m := 12) (by norm_num) (by norm_num) (by norm_num) ?_
    have hN₂nn : (0 : ℝ) ≤ (N₂ : ℝ) := Nat.cast_nonneg _
    have hMR' : (531441 : ℝ) ≤ (U₀.card : ℝ) := by linarith only [hMR, hN₂nn]
    exact le_trans (by norm_num) hMR'
  -- `|U|` is large enough for Theorem 2
  have hUsize : (Fintype.card ↥U₀ : ℝ) ^ ((2 : ℝ) / 3) ≤ (U.card : ℝ) := by
    rw [hMcard]
    refine le_trans ?_ hUcard
    have hden : (0 : ℝ) < 1 + 2 * z ^ 3 := by linarith only [pow_nonneg hz0 3]
    rw [← hz8, ← hz3, ← hz12, le_div_iff₀ hden]
    have h1 : (0 : ℝ) ≤ z ^ 8 := pow_nonneg hz0 8
    have hw0 : (0 : ℝ) ≤ z - 3 := by linarith only [hz3ge]
    have h3 : (0 : ℝ) ≤ z ^ 4 - 2 * z ^ 3 - 1 := by
      linarith only [hw0, pow_nonneg hw0 2, pow_nonneg hw0 3, pow_nonneg hw0 4]
    linarith only [mul_nonneg h1 h3]
  obtain ⟨W', hW'⟩ :=
    hthm2 (V := ↥U₀) hN₂M (G.induce (↑U₀ : Set (Fin n))) U hUdiv hUsize
  refine ⟨W'.image Subtype.val, ?_⟩
  rw [← Erdos637.numDistinctDegrees_induce_image]
  refine le_trans ?_ hW'
  rw [hMcard]
  have h1 : (lam * n) ^ ((2 : ℝ) / 3) ≤ (U₀.card : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (mul_nonneg hlam0.le (Nat.cast_nonneg n)) hU₀card (by norm_num)
  rw [Real.mul_rpow hlam0.le (Nat.cast_nonneg n)] at h1
  calc c * lam ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)
      = c * (lam ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) := by ring
    _ ≤ c * (U₀.card : ℝ) ^ ((2 : ℝ) / 3) := mul_le_mul_of_nonneg_left h1 hc0.le

/-! ## The frozen root -/

/-- **Erdős problem 637, JKLY strengthening.**  Every graph on `n` vertices with no clique or
independent set of size `(k + 1) log₂ n` has an induced subgraph with at least `β n ^ (2/3)`
distinct degrees.  Since `Erdos88.RamseyFree` is antitone in its constant (`ramseyFree_mono`),
this natural-number form implies the statement for every real `C ≤ k + 1`, and
`jkly_distinct_degrees` records the unrestricted `C > 0` form. -/
theorem jkly_distinct_degrees_nat (k : ℕ) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree ((k : ℝ) + 1) G →
      ∃ W : Finset (Fin n),
        β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W :=
  jkly_distinct_degrees ((k : ℝ) + 1) (by positivity)

end JKLY
