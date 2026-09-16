import Mathlib
import Proof.Defs
import Proof.Model

/-!
# The union-bound claim

For `m ≥ 1` put `rpar m = 4 (⌊√⌊log₂ m⌋⌋ + 1) + 16` (an integer with
`4 √(log₂ m) + 16 ≤ rpar m ≤ 4 √(log₂ m) + 24`).  The large blocks for `m` are the blocks of
size at least `m · 2 ^ rpar m`.  A choice function `f` is *good* when for every `m ∈ [1, n]`, every
`A' ⊆ A` with `|A'| ≤ m` and every set `B'` of at most `m` vertices in large blocks, fewer than
`m · rpar m` edges of `graphOf f` join `A'` to `B'`.

Counting: the number of choice functions realising a prescribed set `E` of `A`-block-vertex
pairs is at most `|Choice n| / ∏_{e ∈ E} bsize(e)` (`card_forced_le`), and a union bound over
`m`, `A'`, `B'` and `E` bounds the number of bad choice functions by
`|Choice n| · ∑_m badBound n m` (`card_bad_le`), where every large block has at least
`max (m · 2 ^ rpar m, √n / 2)` vertices.
-/

open SimpleGraph Finset

namespace Erdos803

/-- The threshold parameter `r = r(m)`. -/
def rpar (m : ℕ) : ℕ := 4 * (Nat.sqrt (Nat.log 2 m) + 1) + 16

/-- Block vertices lying in blocks of size at least `m · 2 ^ rpar m`. -/
def largeB (n m : ℕ) : Finset (BVertex n) :=
  Finset.univ.filter fun b ↦ m * 2 ^ rpar m ≤ bsize n b.1

/-- The edges of `graphOf f` joining `A'` to `B'`, as pairs. -/
def crossEdges {n : ℕ} (f : Choice n) (A' : Finset (Fin n)) (B' : Finset (BVertex n)) :
    Finset (Fin n × BVertex n) :=
  (A' ×ˢ B').filter fun ab ↦ f ab.1 ab.2.1 = ab.2.2

/-- A choice function is good when the union-bound claim holds for it. -/
def Good {n : ℕ} (f : Choice n) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ A' : Finset (Fin n), A'.card ≤ m →
    ∀ B' : Finset (BVertex n), B' ⊆ largeB n m → B'.card ≤ m →
      (crossEdges f A' B').card < m * rpar m

/-- Choice functions realising every pair in `E`: at most `|Choice n| / ∏ bsize`. -/
theorem card_forced_le (n : ℕ) (E : Finset (Fin n × BVertex n)) :
    {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2}.ncard * ∏ e ∈ E, bsize n e.2.1 ≤
      Fintype.card (Choice n) := by
  classical
  set S : Finset (Choice n) := Finset.univ.filter (fun f ↦ ∀ e ∈ E, f e.1 e.2.1 = e.2.2) with hS
  have hset : {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2} = (S : Set (Choice n)) := by
    ext f
    simp [hS]
  rw [hset, Set.ncard_coe_finset]
  by_cases hSe : S = ∅
  · rw [hSe]
    simp
  · obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have hinj : ∀ x ∈ E, ∀ y ∈ E, ((x.1, x.2.1) : Fin n × BlockIdx n) = (y.1, y.2.1) → x = y := by
      intro x hx y hy hxy
      rw [hS, Finset.mem_filter] at hf₀
      obtain ⟨a, p, b⟩ := x
      obtain ⟨a', p', b'⟩ := y
      have h1 := hf₀.2 _ hx
      have h2 := hf₀.2 _ hy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      simp only at h1 h2
      rw [← h1, ← h2]
    set K : Finset (Fin n × BlockIdx n) := E.image (fun e ↦ (e.1, e.2.1)) with hK
    have hprod : ∏ e ∈ E, bsize n e.2.1 = ∏ k ∈ K, bsize n k.2 := by
      rw [hK, Finset.prod_image hinj]
    have hdet : ∀ f₁ ∈ S, ∀ f₂ ∈ S, ∀ a : Fin n, ∀ p : BlockIdx n, (a, p) ∈ K →
        f₁ a p = f₂ a p := by
      intro f₁ h₁ f₂ h₂ a p hap
      rw [hS, Finset.mem_filter] at h₁ h₂
      rw [hK, Finset.mem_image] at hap
      obtain ⟨e, he, hep⟩ := hap
      obtain ⟨a', p', b'⟩ := e
      simp only [Prod.mk.injEq] at hep
      obtain ⟨rfl, rfl⟩ := hep
      rw [h₁.2 _ he, h₂.2 _ he]
    have key : (S ×ˢ (Finset.univ :
        Finset ((k : {x : Fin n × BlockIdx n // x ∈ K}) → Fin (bsize n k.1.2)))).card ≤
          Fintype.card (Choice n) := by
      rw [← Finset.card_univ (α := Choice n)]
      refine Finset.card_le_card_of_injOn
        (fun fg ↦ fun a p ↦ if h : (a, p) ∈ K then fg.2 ⟨(a, p), h⟩ else fg.1 a p)
        (fun _ _ ↦ Finset.mem_univ _) ?_
      rintro ⟨f₁, g₁⟩ hm₁ ⟨f₂, g₂⟩ hm₂ heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hm₁ hm₂
      have hfun : ∀ (a : Fin n) (p : BlockIdx n),
          (if h : (a, p) ∈ K then g₁ ⟨(a, p), h⟩ else f₁ a p) =
            (if h : (a, p) ∈ K then g₂ ⟨(a, p), h⟩ else f₂ a p) :=
        fun a p ↦ congrFun (congrFun heq a) p
      have hg : g₁ = g₂ := by
        funext k
        obtain ⟨⟨a, p⟩, hk⟩ := k
        have hk' := hfun a p
        simpa only [hk, dite_true, reduceDIte] using hk'
      have hf : f₁ = f₂ := by
        funext a p
        by_cases hk : (a, p) ∈ K
        · exact hdet f₁ hm₁.1 f₂ hm₂.1 a p hk
        · have hk' := hfun a p
          simpa only [hk, dite_false, reduceDIte] using hk'
      simp [hf, hg]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_pi] at key
    simp only [Fintype.card_fin] at key
    rw [Finset.prod_coe_sort K (fun k ↦ bsize n k.2)] at key
    rw [hprod]
    exact key

/-- The choice functions realising every pair in `E`. -/
private def forced {n : ℕ} (E : Finset (Fin n × BVertex n)) : Finset (Choice n) :=
  Finset.univ.filter fun f ↦ ∀ e ∈ E, f e.1 e.2.1 = e.2.2

/-- `card_forced_le` in `Finset` form. -/
private theorem card_forced_mul_le {n : ℕ} (E : Finset (Fin n × BVertex n)) :
    (forced E).card * ∏ e ∈ E, bsize n e.2.1 ≤ Fintype.card (Choice n) := by
  have h := card_forced_le n E
  have hcoe : {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2} = (forced E : Set (Choice n)) := by
    ext f
    simp [forced]
  rwa [hcoe, Set.ncard_coe_finset] at h

/-- Each forced edge into a large block costs a factor `min (1 / (m · 2 ^ rpar m)) (2 / √n)`. -/
private theorem card_forced_le_real {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m)
    (E : Finset (Fin n × BVertex n)) (hE : ∀ e ∈ E, e.2 ∈ largeB n m) :
    ((forced E).card : ℝ) ≤ (Fintype.card (Choice n) : ℝ) *
      (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ E.card := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hmR : (0 : ℝ) < (m : ℝ) * 2 ^ rpar m := by positivity
  have hbig : ∀ e ∈ E, m * 2 ^ rpar m ≤ bsize n e.2.1 := by
    intro e he
    have h := hE e he
    rw [largeB, Finset.mem_filter] at h
    exact h.2
  have hbpos : ∀ e ∈ E, 0 < bsize n e.2.1 := by
    intro e he
    have h1 := hbig e he
    have h2 : 0 < m * 2 ^ rpar m := Nat.mul_pos hm (Nat.two_pow_pos _)
    omega
  have hble : ∀ e ∈ E, ((bsize n e.2.1 : ℝ))⁻¹ ≤
      min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) := by
    intro e he
    have hb : (0 : ℝ) < (bsize n e.2.1 : ℝ) := by exact_mod_cast hbpos e he
    rw [← one_div]
    refine le_min (one_div_le_one_div_of_le hmR ?_) ?_
    · have h := hbig e he
      have hcast : ((m * 2 ^ rpar m : ℕ) : ℝ) ≤ ((bsize n e.2.1 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at hcast
      exact hcast
    · rw [le_div_iff₀ hsq, div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]
      have h4 := le_four_mul_bsize_sq hn e.2.1
      have h4R : (n : ℝ) ≤ (2 * (bsize n e.2.1 : ℝ)) ^ 2 := by
        have hcast : ((n : ℕ) : ℝ) ≤ ((4 * bsize n e.2.1 ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
        push_cast at hcast
        nlinarith [hcast]
      calc Real.sqrt n ≤ Real.sqrt ((2 * (bsize n e.2.1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt h4R
        _ = 2 * (bsize n e.2.1 : ℝ) := Real.sqrt_sq (by positivity)
  have hP : (0 : ℝ) < ∏ e ∈ E, (bsize n e.2.1 : ℝ) :=
    Finset.prod_pos fun e he ↦ by exact_mod_cast hbpos e he
  have hkey : ((forced E).card : ℝ) * ∏ e ∈ E, (bsize n e.2.1 : ℝ) ≤
      (Fintype.card (Choice n) : ℝ) := by
    have h := card_forced_mul_le E
    have hcast : (((forced E).card * ∏ e ∈ E, bsize n e.2.1 : ℕ) : ℝ) ≤
        (Fintype.card (Choice n) : ℝ) := by exact_mod_cast h
    push_cast at hcast
    exact hcast
  rw [← le_div_iff₀ hP] at hkey
  refine hkey.trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [← Finset.prod_inv_distrib]
  calc ∏ e ∈ E, ((bsize n e.2.1 : ℝ))⁻¹
      ≤ ∏ _e ∈ E, min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
        Finset.prod_le_prod (fun e _ ↦ by positivity) hble
    _ = (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ E.card := Finset.prod_const _

/-- There are at most `(m + 1) (2 N) ^ m` subsets of a set of size at most `N` with at most
`m` elements. -/
private theorem card_powerset_filter_le {α : Type*} [DecidableEq α] (s : Finset α) (m N : ℕ)
    (hs : s.card ≤ N) (hN : 1 ≤ N) :
    (s.powerset.filter fun t ↦ t.card ≤ m).card ≤ (m + 1) * (2 * N) ^ m := by
  have hsub : s.powerset.filter (fun t ↦ t.card ≤ m) ⊆
      (Finset.range (m + 1)).biUnion fun a ↦ s.powersetCard a := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_biUnion.mpr ⟨t.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨ht.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ a ∈ Finset.range (m + 1), (s.powersetCard a).card
      ≤ ∑ _a ∈ Finset.range (m + 1), (2 * N) ^ m := by
        refine Finset.sum_le_sum fun a ha ↦ ?_
        rw [Finset.card_powersetCard]
        have h1 : s.card.choose a ≤ N.choose a := Nat.choose_le_choose a hs
        have h2 : N.choose a ≤ N ^ a := Nat.choose_le_pow N a
        have h3 : N ^ a ≤ N ^ m :=
          Nat.pow_le_pow_right hN (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
        have h4 : N ^ m ≤ (2 * N) ^ m := Nat.pow_le_pow_left (by omega) m
        omega
    _ = (m + 1) * (2 * N) ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The subsets of `Fin n` with at most `m` elements. -/
private def smallA (n m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter fun A' ↦ A'.card ≤ m

/-- The subsets of `largeB n m` with at most `m` elements. -/
private def smallB (n m : ℕ) : Finset (Finset (BVertex n)) :=
  (largeB n m).powerset.filter fun B' ↦ B'.card ≤ m

/-- There are at most `(m + 1) (2 n) ^ m` sets in `smallA n m`. -/
private theorem card_smallA_le {n m : ℕ} (hn : 1 ≤ n) :
    (smallA n m).card ≤ (m + 1) * (2 * n) ^ m := by
  refine card_powerset_filter_le _ m n ?_ hn
  simp

/-- There are at most `(m + 1) (2 n) ^ m` sets in `smallB n m`. -/
private theorem card_smallB_le {n m : ℕ} (hn : 1 ≤ n) :
    (smallB n m).card ≤ (m + 1) * (2 * n) ^ m := by
  refine card_powerset_filter_le _ m n ?_ hn
  exact (Finset.card_le_univ _).trans (card_bVertex_le n)

/-- The per-`m` term of the union bound. -/
noncomputable def badBound (n m : ℕ) : ℝ :=
  ((m + 1 : ℝ) ^ 2 * (2 * n : ℝ) ^ (2 * m) * ((m ^ 2).choose (m * rpar m) : ℝ)) *
    (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)

/-- The choice functions covered by the union bound with parameter `m`. -/
private def badCoverAt (n m : ℕ) : Finset (Choice n) :=
  (smallA n m).biUnion fun A' ↦ (smallB n m).biUnion fun B' ↦
    ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E

/-- The union bound for a single value of `m`. -/
private theorem card_badCoverAt_le {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m) :
    ((badCoverAt n m).card : ℝ) ≤ (Fintype.card (Choice n) : ℝ) * badBound n m := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set c : ℝ := min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) with hc
  set C : ℝ := (Fintype.card (Choice n) : ℝ) with hC
  set κ : ℝ := ((m ^ 2).choose (m * rpar m) : ℝ) with hκ
  set β : ℝ := ((m : ℝ) + 1) * (2 * n : ℝ) ^ m with hβ
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    refine le_min ?_ ?_ <;> positivity
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
  have hβ0 : (0 : ℝ) ≤ β := by
    rw [hβ]
    positivity
  have hcp0 : (0 : ℝ) ≤ C * c ^ (m * rpar m) := mul_nonneg hC0 (pow_nonneg hc0 _)
  have hEbound : ∀ A' ∈ smallA n m, ∀ B' ∈ smallB n m,
      (((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ)) ≤
        κ * (C * c ^ (m * rpar m)) := by
    intro A' hA' B' hB'
    rw [smallA, Finset.mem_filter] at hA'
    rw [smallB, Finset.mem_filter, Finset.mem_powerset] at hB'
    have hstep : ∀ E ∈ (A' ×ˢ B').powersetCard (m * rpar m),
        ((forced E).card : ℝ) ≤ C * c ^ (m * rpar m) := by
      intro E hEmem
      rw [Finset.mem_powersetCard] at hEmem
      have h := card_forced_le_real hn hm E fun e he ↦
        hB'.1 (Finset.mem_product.mp (hEmem.1 he)).2
      rw [hEmem.2] at h
      exact h
    calc (((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ))
        ≤ ∑ E ∈ (A' ×ˢ B').powersetCard (m * rpar m), ((forced E).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ (A' ×ˢ B').powersetCard (m * rpar m), C * c ^ (m * rpar m) :=
          Finset.sum_le_sum hstep
      _ = (((A' ×ˢ B').powersetCard (m * rpar m)).card : ℝ) * (C * c ^ (m * rpar m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ κ * (C * c ^ (m * rpar m)) := by
          refine mul_le_mul_of_nonneg_right ?_ hcp0
          rw [hκ]
          refine Nat.cast_le.mpr ?_
          rw [Finset.card_powersetCard, Finset.card_product]
          refine Nat.choose_le_choose _ ?_
          calc A'.card * B'.card ≤ m * m := Nat.mul_le_mul hA'.2 hB'.2
            _ = m ^ 2 := (sq m).symm
  have hBbound : ∀ A' ∈ smallA n m,
      ((((smallB n m).biUnion fun B' ↦ ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion
        fun E ↦ forced E).card : ℝ)) ≤ β * (κ * (C * c ^ (m * rpar m))) := by
    intro A' hA'
    calc ((((smallB n m).biUnion fun B' ↦ ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion
          fun E ↦ forced E).card : ℝ))
        ≤ ∑ B' ∈ smallB n m,
            ((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _B' ∈ smallB n m, κ * (C * c ^ (m * rpar m)) :=
          Finset.sum_le_sum (hEbound A' hA')
      _ = ((smallB n m).card : ℝ) * (κ * (C * c ^ (m * rpar m))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ β * (κ * (C * c ^ (m * rpar m))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hκ0 hcp0)
          have h := card_smallB_le (n := n) (m := m) hn1
          have hcast : (((smallB n m).card : ℕ) : ℝ) ≤ (((m + 1) * (2 * n) ^ m : ℕ) : ℝ) := by
            exact_mod_cast h
          rw [hβ]
          push_cast at hcast ⊢
          exact hcast
  have hpow : (2 * (n : ℝ)) ^ (2 * m) = ((2 * (n : ℝ)) ^ m) ^ 2 := by
    rw [show 2 * m = m * 2 from Nat.mul_comm 2 m, pow_mul]
  have hfinal : β * (β * (κ * (C * c ^ (m * rpar m)))) = C * badBound n m := by
    rw [badBound, ← hc, ← hκ, hβ, hpow]
    ring
  rw [badCoverAt, ← hfinal]
  calc (((smallA n m).biUnion fun A' ↦ (smallB n m).biUnion fun B' ↦
        ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ)
      ≤ ∑ A' ∈ smallA n m, (((smallB n m).biUnion fun B' ↦
          ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _A' ∈ smallA n m, β * (κ * (C * c ^ (m * rpar m))) := Finset.sum_le_sum hBbound
    _ = ((smallA n m).card : ℝ) * (β * (κ * (C * c ^ (m * rpar m)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ β * (β * (κ * (C * c ^ (m * rpar m)))) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hβ0 (mul_nonneg hκ0 hcp0))
        have h := card_smallA_le (n := n) (m := m) hn1
        have hcast : (((smallA n m).card : ℕ) : ℝ) ≤ (((m + 1) * (2 * n) ^ m : ℕ) : ℝ) := by
          exact_mod_cast h
        rw [hβ]
        push_cast at hcast ⊢
        exact hcast

/-- Union bound: the number of bad choice functions is at most `|Choice n| · ∑_m badBound n m`. -/
theorem card_bad_le (n : ℕ) (hn : 4 ≤ n) :
    ({f : Choice n | ¬ Good f}.ncard : ℝ) ≤
      (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m := by
  classical
  set Bad : Finset (Choice n) := Finset.univ.filter (fun f ↦ ¬ Good f) with hBad
  have hcoe : {f : Choice n | ¬ Good f} = (Bad : Set (Choice n)) := by
    ext f
    simp [hBad]
  rw [hcoe, Set.ncard_coe_finset]
  have hsub : Bad ⊆ (Finset.Icc 1 n).biUnion fun m ↦ badCoverAt n m := by
    intro f hf
    rw [hBad, Finset.mem_filter] at hf
    by_contra hc
    refine hf.2 ?_
    intro m hm1 hmn A' hA' B' hB'sub hB'card
    by_contra hlt
    obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (Nat.not_lt.mp hlt)
    refine hc (Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmn⟩, ?_⟩)
    rw [badCoverAt]
    refine Finset.mem_biUnion.mpr ⟨A', ?_, Finset.mem_biUnion.mpr ⟨B', ?_,
      Finset.mem_biUnion.mpr ⟨E, ?_, ?_⟩⟩⟩
    · rw [smallA, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA'⟩
    · rw [smallB, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hB'sub, hB'card⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, hEcard⟩
      intro e he
      exact (Finset.mem_filter.mp (hEsub he)).1
    · rw [forced, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun e he ↦ (Finset.mem_filter.mp (hEsub he)).2⟩
  calc (Bad.card : ℝ)
      ≤ (((Finset.Icc 1 n).biUnion fun m ↦ badCoverAt n m).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ m ∈ Finset.Icc 1 n, ((badCoverAt n m).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ m ∈ Finset.Icc 1 n, (Fintype.card (Choice n) : ℝ) * badBound n m := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        exact card_badCoverAt_le hn (Finset.mem_Icc.mp hm).1
    _ = (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m :=
        (Finset.mul_sum _ _ _).symm

end Erdos803
