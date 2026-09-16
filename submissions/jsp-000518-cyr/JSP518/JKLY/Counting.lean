/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import JSP518.External.Erdos637

/-!
# Pure counting lemmas for the Jenssen--Keevash--Lichev--Yepremyan development

This file collects the purely combinatorial counting statements used downstream: a
ground-set version of the fixed-intersection bound, the Erdős--Littlewood--Offord
counting bound for `±1` coefficients, a "window hit" bound for functions on `ℤ` with
uniformly positive increments, a restricted Cauchy--Schwarz bound for distinct degrees,
and two small pair-counting helpers.

No probability appears here.
-/

open scoped symmDiff

namespace JKLY

universe u

variable {V : Type u}

/-! ## Fixed intersections inside a ground set -/

/-- Subsets of a ground set `S` meeting a fixed `D ⊆ S` in exactly `j` points are at most
`(D.card).choose j * 2 ^ (S.card - D.card)` in number. -/
lemma card_fixedIntersection_powerset_le [DecidableEq V] {D S : Finset V} (hDS : D ⊆ S)
    (j : ℕ) :
    ((S.powerset).filter fun T ↦ (T ∩ D).card = j).card ≤
      Nat.choose D.card j * 2 ^ (S.card - D.card) := by
  set src : Finset (Finset V) := (S.powerset).filter fun T ↦ (T ∩ D).card = j with hsrc
  set target : Finset (Finset V × Finset V) := D.powersetCard j ×ˢ (S \ D).powerset with htgt
  have hmap : ∀ T ∈ src, (T ∩ D, T \ D) ∈ target := by
    intro T hT
    rw [hsrc, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTS, hTj⟩ := hT
    rw [htgt, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset]
    refine ⟨⟨Finset.inter_subset_right, hTj⟩, ?_⟩
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨hTS hz.1, hz.2⟩
  have hinj : Set.InjOn (fun T ↦ (T ∩ D, T \ D)) (src : Set (Finset V)) := by
    intro A _ B _ hAB
    have hinter : A ∩ D = B ∩ D := congrArg Prod.fst hAB
    have hsdiff : A \ D = B \ D := congrArg Prod.snd hAB
    calc
      A = A \ D ∪ A ∩ D := (Finset.sdiff_union_inter A D).symm
      _ = B \ D ∪ B ∩ D := by rw [hsdiff, hinter]
      _ = B := Finset.sdiff_union_inter B D
  calc
    src.card ≤ target.card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = Nat.choose D.card j * 2 ^ (S.card - D.card) := by
      rw [htgt]
      simp [Finset.card_sdiff_of_subset hDS]

/-! ## The Erdős--Littlewood--Offord bound for `±1` coefficients -/

/-- Flipping the `Q`-coordinates of `T` turns the signed count `|T ∩ P| - |T ∩ Q|` into the
plain count `|(T ∆ Q) ∩ (P ∪ Q)| - |Q|`. -/
lemma card_symmDiff_inter_union [DecidableEq V] {T P Q : Finset V} (hPQ : Disjoint P Q) :
    ((T ∆ Q) ∩ (P ∪ Q)).card + (T ∩ Q).card = (T ∩ P).card + Q.card := by
  have hset : (T ∆ Q) ∩ (P ∪ Q) = (T ∩ P) ∪ (Q \ T) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_symmDiff, Finset.mem_sdiff]
    have hpq : ¬ (z ∈ P ∧ z ∈ Q) := fun hz ↦ Finset.disjoint_left.mp hPQ hz.1 hz.2
    tauto
  have hdisj : Disjoint (T ∩ P) (Q \ T) :=
    (hPQ.mono_left Finset.inter_subset_right).mono_right Finset.sdiff_subset
  have hQ : (Q \ T).card + (Q ∩ T).card = Q.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter Q T),
      Finset.sdiff_union_inter]
  have hinter : (Q ∩ T).card = (T ∩ Q).card := by rw [Finset.inter_comm]
  rw [hset, Finset.card_union_of_disjoint hdisj]
  omega

/-- Erdős--Littlewood--Offord for `±1` coefficients: inside a ground set `S`, the number of
subsets `T` realising a prescribed value of `|T ∩ P| - |T ∩ Q|` is at most the central
binomial coefficient of `|P ∪ Q|` times `2 ^ (|S| - |P ∪ Q|)`. -/
lemma card_filter_shift_le [DecidableEq V] {P Q S : Finset V} (hPQ : Disjoint P Q)
    (hPS : P ⊆ S) (hQS : Q ⊆ S) (t : ℤ) :
    ((S.powerset).filter fun T ↦ ((T ∩ P).card : ℤ) - ((T ∩ Q).card : ℤ) = t).card ≤
      Nat.choose (P ∪ Q).card ((P ∪ Q).card / 2) * 2 ^ (S.card - (P ∪ Q).card) := by
  have hmap : ∀ T ∈ (S.powerset).filter
      (fun T ↦ ((T ∩ P).card : ℤ) - ((T ∩ Q).card : ℤ) = t),
      T ∆ Q ∈ (S.powerset).filter
        (fun T' ↦ (T' ∩ (P ∪ Q)).card = (t + (Q.card : ℤ)).toNat) := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTS, ht⟩ := hT
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [Finset.mem_symmDiff] at hz
      rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hTS h1
      · exact hQS h1
    · have hcard := card_symmDiff_inter_union (T := T) hPQ
      omega
  calc
    ((S.powerset).filter fun T ↦ ((T ∩ P).card : ℤ) - ((T ∩ Q).card : ℤ) = t).card
        ≤ ((S.powerset).filter fun T' ↦
            (T' ∩ (P ∪ Q)).card = (t + (Q.card : ℤ)).toNat).card :=
          Finset.card_le_card_of_injOn _ hmap ((symmDiff_left_injective Q).injOn)
    _ ≤ Nat.choose (P ∪ Q).card ((t + (Q.card : ℤ)).toNat) *
          2 ^ (S.card - (P ∪ Q).card) :=
          card_fixedIntersection_powerset_le (Finset.union_subset hPS hQS) _
    _ ≤ Nat.choose (P ∪ Q).card ((P ∪ Q).card / 2) * 2 ^ (S.card - (P ∪ Q).card) :=
          Nat.mul_le_mul (Nat.choose_le_middle _ _) le_rfl

/-! ## Windows hit by a function with uniformly positive increments -/

/-- A real function on `ℤ` whose consecutive increments are at least `s` grows at least
linearly. -/
lemma add_mul_le_of_step (f : ℤ → ℝ) {s : ℝ} (hstep : ∀ i : ℤ, f i + s ≤ f (i + 1))
    {i j : ℤ} (hij : i ≤ j) : f i + ((j : ℝ) - (i : ℝ)) * s ≤ f j := by
  induction j, hij using Int.leInduction with
  | base => simp
  | succ n _ ih =>
    have h1 := hstep n
    have h2 : ((n + 1 : ℤ) : ℝ) - (i : ℝ) = ((n : ℝ) - (i : ℝ)) + 1 := by push_cast; ring
    rw [h2, add_mul, one_mul, ← add_assoc]
    linarith

/-- A real function on `ℤ` whose consecutive increments are at least `s > 0` takes values in
a window of length `L` at most `L / s + 1` times. -/
lemma card_filter_mem_Icc_of_step {K : ℕ} (f : ℤ → ℝ) {s : ℝ} (hs : 0 < s)
    (hstep : ∀ i : ℤ, f i + s ≤ f (i + 1)) (a L : ℝ) (hL : 0 ≤ L) :
    (((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
        fun i ↦ a ≤ f i ∧ f i ≤ a + L).card : ℝ) ≤ L / s + 1 := by
  set T : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
    fun i ↦ a ≤ f i ∧ f i ≤ a + L with hTdef
  have hLs : (0 : ℝ) ≤ L / s := div_nonneg hL hs.le
  rcases T.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hmin : T.min' hne ∈ T := T.min'_mem hne
    have hmax : T.max' hne ∈ T := T.max'_mem hne
    have hle : T.min' hne ≤ T.max' hne := T.min'_le _ hmax
    have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨T.min'_le x hx, T.le_max' x hx⟩
    have hcard : (T.card : ℤ) ≤ T.max' hne - T.min' hne + 1 := by
      have hc := Finset.card_le_card hsub
      rw [Int.card_Icc] at hc
      omega
    have hgrow := add_mul_le_of_step f hstep hle
    have hminb : a ≤ f (T.min' hne) := (Finset.mem_filter.mp hmin).2.1
    have hmaxb : f (T.max' hne) ≤ a + L := (Finset.mem_filter.mp hmax).2.2
    have hdiff : ((T.max' hne : ℝ) - (T.min' hne : ℝ)) * s ≤ L := by linarith
    have hdle : ((T.max' hne : ℝ) - (T.min' hne : ℝ)) ≤ L / s := by
      rw [le_div_iff₀ hs]
      exact hdiff
    have hcardR : (T.card : ℝ) ≤ ((T.max' hne : ℝ) - (T.min' hne : ℝ)) + 1 := by
      exact_mod_cast hcard
    linarith

/-! ## Restricted Cauchy--Schwarz for distinct degrees -/

/-- Cauchy--Schwarz on a subset `S ⊆ W`, counting degree values only through the number of
distinct degrees of the whole of `W`. -/
lemma card_sq_le_numDistinctDegrees_mul [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S W : Finset V} (hSW : S ⊆ W) :
    (S.card : ℝ) ^ 2 ≤ (Erdos637.numDistinctDegrees G W : ℝ) *
      (((S ×ˢ S).filter fun q ↦
        Erdos637.degreeInto G q.1 W = Erdos637.degreeInto G q.2 W).card : ℝ) := by
  have hcauchy := Erdos637.card_sq_le_card_image_mul_card_eqPairs S
    (fun v ↦ Erdos637.degreeInto G v W)
  have himg : (S.image fun v ↦ Erdos637.degreeInto G v W).card ≤
      Erdos637.numDistinctDegrees G W := by
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, hSW hv, rfl⟩
  have hnat : S.card ^ 2 ≤ Erdos637.numDistinctDegrees G W *
      ((S ×ˢ S).filter fun q ↦
        Erdos637.degreeInto G q.1 W = Erdos637.degreeInto G q.2 W).card :=
    hcauchy.trans (Nat.mul_le_mul himg le_rfl)
  exact_mod_cast hnat

/-! ## Pair-counting helpers -/

/-- If every `u ∈ S` has at most `b` partners `u' ∈ S`, then at most `S.card * b` ordered
pairs of `S ×ˢ S` are related. -/
lemma card_pairs_le_of_forall_card_le [DecidableEq V] {S : Finset V} (p : V × V → Prop)
    [DecidablePred p] {b : ℕ} (hb : ∀ u ∈ S, (S.filter fun u' ↦ p (u, u')).card ≤ b) :
    ((S ×ˢ S).filter p).card ≤ S.card * b := by
  have hsub : (S ×ˢ S).filter p ⊆
      S.biUnion fun u ↦ (S.filter fun u' ↦ p (u, u')).image fun u' ↦ (u, u') := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine Finset.mem_biUnion.mpr ⟨q.1, h1, ?_⟩
    refine Finset.mem_image.mpr ⟨q.2, Finset.mem_filter.mpr ⟨h2, ?_⟩, ?_⟩
    · simpa using h3
    · simp
  calc
    ((S ×ˢ S).filter p).card ≤
        (S.biUnion fun u ↦ (S.filter fun u' ↦ p (u, u')).image fun u' ↦ (u, u')).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, ((S.filter fun u' ↦ p (u, u')).image fun u' ↦ (u, u')).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, b := Finset.sum_le_sum fun u hu ↦ Finset.card_image_le.trans (hb u hu)
    _ = S.card * b := by rw [Finset.sum_const, smul_eq_mul]

/-- If the values of `g` on `S` are pairwise `1`-separated, then at most `S.card * (2r + 1)`
ordered pairs of distinct points of `S` have `g`-values within `r`. -/
lemma card_close_pairs_le [DecidableEq V] {S : Finset V} (g : V → ℝ)
    (hsep : ∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → 1 ≤ |g u - g u'|) {r : ℝ} (hr : 0 ≤ r) :
    (((S ×ˢ S).filter fun q ↦ q.1 ≠ q.2 ∧ |g q.1 - g q.2| ≤ r).card : ℝ) ≤
      S.card * (2 * r + 1) := by
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith
  have hfloor0 : (0 : ℤ) ≤ ⌊2 * r⌋ := Int.floor_nonneg.mpr h2r
  set b : ℕ := (⌊2 * r⌋ + 1).toNat with hbdef
  have hbZ : (b : ℤ) = ⌊2 * r⌋ + 1 := Int.toNat_of_nonneg (by omega)
  have hbR : (b : ℝ) ≤ 2 * r + 1 := by
    have h1 : ((b : ℤ) : ℝ) = (⌊2 * r⌋ : ℝ) + 1 := by rw [hbZ]; push_cast; ring
    have h2 : (⌊2 * r⌋ : ℝ) ≤ 2 * r := Int.floor_le (2 * r)
    have h3 : ((b : ℤ) : ℝ) = (b : ℝ) := by push_cast; ring
    linarith
  have hpart : ∀ u ∈ S, (S.filter fun u' ↦ u ≠ u' ∧ |g u - g u'| ≤ r).card ≤ b := by
    intro u _
    have hmapsto : ∀ u' ∈ S.filter (fun u' ↦ u ≠ u' ∧ |g u - g u'| ≤ r),
        ⌊g u' - g u + r⌋ ∈ Finset.Icc (0 : ℤ) ⌊2 * r⌋ := by
      intro u' hu'
      rw [Finset.mem_filter] at hu'
      obtain ⟨-, -, habs⟩ := hu'
      rw [abs_le] at habs
      refine Finset.mem_Icc.mpr ⟨Int.le_floor.mpr ?_, Int.floor_le_floor ?_⟩
      · push_cast
        linarith [habs.1, habs.2]
      · linarith [habs.1, habs.2]
    have hinj : Set.InjOn (fun u' ↦ ⌊g u' - g u + r⌋)
        ((S.filter fun u' ↦ u ≠ u' ∧ |g u - g u'| ≤ r) : Set V) := by
      intro x hx y hy hxy
      by_contra hne
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      have hsepxy := hsep x hx.1 y hy.1 hne
      have h1 : (⌊g x - g u + r⌋ : ℝ) ≤ g x - g u + r := Int.floor_le _
      have h2 : g x - g u + r < (⌊g x - g u + r⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h3 : (⌊g y - g u + r⌋ : ℝ) ≤ g y - g u + r := Int.floor_le _
      have h4 : g y - g u + r < (⌊g y - g u + r⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have heq : (⌊g x - g u + r⌋ : ℝ) = (⌊g y - g u + r⌋ : ℝ) := by exact_mod_cast hxy
      have habs : |g x - g y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      linarith
    calc
      (S.filter fun u' ↦ u ≠ u' ∧ |g u - g u'| ≤ r).card ≤
          (Finset.Icc (0 : ℤ) ⌊2 * r⌋).card :=
        Finset.card_le_card_of_injOn _ hmapsto hinj
      _ = b := by rw [Int.card_Icc, hbdef]; omega
  have hmain := card_pairs_le_of_forall_card_le (S := S)
    (fun q : V × V ↦ q.1 ≠ q.2 ∧ |g q.1 - g q.2| ≤ r) (b := b) hpart
  calc
    (((S ×ˢ S).filter fun q ↦ q.1 ≠ q.2 ∧ |g q.1 - g q.2| ≤ r).card : ℝ) ≤
        ((S.card * b : ℕ) : ℝ) := by exact_mod_cast hmain
    _ = (S.card : ℝ) * (b : ℝ) := by push_cast; ring
    _ ≤ (S.card : ℝ) * (2 * r + 1) := mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg _)

end JKLY
