import CameronErdos.Counting.Basic

/-!
# `Lem_IntervalBM`: the choice of `m`, `M` and the set `B`

This file formalises the interval argument on pp. 8–9 of Green, *The Cameron–Erdős
conjecture* (2004), which produces the two "anchor" points `m < M` of `A` and the large
subset `B ⊆ A` of elements that are `32√ε N`-popularly linked to both of them.

Setting: `A ⊆ [1, N]` with `(1/2 − 1/50) N ≤ |A|`, and `ε` small (`ε ≤ 10⁻²⁴`, so that
`ε^{1/8} ≤ 10⁻³`) with `N` large (`ε^{1/8} N ≥ 1000`).  Writing
`D = D(A, 32 √ε N)` for the set of popular differences, the conclusion is that there are
`m, M ∈ A` with `m < M` such that

* (a) both `m` and `M` have at least `|A| − 16 ε^{1/4} N` popular partners (Green's Lemma 9
  property);
* (b) `|A ∩ [1, m]| ≤ 9 ε^{1/8} N` and `|A ∩ [M, N]| ≤ 9 ε^{1/8} N`;
* (c) `B = {a ∈ A : m < a < M, a − m ∈ D, a − M ∈ D}` has `|B| ≥ |A| − 50 ε^{1/8} N`;
* (d) `M − m > N/4`.

The proof splits `[1, N]` into blocks of length `ℓ = ⌊2 ε^{1/8} N⌋`, takes the first and
last blocks containing at least `9 ε^{1/4} N` points of `A`, and picks `m`, `M` in them
using Green's Lemma 9 (`lem9_degreeCount_green`).
-/

open Finset

namespace CameronErdos

section IntervalBM

variable {N : ℕ} {A : Finset ℤ}

/-- If `a ≤ b * b` and `0 ≤ b` then `√a ≤ b`. -/
private lemma sqrt_le_of_le_mul_self {a b : ℝ} (hb : 0 ≤ b) (hab : a ≤ b * b) :
    Real.sqrt a ≤ b := by
  calc Real.sqrt a ≤ Real.sqrt (b * b) := Real.sqrt_le_sqrt hab
    _ = b := Real.sqrt_mul_self hb

/-- **`Lem_IntervalBM`** (Green, pp. 8–9).  Choice of the anchors `m < M` and the set `B`. -/
theorem lem_intervalBM (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (hε0 : ε ≤ 1 / 10 ^ 24)
    (hN : (1000 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ))
    (hAcard : (1 / 2 - 1 / 50 : ℝ) * (N : ℝ) ≤ (#A : ℝ)) :
    ∃ m M : ℤ, m ∈ A ∧ M ∈ A ∧ m < M ∧
      ((#A : ℝ) - 16 * Real.sqrt (Real.sqrt ε) * (N : ℝ)
          ≤ (#{a' ∈ A | m - a' ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ))} : ℝ)) ∧
      ((#A : ℝ) - 16 * Real.sqrt (Real.sqrt ε) * (N : ℝ)
          ≤ (#{a' ∈ A | M - a' ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ))} : ℝ)) ∧
      ((#{a ∈ A | a ≤ m} : ℝ) ≤ 9 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) ∧
      ((#{a ∈ A | M ≤ a} : ℝ) ≤ 9 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) ∧
      ((#A : ℝ) - 50 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)
          ≤ (#{a ∈ A | m < a ∧ a < M ∧
                a - m ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ)) ∧
                a - M ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ))} : ℝ)) ∧
      ((N : ℝ) / 4 < (M : ℝ) - (m : ℝ)) := by
  classical
  ---------------------------------------------------------------------------
  -- 0.  Numerical preliminaries: `x = ε^{1/8} ≤ 10⁻³` and `x N ≥ 1000`.
  ---------------------------------------------------------------------------
  set x : ℝ := Real.sqrt (Real.sqrt (Real.sqrt ε)) with hxdef
  have hx2 : x * x = Real.sqrt (Real.sqrt ε) := by
    rw [hxdef]; exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hxpos : 0 < x := by
    rw [hxdef]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hε))
  have hxle : x ≤ 1 / 1000 := by
    have h1 : Real.sqrt ε ≤ 1 / 10 ^ 12 :=
      sqrt_le_of_le_mul_self (by norm_num) (by linarith [hε0])
    have h2 : Real.sqrt (Real.sqrt ε) ≤ 1 / 10 ^ 6 :=
      sqrt_le_of_le_mul_self (by norm_num) (by norm_num at h1 ⊢; linarith)
    rw [hxdef]
    exact sqrt_le_of_le_mul_self (by norm_num) (by norm_num at h2 ⊢; linarith)
  have hxN : (1000 : ℝ) ≤ x * (N : ℝ) := hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [hxpos, hc, hxN]
  have hNpos' : 0 < N := by exact_mod_cast hNpos
  have hxNpos : (0 : ℝ) < x * (N : ℝ) := mul_pos hxpos hNpos
  have hxNsmall : x * (N : ℝ) ≤ (1 / 1000) * (N : ℝ) := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1000 - x) hNpos.le
    linarith only [h]
  have hxx : (x * x) * (N : ℝ) ≤ (1 / 1000) * (x * (N : ℝ)) := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 1000 - x) hxNpos.le
    linarith only [h]
  ---------------------------------------------------------------------------
  -- 1.  The blocks.
  ---------------------------------------------------------------------------
  set ℓ : ℕ := ⌊2 * x * (N : ℝ)⌋₊ with hldef
  have hlle : (ℓ : ℝ) ≤ 2 * x * (N : ℝ) := Nat.floor_le (by positivity)
  have hlgt : 2 * x * (N : ℝ) - 1 < (ℓ : ℝ) := by
    have := Nat.lt_floor_add_one (2 * x * (N : ℝ))
    rw [← hldef] at this
    linarith
  have hlbig : (1999 / 1000 : ℝ) * (x * (N : ℝ)) ≤ (ℓ : ℝ) := by linarith only [hlgt, hxN]
  have hlposR : (0 : ℝ) < (ℓ : ℝ) := by linarith only [hlgt, hxN]
  have hlpos : 0 < ℓ := by exact_mod_cast hlposR
  set n : ℕ := N / ℓ + 1 with hndef
  have hnl : (n : ℝ) * (ℓ : ℝ) ≤ (N : ℝ) + (ℓ : ℝ) := by
    have hnat : n * ℓ ≤ N + ℓ := by
      calc n * ℓ = N / ℓ * ℓ + ℓ := by rw [hndef]; ring
        _ ≤ N + ℓ := Nat.add_le_add_right (Nat.div_mul_le_self N ℓ) ℓ
    exact_mod_cast hnat
  set idx : ℤ → ℕ := fun a => (a - 1).toNat / ℓ with hidxdef
  set block : ℕ → Finset ℤ := fun i => {a ∈ A | idx a = i} with hblockdef
  have hblock_sub : ∀ i, block i ⊆ A := fun i => Finset.filter_subset _ _
  have hidx_lt : ∀ a ∈ A, idx a ∈ Finset.range n := by
    intro a ha
    have h := Finset.mem_Icc.1 (hA ha)
    have h1 : (a - 1).toNat ≤ N := by omega
    have : (a - 1).toNat / ℓ ≤ N / ℓ := Nat.div_le_div_right h1
    simp only [Finset.mem_range, hidxdef, hndef]
    omega
  have hidx_mono : ∀ a a' : ℤ, a ≤ a' → idx a ≤ idx a' := by
    intro a a' h
    exact Nat.div_le_div_right (by omega)
  have hAsum : #A = ∑ i ∈ Finset.range n, #(block i) :=
    Finset.card_eq_sum_card_fiberwise hidx_lt
  have hblock_le : ∀ i, #(block i) ≤ ℓ := by
    intro i
    have hcard : #(block i) ≤ #(Finset.range ℓ) := by
      refine Finset.card_le_card_of_injOn (fun a => (a - 1).toNat % ℓ) ?_ ?_
      · intro a _
        exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hlpos))
      · intro a ha a' ha' hmod
        simp only [Finset.mem_coe, hblockdef, Finset.mem_filter] at ha ha'
        have hda : (a - 1).toNat / ℓ = i := ha.2
        have hda' : (a' - 1).toNat / ℓ = i := ha'.2
        have h1 := Finset.mem_Icc.1 (hA ha.1)
        have h2 := Finset.mem_Icc.1 (hA ha'.1)
        have e1 := Nat.div_add_mod (a - 1).toNat ℓ
        have e2 := Nat.div_add_mod (a' - 1).toNat ℓ
        rw [hda] at e1
        rw [hda'] at e2
        simp only at hmod
        have hpp : (a - 1).toNat = (a' - 1).toNat := by rw [← e1, ← e2, hmod]
        omega
    simpa using hcard
  -- the "large" blocks
  set C : ℝ := 9 * (x * x) * (N : ℝ) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set big : Finset ℕ := (Finset.range n).filter (fun i => C ≤ (#(block i) : ℝ)) with hbigdef
  have hbig_sub : big ⊆ Finset.range n := Finset.filter_subset _ _
  ---------------------------------------------------------------------------
  -- 2.  The key numeric estimate `n · C ≤ 5 x N`.
  ---------------------------------------------------------------------------
  have hnC : (n : ℝ) * C ≤ 5 * x * (N : ℝ) := by
    have hyPos : (0 : ℝ) < x * (N : ℝ) := hxNpos
    have hc1 : (4991 / 1000 : ℝ) ≤ 5 - 9 * x := by linarith
    have hc2 : (1999 / 1000 : ℝ) * (x * (N : ℝ)) ≤ (ℓ : ℝ) := hlbig
    have hprod : (4991 / 1000 : ℝ) * ((1999 / 1000) * (x * (N : ℝ)))
        ≤ (5 - 9 * x) * (ℓ : ℝ) :=
      mul_le_mul hc1 hc2 (by positivity) (by linarith)
    have hgoal : 9 * (x * (N : ℝ)) ≤ (5 - 9 * x) * (ℓ : ℝ) := by
      linarith only [hprod, hyPos]
    have h4 : 9 * (x * (N : ℝ)) * (x * (N : ℝ))
        ≤ ((5 - 9 * x) * (ℓ : ℝ)) * (x * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hgoal hyPos.le
    have h2 : ((n : ℝ) * (ℓ : ℝ)) * C ≤ ((N : ℝ) + (ℓ : ℝ)) * C :=
      mul_le_mul_of_nonneg_right hnl hCpos.le
    have h3 : ((N : ℝ) + (ℓ : ℝ)) * C ≤ (5 * x * (N : ℝ)) * (ℓ : ℝ) := by
      rw [hCdef]; linarith only [h4]
    have hfinal : ((n : ℝ) * C) * (ℓ : ℝ) ≤ (5 * x * (N : ℝ)) * (ℓ : ℝ) := by
      calc ((n : ℝ) * C) * (ℓ : ℝ) = ((n : ℝ) * (ℓ : ℝ)) * C := by ring
        _ ≤ ((N : ℝ) + (ℓ : ℝ)) * C := h2
        _ ≤ (5 * x * (N : ℝ)) * (ℓ : ℝ) := h3
    exact le_of_mul_le_mul_right hfinal hlposR
  have hsmall_sum : ∀ S : Finset ℕ, S ⊆ Finset.range n → (∀ i ∈ S, i ∉ big) →
      (∑ i ∈ S, (#(block i) : ℝ)) ≤ 5 * x * (N : ℝ) := by
    intro S hS hnb
    have hterm : ∀ i ∈ S, (#(block i) : ℝ) ≤ C := by
      intro i hi
      by_contra hc
      exact hnb i hi (Finset.mem_filter.2 ⟨hS hi, (not_le.1 hc).le⟩)
    have hScard : (#S : ℝ) ≤ (n : ℝ) := by
      have := Finset.card_le_card hS
      rw [Finset.card_range] at this
      exact_mod_cast this
    calc (∑ i ∈ S, (#(block i) : ℝ)) ≤ ∑ _i ∈ S, C := Finset.sum_le_sum hterm
      _ = (#S : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_right hScard hCpos.le
      _ ≤ 5 * x * (N : ℝ) := hnC
  have hAsumR : (#A : ℝ) = ∑ i ∈ Finset.range n, (#(block i) : ℝ) := by
    rw [hAsum]; push_cast; ring
  ---------------------------------------------------------------------------
  -- 3.  There are at least two large blocks.
  ---------------------------------------------------------------------------
  have hbigNe : big.Nonempty := by
    rcases Finset.eq_empty_or_nonempty big with hb | hb
    · exfalso
      have := hsmall_sum (Finset.range n) (le_refl _) (by intro i _; rw [hb]; simp)
      rw [← hAsumR] at this
      linarith only [this, hAcard, hxNsmall, hNpos]
    · exact hb
  set j : ℕ := big.min' hbigNe with hjdef
  set k : ℕ := big.max' hbigNe with hkdef
  have hjbig : j ∈ big := Finset.min'_mem _ _
  have hkbig : k ∈ big := Finset.max'_mem _ _
  have hjn : j ∈ Finset.range n := hbig_sub hjbig
  have hkn : k ∈ Finset.range n := hbig_sub hkbig
  have hjC : C ≤ (#(block j) : ℝ) := (Finset.mem_filter.1 hjbig).2
  have hkC : C ≤ (#(block k) : ℝ) := (Finset.mem_filter.1 hkbig).2
  have hjk : j < k := by
    rcases lt_or_eq_of_le (Finset.min'_le_max' big hbigNe) with h | h
    · exact h
    · exfalso
      -- if `j = k` then `big = {j}` and `A` is contained in one block plus small blocks
      have hbig_eq : ∀ i ∈ big, i = j := by
        intro i hi
        have h1 : j ≤ i := Finset.min'_le _ _ hi
        have h2 : i ≤ k := Finset.le_max' _ _ hi
        omega
      have hsplit : (#(block j) : ℝ) + ∑ i ∈ (Finset.range n).erase j, (#(block i) : ℝ)
          = ∑ i ∈ Finset.range n, (#(block i) : ℝ) :=
        Finset.add_sum_erase _ (fun i => (#(block i) : ℝ)) hjn
      have hrest : ∑ i ∈ (Finset.range n).erase j, (#(block i) : ℝ) ≤ 5 * x * (N : ℝ) := by
        refine hsmall_sum _ (Finset.erase_subset _ _) ?_
        intro i hi hib
        exact (Finset.ne_of_mem_erase hi) (hbig_eq i hib)
      have hbj : (#(block j) : ℝ) ≤ (ℓ : ℝ) := by
        have := hblock_le j; exact_mod_cast this
      rw [← hAsumR] at hsplit
      linarith only [hsplit, hrest, hbj, hlle, hAcard, hxNsmall, hNpos]
  ---------------------------------------------------------------------------
  -- 4.  Green's Lemma 9 supplies good anchors inside the blocks.
  ---------------------------------------------------------------------------
  set D : Finset ℤ := popularDiff A (32 * Real.sqrt ε * (N : ℝ)) with hDdef
  have hlem9 : (#{a ∈ A | (#{a' ∈ A | a - a' ∈ D} : ℝ) < (#A : ℝ) - 16 * (x * x) * (N : ℝ)} : ℝ)
      ≤ 8 * (x * x) * (N : ℝ) := by
    rw [hx2, hDdef]
    exact lem9_degreeCount_green hA hε
  set Bad : Finset ℤ :=
    {a ∈ A | (#{a' ∈ A | a - a' ∈ D} : ℝ) < (#A : ℝ) - 16 * (x * x) * (N : ℝ)} with hBaddef
  have hgood : ∀ i ∈ big, ∃ a ∈ block i,
      (#A : ℝ) - 16 * (x * x) * (N : ℝ) ≤ (#{a' ∈ A | a - a' ∈ D} : ℝ) := by
    intro i hi
    have hiC : C ≤ (#(block i) : ℝ) := (Finset.mem_filter.1 hi).2
    have hxxN : (0 : ℝ) < x * x * (N : ℝ) := by positivity
    have hlt : (#Bad : ℝ) < (#(block i) : ℝ) := by
      rw [hCdef] at hiC
      linarith only [hiC, hlem9, hxxN]
    have hnotsub : ¬ block i ⊆ Bad := by
      intro hsub
      have h1 := Finset.card_le_card hsub
      have h2 : (#(block i) : ℝ) ≤ (#Bad : ℝ) := by exact_mod_cast h1
      linarith only [h2, hlt]
    obtain ⟨a, haB, hanot⟩ := Finset.not_subset.1 hnotsub
    refine ⟨a, haB, ?_⟩
    have haA : a ∈ A := hblock_sub i haB
    by_contra hc
    exact hanot (Finset.mem_filter.2 ⟨haA, not_le.1 hc⟩)
  obtain ⟨m, hmblock, hmgood⟩ := hgood j hjbig
  obtain ⟨M, hMblock, hMgood⟩ := hgood k hkbig
  have hmA : m ∈ A := hblock_sub j hmblock
  have hMA : M ∈ A := hblock_sub k hMblock
  have hmidx : idx m = j := (Finset.mem_filter.1 hmblock).2
  have hMidx : idx M = k := (Finset.mem_filter.1 hMblock).2
  have hmM : m < M := by
    by_contra hc
    have : idx M ≤ idx m := hidx_mono M m (not_lt.1 hc)
    omega
  ---------------------------------------------------------------------------
  -- 5.  Few elements of `A` lie below `m` or above `M`.
  ---------------------------------------------------------------------------
  have hcard_le_sum : ∀ (A' : Finset ℤ) (S : Finset ℕ), A' ⊆ A → (∀ a ∈ A', idx a ∈ S) →
      #A' ≤ ∑ i ∈ S, #(block i) := by
    intro A' S hsub hmaps
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_le_sum fun i _ => Finset.card_le_card ?_
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_filter.2 ⟨hsub ha.1, ha.2⟩
  have hblR : ∀ i, (#(block i) : ℝ) ≤ (ℓ : ℝ) := by
    intro i; have := hblock_le i; exact_mod_cast this
  have hlowM : (#{a ∈ A | a ≤ m} : ℝ) ≤ 9 * x * (N : ℝ) := by
    have hmaps : ∀ a ∈ {a ∈ A | a ≤ m}, idx a ∈ Finset.range (j + 1) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have := hidx_mono a m ha.2
      rw [hmidx] at this
      exact Finset.mem_range.2 (by omega)
    have hle := hcard_le_sum _ _ (Finset.filter_subset _ _) hmaps
    have hleR : (#{a ∈ A | a ≤ m} : ℝ) ≤ ∑ i ∈ Finset.range (j + 1), (#(block i) : ℝ) := by
      have : ((∑ i ∈ Finset.range (j + 1), #(block i) : ℕ) : ℝ)
          = ∑ i ∈ Finset.range (j + 1), (#(block i) : ℝ) := by push_cast; ring
      rw [← this]; exact_mod_cast hle
    have hsplit : ∑ i ∈ Finset.range (j + 1), (#(block i) : ℝ)
        = ∑ i ∈ Finset.range j, (#(block i) : ℝ) + (#(block j) : ℝ) := Finset.sum_range_succ _ _
    have hpre : ∑ i ∈ Finset.range j, (#(block i) : ℝ) ≤ 5 * x * (N : ℝ) := by
      refine hsmall_sum _ ?_ ?_
      · intro i hi
        rw [Finset.mem_range] at hi ⊢
        rw [Finset.mem_range] at hjn
        omega
      · intro i hi hib
        have := Finset.min'_le big i hib
        rw [Finset.mem_range] at hi
        omega
    have hbj := hblR j
    linarith only [hleR, hsplit, hpre, hbj, hlle, hxNpos]
  have hhighM : (#{a ∈ A | M ≤ a} : ℝ) ≤ 9 * x * (N : ℝ) := by
    set S : Finset ℕ := (Finset.range n).filter (fun i => k ≤ i) with hSdef
    have hmaps : ∀ a ∈ {a ∈ A | M ≤ a}, idx a ∈ S := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have h1 := hidx_mono M a ha.2
      rw [hMidx] at h1
      exact Finset.mem_filter.2 ⟨hidx_lt a ha.1, h1⟩
    have hle := hcard_le_sum _ _ (Finset.filter_subset _ _) hmaps
    have hleR : (#{a ∈ A | M ≤ a} : ℝ) ≤ ∑ i ∈ S, (#(block i) : ℝ) := by
      have : ((∑ i ∈ S, #(block i) : ℕ) : ℝ) = ∑ i ∈ S, (#(block i) : ℝ) := by push_cast; ring
      rw [← this]; exact_mod_cast hle
    have hkS : k ∈ S := Finset.mem_filter.2 ⟨hkn, le_refl _⟩
    have hsplit : (#(block k) : ℝ) + ∑ i ∈ S.erase k, (#(block i) : ℝ)
        = ∑ i ∈ S, (#(block i) : ℝ) :=
      Finset.add_sum_erase _ (fun i => (#(block i) : ℝ)) hkS
    have hpost : ∑ i ∈ S.erase k, (#(block i) : ℝ) ≤ 5 * x * (N : ℝ) := by
      refine hsmall_sum _ (le_trans (Finset.erase_subset _ _) (Finset.filter_subset _ _)) ?_
      intro i hi hib
      have hne : i ≠ k := Finset.ne_of_mem_erase hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hki : k ≤ i := (Finset.mem_filter.1 hiS).2
      have := Finset.le_max' big i hib
      omega
    have hbk := hblR k
    linarith only [hleR, hsplit, hpost, hbk, hlle, hxNpos]
  ---------------------------------------------------------------------------
  -- 6.  The set `B`.
  ---------------------------------------------------------------------------
  set B : Finset ℤ := {a ∈ A | m < a ∧ a < M ∧ a - m ∈ D ∧ a - M ∈ D} with hBdef
  have hBsub : B ⊆ A := Finset.filter_subset _ _
  have hnbd : ∀ c ∈ A, (#{a ∈ A | a - c ∉ D} : ℝ) ≤ (#A : ℝ) -
      (#{a' ∈ A | c - a' ∈ D} : ℝ) := by
    intro c _
    have heq : {a ∈ A | a - c ∉ D} = {a ∈ A | c - a ∉ D} := by
      ext a
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      constructor
      · intro h hc
        exact h (by rw [hDdef] at hc ⊢; rw [← neg_sub]; exact popularDiff_neg.1 hc)
      · intro h hc
        exact h (by rw [hDdef] at hc ⊢; rw [← neg_sub]; exact popularDiff_neg.1 hc)
    rw [heq]
    have := Finset.card_filter_add_card_filter_not (s := A) (p := fun a => c - a ∈ D)
    have hR : (#{a ∈ A | c - a ∈ D} : ℝ) + (#{a ∈ A | c - a ∉ D} : ℝ) = (#A : ℝ) := by
      exact_mod_cast this
    linarith
  have hBcard : (#A : ℝ) - 50 * x * (N : ℝ) ≤ (#B : ℝ) := by
    have hsubU : A \ B ⊆ ({a ∈ A | a ≤ m} ∪ {a ∈ A | M ≤ a}) ∪
        ({a ∈ A | a - m ∉ D} ∪ {a ∈ A | a - M ∉ D}) := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have haA := ha.1
      have hnb : ¬ (m < a ∧ a < M ∧ a - m ∈ D ∧ a - M ∈ D) := by
        intro h
        exact ha.2 (Finset.mem_filter.2 ⟨haA, h⟩)
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases h1 : a ≤ m
      · exact Or.inl (Or.inl ⟨haA, h1⟩)
      · by_cases h2 : M ≤ a
        · exact Or.inl (Or.inr ⟨haA, h2⟩)
        · by_cases h3 : a - m ∈ D
          · refine Or.inr (Or.inr ⟨haA, ?_⟩)
            intro h4
            exact hnb ⟨by omega, by omega, h3, h4⟩
          · exact Or.inr (Or.inl ⟨haA, h3⟩)
    have hcardU : #(A \ B) ≤ (#{a ∈ A | a ≤ m} + #{a ∈ A | M ≤ a}) +
        (#{a ∈ A | a - m ∉ D} + #{a ∈ A | a - M ∉ D}) := by
      refine le_trans (Finset.card_le_card hsubU) ?_
      refine le_trans (Finset.card_union_le _ _) ?_
      exact Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
    have hcardUR : (#(A \ B) : ℝ) ≤ ((#{a ∈ A | a ≤ m} : ℝ) + (#{a ∈ A | M ≤ a} : ℝ)) +
        ((#{a ∈ A | a - m ∉ D} : ℝ) + (#{a ∈ A | a - M ∉ D} : ℝ)) := by
      exact_mod_cast hcardU
    have hsdiff : (#(A \ B) : ℝ) = (#A : ℝ) - (#B : ℝ) := by
      have h := Finset.card_sdiff_add_card_eq_card hBsub
      have h2 : (#(A \ B) : ℝ) + (#B : ℝ) = (#A : ℝ) := by exact_mod_cast h
      linarith only [h2]
    have hm3 := hnbd m hmA
    have hM3 := hnbd M hMA
    rw [hsdiff] at hcardUR
    linarith only [hcardUR, hlowM, hhighM, hm3, hM3, hmgood, hMgood, hxx, hxNpos]
  ---------------------------------------------------------------------------
  -- 7.  `B` lies in `(m, M)`, which forces `M - m > N/4`.
  ---------------------------------------------------------------------------
  have hBIoo : B ⊆ Finset.Ioo m M := by
    intro a ha
    rw [hBdef, Finset.mem_filter] at ha
    exact Finset.mem_Ioo.2 ⟨ha.2.1, ha.2.2.1⟩
  have hBlen : (#B : ℤ) ≤ M - m - 1 := by
    have h1 : #B ≤ #(Finset.Ioo m M) := Finset.card_le_card hBIoo
    rw [Int.card_Ioo] at h1
    omega
  have hBlenR : (#B : ℝ) ≤ (M : ℝ) - (m : ℝ) - 1 := by
    have : ((#B : ℤ) : ℝ) ≤ ((M - m - 1 : ℤ) : ℝ) := by exact_mod_cast hBlen
    push_cast at this
    linarith
  have hd : (N : ℝ) / 4 < (M : ℝ) - (m : ℝ) := by
    have h50 : 50 * x * (N : ℝ) ≤ (1 / 20) * (N : ℝ) := by linarith only [hxNsmall]
    linarith only [hBlenR, hBcard, hAcard, h50, hNpos]
  ---------------------------------------------------------------------------
  -- 8.  Assemble.
  ---------------------------------------------------------------------------
  refine ⟨m, M, hmA, hMA, hmM, ?_, ?_, ?_, ?_, ?_, hd⟩
  · rw [← hx2]; exact hmgood
  · rw [← hx2]; exact hMgood
  · exact hlowM
  · exact hhighM
  · exact hBcard

end IntervalBM

/-! ## Axiom audit -/

#print axioms CameronErdos.lem_intervalBM

end CameronErdos
