import CameronErdos.Part1.Prop3
import CameronErdos.Counting.Basic

/-!
# Green's Proposition 4

This file formalizes Proposition 4 of Green, *The Cameron–Erdős conjecture* (2004)
(see `ref/green-cameron-erdos-0304058.pdf`, pp. 5–6):

> If `A ⊆ ZMod p` is sum-free and `d` is a good length for `A`, then the granularization
> `A' = ⋃_{i ∈ T} I i` has at most `ε p²` additive triples.
-/

namespace CameronErdos

open Finset

/-! ### The left endpoints `⌊n p / M⌋` of the blocks -/

/-- The left endpoint of the `n`-th block, `⌊n p / M⌋`, defined for every `n : ℕ`
(not only for `n < M`). -/
def bst (p M n : ℕ) : ℕ := n * p / M

lemma bst_mono (p M : ℕ) : Monotone (bst p M) := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul_right p h)

lemma bst_zero (p M : ℕ) : bst p M 0 = 0 := by simp [bst]

lemma bst_M {p M : ℕ} (hM : 0 < M) : bst p M M = p := by
  rw [bst, Nat.mul_div_cancel_left _ hM]

lemma bst_le_p {p M n : ℕ} (hM : 0 < M) (hn : n ≤ M) : bst p M n ≤ p :=
  (bst_mono p M hn).trans (le_of_eq (bst_M hM))

/-- `⌊mp/M⌋ + ⌊np/M⌋ ≤ ⌊(m+n)p/M⌋`. -/
lemma bst_add_le (p M m n : ℕ) : bst p M m + bst p M n ≤ bst p M (m + n) := by
  have h : m * p + n * p = (m + n) * p := by ring
  calc bst p M m + bst p M n = m * p / M + n * p / M := rfl
    _ ≤ (m * p + n * p) / M := Nat.div_add_div_le_add_div
    _ = bst p M (m + n) := by rw [bst, h]

/-- `⌊(m+n)p/M⌋ ≤ ⌊mp/M⌋ + ⌊np/M⌋ + 1`. -/
lemma bst_add_le_add_one {M : ℕ} (hM : 0 < M) (p m n : ℕ) :
    bst p M (m + n) ≤ bst p M m + bst p M n + 1 := by
  have h1 : m * p < (m * p / M + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  have h2 : n * p < (n * p / M + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  have key : (m + n) * p < (m * p / M + n * p / M + 1 + 1) * M := by
    have h : (m + n) * p = m * p + n * p := by ring
    rw [h]
    calc m * p + n * p < (m * p / M + 1) * M + (n * p / M + 1) * M := by omega
      _ = (m * p / M + n * p / M + 1 + 1) * M := by ring
  simp only [bst]
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hM).mpr key)

/-- `⌊(n+M)p/M⌋ = ⌊np/M⌋ + p`. -/
lemma bst_add_M {M : ℕ} (hM : 0 < M) (p n : ℕ) : bst p M (n + M) = bst p M n + p := by
  have h : (n + M) * p = n * p + p * M := by ring
  rw [bst, bst, h, Nat.add_mul_div_right _ _ hM]

variable {p : ℕ} [NeZero p]

lemma mem_baseBlock' {M i : ℕ} {lam : ZMod p} :
    lam ∈ baseBlock p M i ↔ bst p M i ≤ lam.val ∧ lam.val < bst p M (i + 1) :=
  mem_baseBlock

/-! ### Block lengths -/

lemma card_baseBlock' {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    (baseBlock p M i).card = bst p M (i + 1) - bst p M i :=
  card_baseBlock hM hi

lemma len_le_L {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    bst p M (i + 1) - bst p M i ≤ L p M := by
  have h := block_card_le (p := p) (d := (1 : ZMod p)) isUnit_one hM hi
  rwa [card_block isUnit_one, card_baseBlock' hM hi] at h

lemma L_sub_one_le_len {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    L p M - 1 ≤ bst p M (i + 1) - bst p M i := by
  have h := block_card_ge (p := p) (d := (1 : ZMod p)) isUnit_one hM hi
  rwa [card_block isUnit_one, card_baseBlock' hM hi] at h

omit [NeZero p] in
lemma p_le_M_mul_L {M : ℕ} (hM : 0 < M) : p ≤ M * L p M := by
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h : (p : ℝ) / (M : ℝ) ≤ (L p M : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hM'] at h
  have : (p : ℝ) ≤ ((M * L p M : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

lemma M_mul_L_sub_one_lt {M : ℕ} (hM : 0 < M) : M * (L p M - 1) < p := by
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hL : 0 < L p M := L_pos (p := p) hM
  have h : (L p M : ℝ) - 1 < (p : ℝ) / (M : ℝ) := by
    have := Nat.ceil_lt_add_one (a := (p : ℝ) / (M : ℝ)) (by positivity)
    rw [L]; linarith
  rw [lt_div_iff₀ hM'] at h
  have hcast : ((L p M - 1 : ℕ) : ℝ) = (L p M : ℝ) - 1 := by
    have : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  have h2 : ((M * (L p M - 1) : ℕ) : ℝ) < (p : ℝ) := by push_cast [hcast]; linarith
  exact_mod_cast h2


/-! ### The core interval count

If `z` lifts to an integer `s` sitting comfortably inside the sumset of the integer intervals
`[⌊ip/M⌋, ⌊(i+1)p/M⌋)` and `[⌊jp/M⌋, ⌊(j+1)p/M⌋)`, then `z` has at least `c` representations
`z = x + y` with `x ∈ I i` and `y ∈ I j`.
-/

lemma card_pairs_ge {d : ZMod p} (hd : IsUnit d) {M i j : ℕ} (hM : 0 < M)
    (hi : i < M) (hj : j < M) {z : ZMod p} {s c : ℕ}
    (hsz : ((s : ℕ) : ZMod p) * d = z)
    (hci : c ≤ bst p M (i + 1) - bst p M i) (hcj : c ≤ bst p M (j + 1) - bst p M j)
    (hleft : bst p M i + bst p M j + c ≤ s + 1)
    (hright : s + c + 1 ≤ bst p M (i + 1) + bst p M (j + 1)) :
    c ≤ #{q ∈ block d M i ×ˢ block d M j | q.1 + q.2 = z} := by
  classical
  have ha : bst p M i ≤ bst p M (i + 1) := bst_mono p M (Nat.le_succ i)
  have he : bst p M j ≤ bst p M (j + 1) := bst_mono p M (Nat.le_succ j)
  have hbp : bst p M (i + 1) ≤ p := bst_le_p hM hi
  have hfp : bst p M (j + 1) ≤ p := bst_le_p hM hj
  set u₀ : ℕ := max (bst p M i) (s + 1 - bst p M (j + 1)) with hu₀
  have hkey : ∀ t ∈ Finset.range c,
      bst p M i ≤ u₀ + t ∧ u₀ + t < bst p M (i + 1) ∧ u₀ + t ≤ s ∧
        bst p M j ≤ s - (u₀ + t) ∧ s - (u₀ + t) < bst p M (j + 1) := by
    intro t ht
    rw [Finset.mem_range] at ht
    omega
  have hcard := Finset.card_range c
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun t => ((((u₀ + t : ℕ) : ZMod p) * d), ((((s - (u₀ + t) : ℕ)) : ZMod p) * d))) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hkey t ht
    have hval1 : (((u₀ + t : ℕ) : ZMod p)).val = u₀ + t :=
      ZMod.val_cast_of_lt (lt_of_lt_of_le h2 hbp)
    have hval2 : (((s - (u₀ + t) : ℕ) : ZMod p)).val = s - (u₀ + t) :=
      ZMod.val_cast_of_lt (lt_of_lt_of_le h5 hfp)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨mem_block.mpr ⟨_, mem_baseBlock'.mpr ⟨by rw [hval1]; exact h1, by rw [hval1]; exact h2⟩,
        rfl⟩, mem_block.mpr ⟨_, mem_baseBlock'.mpr ⟨by rw [hval2]; exact h4,
        by rw [hval2]; exact h5⟩, rfl⟩⟩, ?_⟩
    rw [← add_mul, ← Nat.cast_add, show u₀ + t + (s - (u₀ + t)) = s from by omega, hsz]
  · intro t ht t' ht' hff
    rw [Finset.mem_coe] at ht ht'
    simp only [Prod.mk.injEq] at hff
    obtain ⟨h1, _, h3, _, _⟩ := hkey t ht
    obtain ⟨h1', _, h3', _, _⟩ := hkey t' ht'
    have hb2 : u₀ + t < bst p M (i + 1) := (hkey t ht).2.1
    have hb2' : u₀ + t' < bst p M (i + 1) := (hkey t' ht').2.1
    have := mul_isUnit_injective hd hff.1
    have hval : (((u₀ + t : ℕ) : ZMod p)).val = (((u₀ + t' : ℕ) : ZMod p)).val := by rw [this]
    rw [ZMod.val_cast_of_lt (lt_of_lt_of_le hb2 hbp),
      ZMod.val_cast_of_lt (lt_of_lt_of_le hb2' hbp)] at hval
    omega

/-! ### Which blocks can contain a sum

If `x ∈ I i`, `y ∈ I j`, `z ∈ I k` and `x + y = z`, then `k ≡ i + j` or `k ≡ i + j + 1 (mod M)`,
unless `x` and `y` are the left endpoints of their blocks.
-/

lemma val_add_cases {a b : ZMod p} : a.val + b.val = (a + b).val ∨ a.val + b.val = (a + b).val + p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hva := ZMod.val_lt a
  have hvb := ZMod.val_lt b
  have hsum : (a + b).val = (a.val + b.val) % p := ZMod.val_add a b
  have hdm := Nat.div_add_mod (a.val + b.val) p
  have hq : (a.val + b.val) / p < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]; omega
  interval_cases h : (a.val + b.val) / p <;> omega

lemma block_add_index {d : ZMod p} (hd : IsUnit d) {M i j k : ℕ} (hM : 0 < M) (hk : k < M)
    {x y z : ZMod p} (hx : x ∈ block d M i) (hy : y ∈ block d M j) (hz : z ∈ block d M k)
    (hxyz : x + y = z) :
    k = (i + j) % M ∨ k = (i + j + 1) % M ∨
      (x = ((bst p M i : ℕ) : ZMod p) * d ∧ y = ((bst p M j : ℕ) : ZMod p) * d) := by
  obtain ⟨xi, hxi, rfl⟩ := mem_block.mp hx
  obtain ⟨et, het, rfl⟩ := mem_block.mp hy
  obtain ⟨ze, hze, rfl⟩ := mem_block.mp hz
  rw [mem_baseBlock'] at hxi het hze
  have hsum : xi + et = ze := by
    refine mul_isUnit_injective hd ?_
    simpa [add_mul] using hxyz
  -- the lift `s = xi.val + et.val` of `ze`
  obtain ⟨t, ht, hs⟩ : ∃ t : ℕ, t ≤ 1 ∧ xi.val + et.val = ze.val + t * p := by
    rcases val_add_cases (a := xi) (b := et) with h | h
    · exact ⟨0, by omega, by rw [hsum] at h; omega⟩
    · exact ⟨1, le_rfl, by rw [hsum] at h; omega⟩
  set k' : ℕ := k + t * M with hk'
  have hbk : bst p M k' = bst p M k + t * p := by
    interval_cases t <;> simp [hk', bst_add_M hM]
  have hbk1 : bst p M (k' + 1) = bst p M (k + 1) + t * p := by
    interval_cases t
    · simp [hk']
    · simp only [one_mul, hk']
      rw [show k + M + 1 = (k + 1) + M from by ring, bst_add_M hM]
  have h5 : bst p M (i + j) ≤ bst p M i + bst p M j + 1 := bst_add_le_add_one hM p i j
  have h6 : bst p M (i + 1) + bst p M (j + 1) ≤ bst p M (i + j + 2) := by
    have := bst_add_le p M (i + 1) (j + 1)
    simpa [show i + 1 + (j + 1) = i + j + 2 from by ring] using this
  have hfin : k' = i + j ∨ k' = i + j + 1 ∨ (xi.val = bst p M i ∧ et.val = bst p M j) := by
    by_cases hc1 : i + j + 2 ≤ k'
    · exact absurd (bst_mono p M hc1) (by omega)
    · by_cases hc2 : k' + 1 ≤ i + j
      · have := bst_mono p M hc2
        exact Or.inr (Or.inr (by omega))
      · omega
  rcases hfin with h | h | ⟨h1, h2⟩
  · left
    rw [← h, hk', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  · right; left
    rw [← h, hk', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  · right; right
    refine ⟨?_, ?_⟩
    · congr 1
      rw [← h1, ZMod.natCast_rightInverse xi]
    · congr 1
      rw [← h2, ZMod.natCast_rightInverse et]

/-! ### The middle part of a block -/

/-- The elements of the `k`-th base block at distance at least `m` from both endpoints. -/
def baseMid (p : ℕ) [NeZero p] (M m k : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun lam : ZMod p => bst p M k + m ≤ lam.val ∧ lam.val < bst p M (k + 1) - m

/-- The middle part `I k` with both ends of length `m` removed. -/
def blockMid {p : ℕ} [NeZero p] (d : ZMod p) (M m k : ℕ) : Finset (ZMod p) :=
  (baseMid p M m k).image fun lam => lam * d

lemma mem_baseMid {M m k : ℕ} {lam : ZMod p} :
    lam ∈ baseMid p M m k ↔
      bst p M k + m ≤ lam.val ∧ lam.val < bst p M (k + 1) - m := by
  simp [baseMid]

lemma mem_blockMid {d : ZMod p} {M m k : ℕ} {x : ZMod p} :
    x ∈ blockMid d M m k ↔ ∃ lam ∈ baseMid p M m k, lam * d = x := by
  simp [blockMid]

lemma baseMid_subset {M m k : ℕ} : baseMid p M m k ⊆ baseBlock p M k := by
  intro lam h
  rw [mem_baseMid] at h
  rw [mem_baseBlock']
  omega

lemma blockMid_subset_block {d : ZMod p} {M m k : ℕ} : blockMid d M m k ⊆ block d M k :=
  Finset.image_subset_image baseMid_subset

lemma card_baseMid {M m k : ℕ} (hM : 0 < M) (hk : k < M) :
    (baseMid p M m k).card = (bst p M (k + 1) - m) - (bst p M k + m) := by
  have hb : bst p M (k + 1) - m ≤ p := le_trans (Nat.sub_le _ _) (bst_le_p hM hk)
  exact card_filter_val_Ico hb

lemma card_block_le_card_blockMid_add {d : ZMod p} (hd : IsUnit d) {M m k : ℕ}
    (hM : 0 < M) (hk : k < M) :
    (block d M k).card ≤ (blockMid d M m k).card + 2 * m := by
  have h1 : (block d M k).card = bst p M (k + 1) - bst p M k := by
    rw [card_block hd, card_baseBlock' hM hk]
  have h2 : (blockMid d M m k).card = (bst p M (k + 1) - m) - (bst p M k + m) := by
    rw [blockMid, Finset.card_image_of_injective _ (mul_isUnit_injective hd), card_baseMid hM hk]
  rw [h1, h2]
  omega

/-! ### Many representations in the middle of a dense block -/

/-- The pairs of dense indices `(i, j)` with `i + j + σ ≡ k (mod M)`. -/
noncomputable def pairIdx (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ : ℝ) (σ k : ℕ) :
    Finset (ℕ × ℕ) :=
  ((denseIdx A d M ε₁) ×ˢ (denseIdx A d M ε₁)).filter fun q => (q.1 + q.2 + σ) % M = k

lemma card_pairIdx_mul_le_rep {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d) {M : ℕ}
    (hM : 0 < M) {ε₁ : ℝ} {σ c k : ℕ} (hσ : σ ≤ 1) (hcL : c + 1 ≤ L p M)
    {z : ZMod p} (hz : z ∈ blockMid d M (c + 1) k) :
    (pairIdx A d M ε₁ σ k).card * c ≤ rep (granularization A d M ε₁) z := by
  classical
  obtain ⟨ze, hze, hzed⟩ := mem_blockMid.mp hz
  rw [mem_baseMid] at hze
  set F : ℕ × ℕ → Finset (ZMod p × ZMod p) :=
    fun q => {r ∈ block d M q.1 ×ˢ block d M q.2 | r.1 + r.2 = z} with hF
  have hpiece : ∀ q ∈ pairIdx A d M ε₁ σ k, c ≤ (F q).card := by
    rintro ⟨i, j⟩ hq
    simp only [pairIdx, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hiT, hjT⟩, hmod⟩ := hq
    have hi : i < M := (mem_denseIdx.mp hiT).1
    have hj : j < M := (mem_denseIdx.mp hjT).1
    set n : ℕ := i + j + σ with hn
    have ht2 : n / M < 2 := (Nat.div_lt_iff_lt_mul hM).mpr (by omega)
    have hdm : n / M * M + n % M = n := Nat.div_add_mod' n M
    obtain ⟨t, ht1, hnk⟩ : ∃ t, t ≤ 1 ∧ n = k + t * M := ⟨n / M, by omega, by omega⟩
    -- the lift of `ze.val`
    refine card_pairs_ge hd hM hi hj (s := ze.val + t * p) ?_ ?_ ?_ ?_ ?_
    · rw [← hzed]
      congr 1
      push_cast
      rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_rightInverse ze]
    · have := L_sub_one_le_len (p := p) hM hi
      omega
    · have := L_sub_one_le_len (p := p) hM hj
      omega
    · have key1 : bst p M i + bst p M j ≤ bst p M (i + j) := bst_add_le p M i j
      have key2 : bst p M (i + j) ≤ bst p M n := bst_mono p M (by omega)
      have key3 : bst p M n = bst p M k + t * p := by
        rw [hnk]; interval_cases t <;> simp [bst_add_M hM]
      omega
    · have key4 : bst p M (i + 1 + (j + 1)) ≤ bst p M (i + 1) + bst p M (j + 1) + 1 :=
        bst_add_le_add_one hM p (i + 1) (j + 1)
      have key5 : bst p M (n + 1) ≤ bst p M (i + 1 + (j + 1)) := bst_mono p M (by omega)
      have key6 : bst p M (n + 1) = bst p M (k + 1) + t * p := by
        have hnk1 : n + 1 = (k + 1) + t * M := by omega
        rw [hnk1]; interval_cases t <;> simp [bst_add_M hM]
      omega
  have hdisj : ∀ q ∈ pairIdx A d M ε₁ σ k, ∀ q' ∈ pairIdx A d M ε₁ σ k, q ≠ q' →
      Disjoint (F q) (F q') := by
    intro q _ q' _ hqq
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [hF] at hr hr'
    simp only [Finset.mem_filter, Finset.mem_product] at hr hr'
    by_cases h1 : q.1 = q'.1
    · have h2 : q.2 ≠ q'.2 := fun h => hqq (Prod.ext h1 h)
      exact (Finset.disjoint_left.mp (block_disjoint hd h2)) hr.1.2 hr'.1.2
    · exact (Finset.disjoint_left.mp (block_disjoint hd h1)) hr.1.1 hr'.1.1
  have hsub : (pairIdx A d M ε₁ σ k).biUnion F ⊆
      {r ∈ granularization A d M ε₁ ×ˢ granularization A d M ε₁ | r.1 + r.2 = z} := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨q, hq, hrq⟩ := hr
    simp only [pairIdx, Finset.mem_filter, Finset.mem_product] at hq
    rw [hF] at hrq
    simp only [Finset.mem_filter, Finset.mem_product] at hrq
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_biUnion.mpr ⟨q.1, hq.1.1, hrq.1.1⟩,
      Finset.mem_biUnion.mpr ⟨q.2, hq.1.2, hrq.1.2⟩⟩, hrq.2⟩
  calc (pairIdx A d M ε₁ σ k).card * c = ∑ _q ∈ pairIdx A d M ε₁ σ k, c := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ q ∈ pairIdx A d M ε₁ σ k, (F q).card := Finset.sum_le_sum hpiece
    _ = ((pairIdx A d M ε₁ σ k).biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ rep (granularization A d M ε₁) z := Finset.card_le_card hsub

/-! ### Step 1: counting the additive triples of `A'` by blocks -/

/-- The index triples `(i, j, k)` of dense blocks with `k ≡ i + j` or `k ≡ i + j + 1 (mod M)`. -/
noncomputable def admIdx (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ : ℝ) :
    Finset (ℕ × ℕ × ℕ) :=
  ((denseIdx A d M ε₁) ×ˢ (denseIdx A d M ε₁) ×ˢ (denseIdx A d M ε₁)).filter
    fun q => (q.1 + q.2.1) % M = q.2.2 ∨ (q.1 + q.2.1 + 1) % M = q.2.2

lemma card_triples_block_le {d : ZMod p} (hd : IsUnit d) {M i j k : ℕ} (hM : 0 < M)
    (hi : i < M) (hj : j < M) :
    #{t ∈ block d M i ×ˢ block d M j ×ˢ block d M k | t.1 + t.2.1 = t.2.2} ≤ L p M ^ 2 := by
  classical
  have hinj : #{t ∈ block d M i ×ˢ block d M j ×ˢ block d M k | t.1 + t.2.1 = t.2.2}
      ≤ (block d M i ×ˢ block d M j).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨ht.1.1, ht.1.2.1⟩
    · intro t ht t' ht' htt
      simp only [Finset.mem_coe, Finset.mem_filter] at ht ht'
      simp only [Prod.mk.injEq] at htt
      have : t.2.2 = t'.2.2 := by rw [← ht.2, ← ht'.2, htt.1, htt.2]
      exact Prod.ext htt.1 (Prod.ext htt.2 this)
  refine hinj.trans ?_
  rw [Finset.card_product, sq]
  exact Nat.mul_le_mul (block_card_le hd hM hi) (block_card_le hd hM hj)

theorem addTriples_granularization_le {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) {ε₁ : ℝ} :
    addTriples (granularization A d M ε₁) ≤ (admIdx A d M ε₁).card * L p M ^ 2 + M ^ 2 := by
  classical
  set A' := granularization A d M ε₁ with hA'
  set E : Finset (ZMod p) :=
    (Finset.range M).image fun i => ((bst p M i : ℕ) : ZMod p) * d with hE
  set S : Finset (ZMod p × ZMod p × ZMod p) :=
    {t ∈ A' ×ˢ A' ×ˢ A' | t.1 + t.2.1 = t.2.2} with hS
  set G : ℕ × ℕ × ℕ → Finset (ZMod p × ZMod p × ZMod p) :=
    fun q => {t ∈ block d M q.1 ×ˢ block d M q.2.1 ×ˢ block d M q.2.2 | t.1 + t.2.1 = t.2.2}
    with hG
  -- the triples whose first two entries are left endpoints
  have hS2 : #{t ∈ S | t.1 ∈ E ∧ t.2.1 ∈ E} ≤ M ^ 2 := by
    have hinj : #{t ∈ S | t.1 ∈ E ∧ t.2.1 ∈ E} ≤ (E ×ˢ E).card := by
      refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
      · intro t ht
        simp only [Finset.mem_coe, Finset.mem_filter] at ht
        simp only [Finset.mem_coe, Finset.mem_product]
        exact ⟨ht.2.1, ht.2.2⟩
      · intro t ht t' ht' htt
        simp only [Finset.mem_coe, Finset.mem_filter, hS, Finset.mem_filter] at ht ht'
        simp only [Prod.mk.injEq] at htt
        have : t.2.2 = t'.2.2 := by rw [← ht.1.2, ← ht'.1.2, htt.1, htt.2]
        exact Prod.ext htt.1 (Prod.ext htt.2 this)
    refine hinj.trans ?_
    have hcardE : E.card ≤ M := le_trans Finset.card_image_le (by rw [Finset.card_range])
    rw [Finset.card_product, sq]
    exact Nat.mul_le_mul hcardE hcardE
  -- the remaining triples lie in admissible block triples
  have hS1 : #{t ∈ S | ¬ (t.1 ∈ E ∧ t.2.1 ∈ E)} ≤ (admIdx A d M ε₁).card * L p M ^ 2 := by
    have hsub : {t ∈ S | ¬ (t.1 ∈ E ∧ t.2.1 ∈ E)} ⊆ (admIdx A d M ε₁).biUnion G := by
      intro t ht
      simp only [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_product] at ht
      obtain ⟨⟨⟨hx, hy, hz⟩, hsum⟩, hnot⟩ := ht
      rw [hA', granularization, Finset.mem_biUnion] at hx hy hz
      obtain ⟨i, hiT, hxi⟩ := hx
      obtain ⟨j, hjT, hyj⟩ := hy
      obtain ⟨k, hkT, hzk⟩ := hz
      have hi : i < M := (mem_denseIdx.mp hiT).1
      have hj : j < M := (mem_denseIdx.mp hjT).1
      have hk : k < M := (mem_denseIdx.mp hkT).1
      rcases block_add_index hd hM hk hxi hyj hzk hsum with h | h | ⟨h1, h2⟩
      · refine Finset.mem_biUnion.mpr ⟨(i, j, k), ?_, ?_⟩
        · simp only [admIdx, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hiT, hjT, hkT⟩, Or.inl h.symm⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hxi, hyj, hzk⟩, hsum⟩
      · refine Finset.mem_biUnion.mpr ⟨(i, j, k), ?_, ?_⟩
        · simp only [admIdx, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hiT, hjT, hkT⟩, Or.inr h.symm⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hxi, hyj, hzk⟩, hsum⟩
      · exact absurd ⟨h1 ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi),
          h2 ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr hj)⟩ hnot
    calc #{t ∈ S | ¬ (t.1 ∈ E ∧ t.2.1 ∈ E)} ≤ ((admIdx A d M ε₁).biUnion G).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ q ∈ admIdx A d M ε₁, (G q).card := Finset.card_biUnion_le
      _ ≤ (admIdx A d M ε₁).card * L p M ^ 2 := by
          rw [← smul_eq_mul]
          refine Finset.sum_le_card_nsmul _ _ _ ?_
          intro q hq
          simp only [admIdx, Finset.mem_filter, Finset.mem_product] at hq
          exact card_triples_block_le hd hM (mem_denseIdx.mp hq.1.1).1 (mem_denseIdx.mp hq.1.2.1).1
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun t => t.1 ∈ E ∧ t.2.1 ∈ E)
  have : addTriples A' = S.card := rfl
  rw [this, ← hsplit]
  omega

/-! ### Step 2: pigeonholing the admissible index triples -/

lemma card_pairIdx_le {A : Finset (ZMod p)} {d : ZMod p} {M : ℕ} {ε₁ : ℝ} {σ k : ℕ} :
    (pairIdx A d M ε₁ σ k).card ≤ M := by
  classical
  have key : (pairIdx A d M ε₁ σ k).card ≤ (Finset.range M).card := by
    refine Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, pairIdx, Finset.mem_filter, Finset.mem_product] at hq
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (mem_denseIdx.mp hq.1.1).1)
    · intro q hq q' hq' hqq
      simp only at hqq
      simp only [Finset.mem_coe, pairIdx, Finset.mem_filter, Finset.mem_product] at hq hq'
      have hj : q.2 < M := (mem_denseIdx.mp hq.1.2).1
      have hj' : q'.2 < M := (mem_denseIdx.mp hq'.1.2).1
      have hmod : (q.1 + q.2 + σ) % M = (q'.1 + q'.2 + σ) % M := by rw [hq.2, hq'.2]
      have hcancel : q.2 % M = q'.2 % M := by
        have h1 : (q.1 + σ) + q.2 ≡ (q.1 + σ) + q'.2 [MOD M] := by
          show _ % M = _ % M
          rw [show q.1 + σ + q.2 = q.1 + q.2 + σ from by ring,
            show q.1 + σ + q'.2 = q'.1 + q'.2 + σ from by omega]
          exact hmod
        exact Nat.ModEq.add_left_cancel' _ h1
      rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at hcancel
      exact Prod.ext hqq hcancel
  rwa [Finset.card_range] at key

lemma card_admIdx_le_sum {A : Finset (ZMod p)} {d : ZMod p} {M : ℕ} {ε₁ : ℝ} :
    (admIdx A d M ε₁).card
      ≤ ∑ k ∈ denseIdx A d M ε₁,
          ((pairIdx A d M ε₁ 0 k).card + (pairIdx A d M ε₁ 1 k).card) := by
  classical
  set T := denseIdx A d M ε₁ with hT
  have hsub : admIdx A d M ε₁ ⊆
      T.biUnion fun k => ((pairIdx A d M ε₁ 0 k) ∪ (pairIdx A d M ε₁ 1 k)).image
        fun q => (q.1, q.2, k) := by
    intro q hq
    simp only [admIdx, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2, h3⟩, hadm⟩ := hq
    refine Finset.mem_biUnion.mpr ⟨q.2.2, h3, Finset.mem_image.mpr ⟨(q.1, q.2.1), ?_, rfl⟩⟩
    rcases hadm with h | h
    · exact Finset.mem_union_left _ (by
        simp only [pairIdx, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨h1, h2⟩, by simpa using h⟩)
    · exact Finset.mem_union_right _ (by
        simp only [pairIdx, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨h1, h2⟩, h⟩)
  calc (admIdx A d M ε₁).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ T, (((pairIdx A d M ε₁ 0 k) ∪ (pairIdx A d M ε₁ 1 k)).image
          fun q => (q.1, q.2, k)).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ T, ((pairIdx A d M ε₁ 0 k).card + (pairIdx A d M ε₁ 1 k).card) :=
        Finset.sum_le_sum fun k _ =>
          le_trans Finset.card_image_le (Finset.card_union_le _ _)

/-! ### Step 4: `A` is dense in the middle of a dense block -/

lemma card_inter_blockMid_ge {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d) {M : ℕ}
    (hM : 0 < M) {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) {m k : ℕ} (hk : k ∈ denseIdx A d M ε₁) :
    ε₁ * ((L p M : ℝ) - 1) - 2 * m ≤ ((A ∩ blockMid d M m k).card : ℝ) := by
  classical
  obtain ⟨hkM, hdense⟩ := mem_denseIdx.mp hk
  have hsub : A ∩ block d M k ⊆ (A ∩ blockMid d M m k) ∪ (block d M k \ blockMid d M m k) := by
    intro x hx
    rw [Finset.mem_inter] at hx
    by_cases hmid : x ∈ blockMid d M m k
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx.1, hmid⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx.2, hmid⟩)
  have hsd : (block d M k \ blockMid d M m k).card ≤ 2 * m := by
    rw [Finset.card_sdiff_of_subset blockMid_subset_block]
    have := card_block_le_card_blockMid_add (p := p) (d := d) (m := m) hd hM hkM
    omega
  have hnat : (A ∩ block d M k).card ≤ (A ∩ blockMid d M m k).card + 2 * m :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_left hsd _))
  have hcast : ((A ∩ block d M k).card : ℝ) ≤ ((A ∩ blockMid d M m k).card : ℝ) + 2 * m := by
    exact_mod_cast hnat
  have hge : (L p M : ℝ) - 1 ≤ ((block d M k).card : ℝ) := by
    have h := block_card_ge hd hM hkM
    have h' : ((L p M - 1 : ℕ) : ℝ) ≤ ((block d M k).card : ℝ) := by exact_mod_cast h
    have hcast2 : ((L p M - 1 : ℕ) : ℝ) = (L p M : ℝ) - 1 := by
      have hL1 : 1 ≤ L p M := L_pos (p := p) hM
      have : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    linarith [hcast2 ▸ h']
  nlinarith [mul_le_mul_of_nonneg_left hge hε₁]

/-! ### Proposition 4 -/

/-- **Green, Proposition 4.**  If `A ⊆ ZMod p` is sum-free and `d` is a good length for `A`
(with the parameters `ε₁ = ε`, `ε₂ = ε²/144`, `ε₃ = ε²/80`), then the granularization
`A' = ⋃_{i ∈ T} I i` has at most `ε p²` additive triples. -/
theorem prop4_addTriples_le {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hsf : ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A) {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M)
    (hMp : M < p) (hLp : 2 * L p M - 1 ≤ p) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεL : 24 ≤ ε * L p M)
    (hgood : IsGoodLength A d M ε (ε ^ 2 / 144) (ε ^ 2 / 80)) :
    (addTriples (granularization A d M ε) : ℝ) ≤ ε * (p : ℝ) ^ 2 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hLnn : (0 : ℝ) ≤ (L p M : ℝ) := Nat.cast_nonneg _
  have hL24 : (24 : ℝ) ≤ (L p M : ℝ) := by nlinarith only [hεL, hε1, hε, hLnn]
  have hL0 : (0 : ℝ) < (L p M : ℝ) := by linarith only [hL24]
  have hpML : (p : ℝ) ≤ (M : ℝ) * (L p M : ℝ) := by
    have h := p_le_M_mul_L (p := p) hM
    exact_mod_cast h
  have hMLub : (M : ℝ) * (L p M : ℝ) ≤ 13 / 12 * (p : ℝ) := by
    have hL1 : 1 ≤ L p M := L_pos (p := p) hM
    have h := M_mul_L_sub_one_lt (p := p) hM
    have hc : ((M * (L p M - 1) : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hL1, Nat.cast_one] at hc
    have hh : (0 : ℝ) ≤ (M : ℝ) * ((L p M : ℝ) - 24) :=
      mul_nonneg hM0.le (by linarith only [hL24])
    linarith only [hc, hh]
  have hMub : (M : ℝ) ≤ 1 / 22 * ε * (p : ℝ) := by
    have ha := mul_le_mul_of_nonneg_left hεL hM0.le
    have hb := mul_le_mul_of_nonneg_left hMLub hε.le
    linarith only [ha, hb]
  have hM2 : (M : ℝ) ^ 2 ≤ 1 / 484 * ε * (p : ℝ) ^ 2 := by
    have h1 : (M : ℝ) ^ 2 ≤ (1 / 22 * ε * (p : ℝ)) ^ 2 := pow_le_pow_left₀ hM0.le hMub 2
    have h2 : ε ^ 2 ≤ ε := by nlinarith only [hε, hε1]
    have h3 : ε ^ 2 * (p : ℝ) ^ 2 ≤ ε * (p : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    linarith only [h1, h3]
  -- Step 1: counting additive triples by blocks
  have hNnn : (0 : ℝ) ≤ ((admIdx A d M ε).card : ℝ) := Nat.cast_nonneg _
  have hadmbd : (addTriples (granularization A d M ε) : ℝ)
      ≤ ((admIdx A d M ε).card : ℝ) * (L p M : ℝ) ^ 2 + (M : ℝ) ^ 2 := by
    have h := addTriples_granularization_le (A := A) hd hM (ε₁ := ε)
    exact_mod_cast h
  have h1 : 483 / 484 * ε * (p : ℝ) ^ 2
      < ((admIdx A d M ε).card : ℝ) * (L p M : ℝ) ^ 2 := by
    linarith only [hcon, hadmbd, hM2]
  have hL2M2 : (L p M : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ 169 / 144 * (p : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (M : ℝ) * (L p M : ℝ)) hMLub
    linarith only [h]
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hadmlb : 4 / 5 * ε * (M : ℝ) ^ 2 < ((admIdx A d M ε).card : ℝ) := by
    have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
    have hstep1 := mul_lt_mul_of_pos_right h1 hMsq
    have hstep2 : ((admIdx A d M ε).card : ℝ) * ((L p M : ℝ) ^ 2 * (M : ℝ) ^ 2)
        ≤ ((admIdx A d M ε).card : ℝ) * (169 / 144 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hL2M2 hNnn
    have h4 : (483 / 484 * ε * (M : ℝ) ^ 2) * (p : ℝ) ^ 2
        < (169 / 144 * ((admIdx A d M ε).card : ℝ)) * (p : ℝ) ^ 2 := by
      linarith only [hstep1, hstep2]
    have h5 := lt_of_mul_lt_mul_right h4 hpsq.le
    linarith only [h5]
  -- Step 2: pigeonhole on the shift `σ`
  have hsum : ((admIdx A d M ε).card : ℝ)
      ≤ (∑ k ∈ denseIdx A d M ε, ((pairIdx A d M ε 0 k).card : ℝ))
        + ∑ k ∈ denseIdx A d M ε, ((pairIdx A d M ε 1 k).card : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (card_admIdx_le_sum (A := A) (d := d) (M := M) (ε₁ := ε))
    rw [Nat.cast_sum] at h
    push_cast at h
    rwa [Finset.sum_add_distrib] at h
  obtain ⟨σ, hσ1, hSig⟩ : ∃ σ : ℕ, σ ≤ 1 ∧
      2 / 5 * ε * (M : ℝ) ^ 2 < ∑ k ∈ denseIdx A d M ε, ((pairIdx A d M ε σ k).card : ℝ) := by
    rcases lt_or_ge (2 / 5 * ε * (M : ℝ) ^ 2)
        (∑ k ∈ denseIdx A d M ε, ((pairIdx A d M ε 0 k).card : ℝ)) with h | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, le_rfl, by linarith only [hadmlb, hsum, h]⟩
  -- Step 2b: the popular residues `k`
  have hTsub : denseIdx A d M ε ⊆ Finset.range M := by
    rw [denseIdx]; exact Finset.filter_subset _ _
  have hTcard : ((denseIdx A d M ε).card : ℝ) ≤ (M : ℝ) := by
    have h := Finset.card_le_card hTsub
    rw [Finset.card_range] at h
    exact_mod_cast h
  set K : Finset ℕ := (denseIdx A d M ε).filter
    fun k => 1 / 5 * ε * (M : ℝ) ≤ ((pairIdx A d M ε σ k).card : ℝ) with hKdef
  clear_value K
  have hsplit := Finset.sum_filter_add_sum_filter_not (denseIdx A d M ε)
    (fun k => 1 / 5 * ε * (M : ℝ) ≤ ((pairIdx A d M ε σ k).card : ℝ))
    (fun k => ((pairIdx A d M ε σ k).card : ℝ))
  have hsmall : ∑ k ∈ (denseIdx A d M ε).filter
      (fun k => ¬ (1 / 5 * ε * (M : ℝ) ≤ ((pairIdx A d M ε σ k).card : ℝ))),
      ((pairIdx A d M ε σ k).card : ℝ) ≤ 1 / 5 * ε * (M : ℝ) ^ 2 := by
    have hcardle : (((denseIdx A d M ε).filter
        (fun k => ¬ (1 / 5 * ε * (M : ℝ) ≤ ((pairIdx A d M ε σ k).card : ℝ)))).card : ℝ)
        ≤ (M : ℝ) := by
      refine le_trans ?_ hTcard
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hb : ∀ k ∈ (denseIdx A d M ε).filter
        (fun k => ¬ (1 / 5 * ε * (M : ℝ) ≤ ((pairIdx A d M ε σ k).card : ℝ))),
        ((pairIdx A d M ε σ k).card : ℝ) ≤ 1 / 5 * ε * (M : ℝ) := fun k hk =>
      le_of_lt (not_le.mp (Finset.mem_filter.mp hk).2)
    have h2 := Finset.sum_le_card_nsmul _ _ (1 / 5 * ε * (M : ℝ)) hb
    rw [nsmul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_right hcardle
      (by positivity : (0 : ℝ) ≤ 1 / 5 * ε * (M : ℝ))
    linarith only [h2, h3]
  have hKsum : 1 / 5 * ε * (M : ℝ) ^ 2 < ∑ k ∈ K, ((pairIdx A d M ε σ k).card : ℝ) := by
    rw [hKdef]; linarith only [hsplit, hsmall, hSig]
  have hKub : ∑ k ∈ K, ((pairIdx A d M ε σ k).card : ℝ) ≤ (K.card : ℝ) * (M : ℝ) := by
    have hb : ∀ k ∈ K, ((pairIdx A d M ε σ k).card : ℝ) ≤ (M : ℝ) := by
      intro k _
      exact_mod_cast card_pairIdx_le (A := A) (d := d) (M := M) (ε₁ := ε) (σ := σ) (k := k)
    have h2 := Finset.sum_le_card_nsmul _ _ (M : ℝ) hb
    rwa [nsmul_eq_mul] at h2
  have hKlb : 1 / 5 * ε * (M : ℝ) < (K.card : ℝ) := by
    have h : 1 / 5 * ε * (M : ℝ) ^ 2 < (K.card : ℝ) * (M : ℝ) := lt_of_lt_of_le hKsum hKub
    have h2 : (1 / 5 * ε * (M : ℝ)) * (M : ℝ) < (K.card : ℝ) * (M : ℝ) := by
      rw [show (1 / 5 * ε * (M : ℝ)) * (M : ℝ) = 1 / 5 * ε * (M : ℝ) ^ 2 from by ring]
      exact h
    exact lt_of_mul_lt_mul_right h2 hM0.le
  -- the margin `c` of the middle part of a block
  set c : ℕ := ⌈ε * (L p M : ℝ) / 4⌉₊ with hcdef
  have hcge : ε * (L p M : ℝ) / 4 ≤ (c : ℝ) := Nat.le_ceil _
  have hclt : (c : ℝ) < ε * (L p M : ℝ) / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
  clear_value c
  have hεLle : ε * (L p M : ℝ) ≤ (L p M : ℝ) := by nlinarith only [hε1, hL0]
  have hcL : c + 1 ≤ L p M := by
    have h : ((c + 1 : ℕ) : ℝ) < (L p M : ℝ) := by
      push_cast
      linarith only [hclt, hεLle, hL24]
    have h' : c + 1 < L p M := by exact_mod_cast h
    exact Nat.le_of_lt h'
  -- Step 5: the exceptional set of Proposition 3
  have hbadle : ((Finset.univ.filter fun x : ZMod p =>
      ε ^ 2 / 144 * (p : ℝ) ≤ ((rep (granularization A d M ε) x : ℕ) : ℝ) ∧ rep A x = 0).card : ℝ)
      ≤ ε ^ 2 / 80 * (p : ℝ) :=
    bad_card_le hA hd hM hMp hLp hε (by positivity) (by positivity) hgood
  have hEML : ε ^ 2 * (p : ℝ) ≤ ε ^ 2 * ((M : ℝ) * (L p M : ℝ)) :=
    mul_le_mul_of_nonneg_left hpML (sq_nonneg ε)
  have hsubbad : ∀ k ∈ K, A ∩ blockMid d M (c + 1) k ⊆
      Finset.univ.filter fun x : ZMod p =>
        ε ^ 2 / 144 * (p : ℝ) ≤ ((rep (granularization A d M ε) x : ℕ) : ℝ) ∧ rep A x = 0 := by
    intro k hk x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hxA, hxmid⟩ := hx
    rw [hKdef, Finset.mem_filter] at hk
    obtain ⟨-, hkbig⟩ := hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hrep := card_pairIdx_mul_le_rep (A := A) (ε₁ := ε) hd hM hσ1 hcL hxmid
      have hrepR : ((pairIdx A d M ε σ k).card : ℝ) * (c : ℝ)
          ≤ ((rep (granularization A d M ε) x : ℕ) : ℝ) := by exact_mod_cast hrep
      have hn0 : (0 : ℝ) ≤ 1 / 5 * ε * (M : ℝ) := by positivity
      have hc0 : (0 : ℝ) ≤ ε * (L p M : ℝ) / 4 := by positivity
      have hprod : (1 / 5 * ε * (M : ℝ)) * (ε * (L p M : ℝ) / 4)
          ≤ ((pairIdx A d M ε σ k).card : ℝ) * (c : ℝ) :=
        mul_le_mul hkbig hcge hc0 (le_trans hn0 hkbig)
      linarith only [hprod, hrepR, hEML]
    · rw [rep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      intro hs
      exact hsf a hab.1 b hab.2 (by rw [hs]; exact hxA)
  have hdisjK : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' →
      Disjoint (A ∩ blockMid d M (c + 1) k) (A ∩ blockMid d M (c + 1) k') := by
    intro k _ k' _ hkk
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    exact (Finset.disjoint_left.mp (block_disjoint hd hkk))
      (blockMid_subset_block (Finset.mem_inter.mp hx).2)
      (blockMid_subset_block (Finset.mem_inter.mp hx').2)
  have hbig2 : ∑ k ∈ K, ((A ∩ blockMid d M (c + 1) k).card : ℝ)
      ≤ ((Finset.univ.filter fun x : ZMod p =>
        ε ^ 2 / 144 * (p : ℝ) ≤ ((rep (granularization A d M ε) x : ℕ) : ℝ)
          ∧ rep A x = 0).card : ℝ) := by
    have hsub : (K.biUnion fun k => A ∩ blockMid d M (c + 1) k) ⊆
        Finset.univ.filter fun x : ZMod p =>
          ε ^ 2 / 144 * (p : ℝ) ≤ ((rep (granularization A d M ε) x : ℕ) : ℝ)
            ∧ rep A x = 0 := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      exact hsubbad k hk hxk
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisjK] at hcard
    have hcast : ((∑ k ∈ K, (A ∩ blockMid d M (c + 1) k).card : ℕ) : ℝ) ≤ _ :=
      (Nat.cast_le (α := ℝ)).mpr hcard
    rwa [Nat.cast_sum] at hcast
  have hterm : ∀ k ∈ K, ε * (L p M : ℝ) / 4 ≤ ((A ∩ blockMid d M (c + 1) k).card : ℝ) := by
    intro k hk
    have hkT : k ∈ denseIdx A d M ε := (Finset.mem_filter.mp (hKdef ▸ hk)).1
    have h := card_inter_blockMid_ge (m := c + 1) hd hM hε.le hkT
    push_cast at h
    linarith only [h, hclt, hεL, hε1]
  have hsum2 : (K.card : ℝ) * (ε * (L p M : ℝ) / 4)
      ≤ ∑ k ∈ K, ((A ∩ blockMid d M (c + 1) k).card : ℝ) := by
    have h2 := Finset.card_nsmul_le_sum K _ (ε * (L p M : ℝ) / 4) hterm
    rwa [nsmul_eq_mul] at h2
  have hlast : (1 / 5 * ε * (M : ℝ)) * (ε * (L p M : ℝ) / 4)
      < (K.card : ℝ) * (ε * (L p M : ℝ) / 4) :=
    mul_lt_mul_of_pos_right hKlb (by positivity)
  have hpos : (0 : ℝ) < ε ^ 2 * (p : ℝ) := by positivity
  linarith only [hbadle, hbig2, hsum2, hlast, hEML, hpos]

end CameronErdos

#print axioms CameronErdos.bst_mono
#print axioms CameronErdos.bst_zero
#print axioms CameronErdos.bst_M
#print axioms CameronErdos.bst_le_p
#print axioms CameronErdos.bst_add_le
#print axioms CameronErdos.bst_add_le_add_one
#print axioms CameronErdos.bst_add_M
#print axioms CameronErdos.mem_baseBlock'
#print axioms CameronErdos.card_baseBlock'
#print axioms CameronErdos.len_le_L
#print axioms CameronErdos.L_sub_one_le_len
#print axioms CameronErdos.p_le_M_mul_L
#print axioms CameronErdos.M_mul_L_sub_one_lt
#print axioms CameronErdos.card_pairs_ge
#print axioms CameronErdos.val_add_cases
#print axioms CameronErdos.block_add_index
#print axioms CameronErdos.mem_baseMid
#print axioms CameronErdos.mem_blockMid
#print axioms CameronErdos.baseMid_subset
#print axioms CameronErdos.blockMid_subset_block
#print axioms CameronErdos.card_baseMid
#print axioms CameronErdos.card_block_le_card_blockMid_add
#print axioms CameronErdos.card_pairIdx_mul_le_rep
#print axioms CameronErdos.card_triples_block_le
#print axioms CameronErdos.addTriples_granularization_le
#print axioms CameronErdos.card_pairIdx_le
#print axioms CameronErdos.card_admIdx_le_sum
#print axioms CameronErdos.card_inter_blockMid_ge
#print axioms CameronErdos.prop4_addTriples_le
