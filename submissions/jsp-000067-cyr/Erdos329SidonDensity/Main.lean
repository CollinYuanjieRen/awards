import Mathlib

/-!
# Erdős Problem #329: a Sidon set with `limsup |A ∩ [1,N]| / √N ≥ 1/2`

Let `A ⊆ ℕ` be a Sidon set (all pairwise sums distinct up to order).  Erdős asked how large
`limsup_{N→∞} |A ∩ {1, …, N}| / N^{1/2}` can be (OPEN; Erdős–Turán proved it is at most `1`,
Krückeberg attained `1/√2`).  The problem page records that Erdős proved `1/2` is possible.
This file proves that statement in the exact shape of the formal-conjectures theorem
`Erdos329.erdos_329.variants.lower_bound` (tagged "research solved" with `sorry`), with the
definitions `IsSidon`, `sqrtPartialDensity`, `sidonUpperDensity` copied verbatim.

Construction.  For an odd prime `p` the Erdős–Turán set `S_p = {2p·i + (i² mod p) : 0 ≤ i < p}`
is a Sidon set of `p` elements in `[0, 2p²)` whose nonzero differences have absolute value at
least `p + 1`.  Place translated copies `N_k + S_{p_k}` in successive blocks, with `p_k` a prime
larger than every element of the previous blocks and `N_k` just above the previous block; a sum
relation `a + b = c + d` is then confined to a single block (the block gaps and the difference
bound rule out cross-block coincidences), so the union is Sidon, and at `N = N_k + 2p_k²` it has
at least `p_k` elements in `[1, N]` with `N ≤ (2p_k + 1)²`, giving partial density
`≥ p_k / (2p_k + 1) → 1/2`, hence upper density `≥ 1/2`.  The value of the supremum,
Krückeberg's `1/√2` and the Erdős–Turán bound `1` are not addressed.
-/

open Function Set Filter

/-- A Sidon set is a set such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition (formal-conjectures definition). -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- The partial density of a Sidon set `A` up to `N`, normalized by dividing by `√N`
(formal-conjectures definition). -/
noncomputable def sqrtPartialDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt

/-- The upper density of a Sidon set `A`, normalized by `√N` (formal-conjectures definition). -/
noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => sqrtPartialDensity A N) atTop

/-- The Erdős–Turán Sidon set modulo `p`: `{2p·i + (i² mod p) : i < p}`. -/
def erdosTuranSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).image fun i ↦ 2 * p * i + i ^ 2 % p

/-- If `2p·X + s = 2p·Y + t` with remainders `s, t < 2p`, then quotients and remainders agree. -/
private lemma split_two_mul {p X Y s t : ℕ} (hp : 0 < p) (hs : s < 2 * p) (ht : t < 2 * p)
    (h : 2 * p * X + s = 2 * p * Y + t) : X = Y ∧ s = t := by
  have h2p : 0 < 2 * p := by omega
  constructor
  · have hd := congrArg (fun z => z / (2 * p)) h
    simpa [Nat.mul_add_div h2p, Nat.div_eq_of_lt hs, Nat.div_eq_of_lt ht] using hd
  · have hm := congrArg (fun z => z % (2 * p)) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] using hm

/-- Membership in the Erdős–Turán set. -/
private lemma mem_erdosTuranSet {p x : ℕ} :
    x ∈ erdosTuranSet p ↔ ∃ i, i < p ∧ 2 * p * i + i ^ 2 % p = x := by
  simp [erdosTuranSet]

/-- For an odd prime `p`, `erdosTuranSet p` is a Sidon set. -/
theorem erdosTuranSet_isSidon (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    IsSidon ((erdosTuranSet p : Set ℕ)) := by
  have hp0 : 0 < p := hp.pos
  intro a ha c hc b hb d hd h
  rw [Finset.mem_coe, mem_erdosTuranSet] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨l, hl, rfl⟩ := hd
  have hri : i ^ 2 % p < p := Nat.mod_lt _ hp0
  have hrj : j ^ 2 % p < p := Nat.mod_lt _ hp0
  have hrk : k ^ 2 % p < p := Nat.mod_lt _ hp0
  have hrl : l ^ 2 % p < p := Nat.mod_lt _ hp0
  -- Reading the equation modulo `2p` gives `i + j = k + l` and equality of the residue sums.
  have hsum : 2 * p * (i + j) + (i ^ 2 % p + j ^ 2 % p)
      = 2 * p * (k + l) + (k ^ 2 % p + l ^ 2 % p) := by
    have e1 : 2 * p * (i + j) = 2 * p * i + 2 * p * j := by ring
    have e2 : 2 * p * (k + l) = 2 * p * k + 2 * p * l := by ring
    rw [e1, e2]
    linarith
  obtain ⟨hij, hrs⟩ := split_two_mul hp0 (by linarith) (by linarith) hsum
  have hmod : (i ^ 2 + j ^ 2) % p = (k ^ 2 + l ^ 2) % p := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [hrs]
  have hdvd : (p : ℤ) ∣ ((k : ℤ) ^ 2 + (l : ℤ) ^ 2) - ((i : ℤ) ^ 2 + (j : ℤ) ^ 2) := by
    have hmd : (i ^ 2 + j ^ 2) ≡ (k ^ 2 + l ^ 2) [MOD p] := hmod
    have hz := Nat.modEq_iff_dvd.mp hmd
    push_cast at hz
    exact hz
  have hijZ : (i : ℤ) + (j : ℤ) = (k : ℤ) + (l : ℤ) := by exact_mod_cast hij
  obtain ⟨c, hc⟩ := hdvd
  -- `(k - i)(k - j) = ij - kl`, and `p ∣ 2(ij - kl)`.
  have h2 : (p : ℤ) ∣ 2 * (((k : ℤ) - (i : ℤ)) * ((k : ℤ) - (j : ℤ))) := by
    refine ⟨c, ?_⟩
    linear_combination hc + ((i : ℤ) + (j : ℤ) - (k : ℤ) + (l : ℤ)) * hijZ
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot2 : ¬ ((p : ℤ) ∣ 2) := by
    intro hdd
    have h2' : p ∣ 2 := by exact_mod_cast hdd
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
  have hmul : (p : ℤ) ∣ ((k : ℤ) - (i : ℤ)) * ((k : ℤ) - (j : ℤ)) :=
    (hpZ.dvd_mul.mp h2).resolve_left hnot2
  rcases hpZ.dvd_mul.mp hmul with hki | hkj
  · have hik : i = k := (Nat.modEq_iff_dvd.mpr (by exact_mod_cast hki)).eq_of_lt_of_lt hi hk
    subst hik
    have hjl : j = l := by omega
    subst hjl
    exact Or.inl ⟨rfl, rfl⟩
  · have hjk : j = k := (Nat.modEq_iff_dvd.mpr (by exact_mod_cast hkj)).eq_of_lt_of_lt hj hk
    subst hjk
    have hil : i = l := by omega
    subst hil
    exact Or.inr ⟨rfl, rfl⟩

/-- Every element of `erdosTuranSet p` is smaller than `2p²`. -/
private lemma erdosTuranSet_lt {p s : ℕ} (hp : 0 < p) (hs : s ∈ erdosTuranSet p) :
    s < 2 * p ^ 2 := by
  rw [mem_erdosTuranSet] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  have h1 : i ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * (i + 1) ≤ 2 * p * p := Nat.mul_le_mul (le_refl (2 * p)) (by omega)
  have h3 : 2 * p * (i + 1) = 2 * p * i + 2 * p := by ring
  have h4 : 2 * p * p = 2 * p ^ 2 := by ring
  linarith

/-- Two elements of `erdosTuranSet p` that differ by less than `p` are equal: the nonzero
differences of the Erdős–Turán set are at least `p + 1` in absolute value. -/
private lemma erdosTuranSet_close {p s t : ℕ} (hp : 0 < p) (hs : s ∈ erdosTuranSet p)
    (ht : t ∈ erdosTuranSet p) (h1 : t < s + p) (h2 : s < t + p) : s = t := by
  rw [mem_erdosTuranSet] at hs ht
  obtain ⟨i, hi, rfl⟩ := hs
  obtain ⟨j, hj, rfl⟩ := ht
  have hri : i ^ 2 % p < p := Nat.mod_lt _ hp
  have hrj : j ^ 2 % p < p := Nat.mod_lt _ hp
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    have e1 : 2 * p * (i + 1) ≤ 2 * p * j := Nat.mul_le_mul (le_refl (2 * p)) (by omega)
    have e2 : 2 * p * (i + 1) = 2 * p * i + 2 * p := by ring
    linarith [Nat.zero_le (j ^ 2 % p)]
  · rw [heq]
  · exfalso
    have e1 : 2 * p * (j + 1) ≤ 2 * p * i := Nat.mul_le_mul (le_refl (2 * p)) (by omega)
    have e2 : 2 * p * (j + 1) = 2 * p * j + 2 * p := by ring
    linarith [Nat.zero_le (i ^ 2 % p)]

/-- The Erdős–Turán set has exactly `p` elements. -/
private lemma card_erdosTuranSet {p : ℕ} (hp : 0 < p) : (erdosTuranSet p).card = p := by
  rw [erdosTuranSet, Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy hxy
  rw [Finset.coe_range, Set.mem_Iio] at hx hy
  have h1 : x ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : y ^ 2 % p < p := Nat.mod_lt _ hp
  exact (split_two_mul hp (by linarith) (by linarith) hxy).1

/-- A prime strictly larger than `m`. -/
private noncomputable def nextPrime (m : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (m + 1))

private lemma nextPrime_gt (m : ℕ) : m < nextPrime m :=
  (Classical.choose_spec (Nat.exists_infinite_primes (m + 1))).1

private lemma nextPrime_prime (m : ℕ) : (nextPrime m).Prime :=
  (Classical.choose_spec (Nat.exists_infinite_primes (m + 1))).2

/-- The data of the construction: `(blockStart k, blockPrime k)`, defined by recursion so that
the `(k+1)`-st prime is larger than the top of the `k`-th block and the `(k+1)`-st block starts
above twice the top of the `k`-th block plus twice the square of the new prime. -/
private noncomputable def blockData : ℕ → ℕ × ℕ
  | 0 => (19, 3)
  | k + 1 =>
      (2 * ((blockData k).1 + 2 * (blockData k).2 ^ 2)
          + 2 * nextPrime ((blockData k).1 + 2 * (blockData k).2 ^ 2) ^ 2 + 1,
        nextPrime ((blockData k).1 + 2 * (blockData k).2 ^ 2))

/-- The start of the `k`-th block. -/
private noncomputable def blockN (k : ℕ) : ℕ := (blockData k).1

/-- The prime used in the `k`-th block. -/
private noncomputable def blockP (k : ℕ) : ℕ := (blockData k).2

/-- A strict upper bound for the `k`-th block. -/
private noncomputable def blockM (k : ℕ) : ℕ := blockN k + 2 * blockP k ^ 2

private lemma blockM_def (k : ℕ) : blockM k = blockN k + 2 * blockP k ^ 2 := rfl

private lemma blockN_zero : blockN 0 = 19 := rfl

private lemma blockP_zero : blockP 0 = 3 := rfl

private lemma blockP_succ (k : ℕ) : blockP (k + 1) = nextPrime (blockM k) := rfl

private lemma blockN_succ (k : ℕ) :
    blockN (k + 1) = 2 * blockM k + 2 * blockP (k + 1) ^ 2 + 1 := rfl

private lemma blockM_lt_blockP (k : ℕ) : blockM k < blockP (k + 1) := by
  rw [blockP_succ]; exact nextPrime_gt _

private lemma blockP_prime : ∀ k, (blockP k).Prime
  | 0 => by rw [blockP_zero]; norm_num
  | k + 1 => by rw [blockP_succ]; exact nextPrime_prime _

private lemma blockN_ge (k : ℕ) : 2 * blockP k ^ 2 ≤ blockN k := by
  cases k with
  | zero => rw [blockN_zero, blockP_zero]; norm_num
  | succ k => rw [blockN_succ]; linarith

private lemma blockN_le_blockM (k : ℕ) : blockN k ≤ blockM k := by
  rw [blockM_def]; exact Nat.le_add_right _ _

private lemma blockP_ge_three : ∀ k, 3 ≤ blockP k
  | 0 => by rw [blockP_zero]
  | k + 1 => by
      have h1 := blockM_lt_blockP k
      have h2 := blockN_ge k
      have h3 : 1 ≤ blockP k := (blockP_prime k).pos
      have h4 := blockM_def k
      nlinarith

private lemma blockP_ne_two (k : ℕ) : blockP k ≠ 2 := by
  have := blockP_ge_three k; omega

private lemma blockM_lt_blockN_succ (k : ℕ) : blockM k < blockN (k + 1) := by
  rw [blockN_succ]
  linarith [Nat.zero_le (blockM k), Nat.zero_le (2 * blockP (k + 1) ^ 2)]

private lemma blockN_lt_succ (k : ℕ) : blockN k < blockN (k + 1) :=
  lt_of_le_of_lt (blockN_le_blockM k) (blockM_lt_blockN_succ k)

private lemma blockM_lt_succ (k : ℕ) : blockM k < blockM (k + 1) :=
  lt_of_lt_of_le (blockM_lt_blockN_succ k) (blockN_le_blockM (k + 1))

private lemma blockN_mono : Monotone blockN :=
  monotone_nat_of_le_succ fun k => (blockN_lt_succ k).le

private lemma blockM_mono : Monotone blockM :=
  monotone_nat_of_le_succ fun k => (blockM_lt_succ k).le

private lemma blockN_ge_one (k : ℕ) : 1 ≤ blockN k := by
  have h := blockN_mono (Nat.zero_le k)
  rw [blockN_zero] at h
  omega

private lemma le_blockN : ∀ k, k ≤ blockN k
  | 0 => by rw [blockN_zero]; norm_num
  | k + 1 => by have := le_blockN k; have := blockN_lt_succ k; omega

private lemma le_blockM (k : ℕ) : k ≤ blockM k :=
  le_trans (le_blockN k) (blockN_le_blockM k)

private lemma le_blockP : ∀ k, k ≤ blockP k
  | 0 => by rw [blockP_zero]; norm_num
  | k + 1 => by
      have h1 := blockM_lt_blockP k
      have h2 := le_blockM k
      omega

/-- The prime of a block dominates the top of every earlier block. -/
private lemma blockM_lt_blockP_of_lt {j k : ℕ} (h : j < k) : blockM j < blockP k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact lt_of_le_of_lt (blockM_mono (by omega : j ≤ m)) (blockM_lt_blockP m)

/-- The gap before the `k`-th block dominates twice the top of every earlier block plus the
internal spread of the `k`-th block. -/
private lemma blockN_gap {j k : ℕ} (h : j < k) :
    2 * blockM j + 2 * blockP k ^ 2 < blockN k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm := blockM_mono (by omega : j ≤ m)
  rw [blockN_succ]
  linarith

/-- The `k`-th block: a translate of the Erdős–Turán set of the `k`-th prime. -/
private noncomputable def block (k : ℕ) : Finset ℕ :=
  (erdosTuranSet (blockP k)).image fun s => blockN k + s

private lemma mem_block {k x : ℕ} :
    x ∈ block k ↔ ∃ s ∈ erdosTuranSet (blockP k), blockN k + s = x := by
  simp [block]

private lemma block_bounds {k x : ℕ} (hx : x ∈ block k) : blockN k ≤ x ∧ x < blockM k := by
  rw [mem_block] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have h1 := erdosTuranSet_lt (blockP_prime k).pos hs
  have h2 := blockM_def k
  constructor <;> omega

private lemma card_block (k : ℕ) : (block k).card = blockP k := by
  rw [block, Finset.card_image_of_injOn (fun x _ y _ h => by omega),
    card_erdosTuranSet (blockP_prime k).pos]

/-- Elements of a later block are more than twice as large as elements of an earlier one. -/
private lemma block_gap {j k x y : ℕ} (h : j < k) (hx : x ∈ block j) (hy : y ∈ block k) :
    2 * x < y := by
  have h1 := (block_bounds hx).2
  have h2 := (block_bounds hy).1
  have h3 := blockN_gap h
  linarith [Nat.zero_le (2 * blockP k ^ 2)]

/-- The Sidon set of Erdős's construction: the union of all blocks. -/
private noncomputable def bigSidon : Set ℕ := ⋃ k, ((block k : Finset ℕ) : Set ℕ)

private lemma mem_bigSidon {x : ℕ} : x ∈ bigSidon ↔ ∃ k, x ∈ block k := by
  simp [bigSidon]

/-- The core case analysis: if `a` and `c` lie in the top block `K` involved in a relation
`a + b = c + d`, the relation is trivial. -/
private lemma sidon_aux {K kb kd a b c d : ℕ} (ha : a ∈ block K) (hb : b ∈ block kb)
    (hc : c ∈ block K) (hd : d ∈ block kd) (hkb : kb ≤ K) (hkd : kd ≤ K)
    (h : a + b = c + d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases eq_or_lt_of_le hkb with hb1 | hb1 <;> rcases eq_or_lt_of_le hkd with hd1 | hd1
  · -- all four elements lie in the block `K`
    rw [hb1] at hb
    rw [hd1] at hd
    rw [mem_block] at ha hb hc hd
    obtain ⟨sa, hsa, rfl⟩ := ha
    obtain ⟨sb, hsb, rfl⟩ := hb
    obtain ⟨sc, hsc, rfl⟩ := hc
    obtain ⟨sd, hsd, rfl⟩ := hd
    have heq : sa + sb = sc + sd := by omega
    rcases erdosTuranSet_isSidon (blockP K) (blockP_prime K) (blockP_ne_two K)
        sa (Finset.mem_coe.mpr hsa) sc (Finset.mem_coe.mpr hsc)
        sb (Finset.mem_coe.mpr hsb) sd (Finset.mem_coe.mpr hsd) heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  · -- `a`, `b`, `c` in the top block but `d` below: impossible
    exfalso
    rw [hb1] at hb
    have h1 := (block_bounds ha).1
    have h2 := (block_bounds hb).1
    have h3 := (block_bounds hc).2
    have h4 := (block_bounds hd).2
    have h5 := blockN_gap hd1
    have h6 := blockM_def K
    linarith
  · -- `a`, `c`, `d` in the top block but `b` below: impossible
    exfalso
    rw [hd1] at hd
    have h1 := (block_bounds ha).2
    have h2 := (block_bounds hb).2
    have h3 := (block_bounds hc).1
    have h4 := (block_bounds hd).1
    have h5 := blockN_gap hb1
    have h6 := blockM_def K
    linarith
  · -- `a`, `c` in the top block, `b` and `d` below: the difference bound applies
    have hbp : b < blockP K := lt_of_lt_of_le (block_bounds hb).2 (blockM_lt_blockP_of_lt hb1).le
    have hdp : d < blockP K := lt_of_lt_of_le (block_bounds hd).2 (blockM_lt_blockP_of_lt hd1).le
    rw [mem_block] at ha hc
    obtain ⟨sa, hsa, rfl⟩ := ha
    obtain ⟨sc, hsc, rfl⟩ := hc
    have heq : sa + b = sc + d := by omega
    have hsac : sa = sc :=
      erdosTuranSet_close (blockP_prime K).pos hsa hsc (by omega) (by omega)
    subst hsac
    exact Or.inl ⟨rfl, by omega⟩

/-- The union of the blocks is a Sidon set. -/
private lemma bigSidon_isSidon : IsSidon bigSidon := by
  intro a ha c hc b hb d hd h
  obtain ⟨ka, ha⟩ := mem_bigSidon.mp ha
  obtain ⟨kb, hb⟩ := mem_bigSidon.mp hb
  obtain ⟨kc, hc⟩ := mem_bigSidon.mp hc
  obtain ⟨kd, hd⟩ := mem_bigSidon.mp hd
  obtain ⟨K, hka, hkb, hkc, hkd, hatt⟩ :
      ∃ K, ka ≤ K ∧ kb ≤ K ∧ kc ≤ K ∧ kd ≤ K ∧ (ka = K ∨ kb = K ∨ kc = K ∨ kd = K) :=
    ⟨max (max ka kb) (max kc kd), by omega, by omega, by omega, by omega, by omega⟩
  have hleft : ka = K ∨ kb = K := by
    rcases eq_or_lt_of_le hka with hka' | hka'
    · exact Or.inl hka'
    rcases eq_or_lt_of_le hkb with hkb' | hkb'
    · exact Or.inr hkb'
    exfalso
    rcases hatt with h' | h' | h' | h'
    · omega
    · omega
    · subst h'
      have e1 := block_gap hka' ha hc
      have e2 := block_gap hkb' hb hc
      omega
    · subst h'
      have e1 := block_gap hka' ha hd
      have e2 := block_gap hkb' hb hd
      omega
  have hright : kc = K ∨ kd = K := by
    rcases eq_or_lt_of_le hkc with hkc' | hkc'
    · exact Or.inl hkc'
    rcases eq_or_lt_of_le hkd with hkd' | hkd'
    · exact Or.inr hkd'
    exfalso
    rcases hleft with h' | h'
    · subst h'
      have e1 := block_gap hkc' hc ha
      have e2 := block_gap hkd' hd ha
      omega
    · subst h'
      have e1 := block_gap hkc' hc hb
      have e2 := block_gap hkd' hd hb
      omega
  rcases hleft with h1 | h1 <;> rcases hright with h2 | h2
  · rw [h1] at ha; rw [h2] at hc
    exact sidon_aux ha hb hc hd hkb hkd h
  · rw [h1] at ha; rw [h2] at hd
    have h' : a + b = d + c := by omega
    exact (sidon_aux ha hb hd hc hkb hkc h').symm
  · rw [h1] at hb; rw [h2] at hc
    have h' : b + a = c + d := by omega
    rcases sidon_aux hb ha hc hd hka hkd h' with ⟨u, v⟩ | ⟨u, v⟩
    · exact Or.inr ⟨v, u⟩
    · exact Or.inl ⟨v, u⟩
  · rw [h1] at hb; rw [h2] at hd
    have h' : b + a = d + c := by omega
    rcases sidon_aux hb ha hd hc hka hkc h' with ⟨u, v⟩ | ⟨u, v⟩
    · exact Or.inl ⟨v, u⟩
    · exact Or.inr ⟨v, u⟩

/-- The `k`-th block contributes `blockP k` elements below `blockM k`. -/
private lemma count_ge (k : ℕ) :
    blockP k ≤ (bigSidon ∩ Set.Icc 1 (blockM k)).ncard := by
  have hsub : ((block k : Finset ℕ) : Set ℕ) ⊆ bigSidon ∩ Set.Icc 1 (blockM k) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨h1, h2⟩ := block_bounds hx
    have h3 := blockN_ge_one k
    refine ⟨mem_bigSidon.mpr ⟨k, hx⟩, ?_⟩
    rw [Set.mem_Icc]
    omega
  have hfin : (bigSidon ∩ Set.Icc 1 (blockM k)).Finite :=
    Set.Finite.subset (Set.finite_Icc 1 (blockM k)) Set.inter_subset_right
  have h5 := Set.ncard_le_ncard hsub hfin
  rwa [Set.ncard_coe_finset, card_block] at h5

private lemma two_blockP_le (k : ℕ) : 2 * blockP k ≤ blockP (k + 1) := by
  have h1 := blockM_lt_blockP k
  have h2 := blockN_ge k
  have h3 : 1 ≤ blockP k := (blockP_prime k).pos
  have h4 := blockM_def k
  nlinarith

private lemma sum_blockP : ∀ K : ℕ, ∑ k ∈ Finset.range (K + 1), blockP k ≤ 2 * blockP K := by
  intro K
  induction K with
  | zero => rw [Finset.sum_range_one]; omega
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have := two_blockP_le K
      omega

/-- Everything of `bigSidon` below `blockN (K+1)` lies in the first `K + 1` blocks. -/
private lemma count_le (K N : ℕ) (hN : N < blockN (K + 1)) :
    (bigSidon ∩ Set.Icc 1 N).ncard ≤ ∑ k ∈ Finset.range (K + 1), blockP k := by
  have hsub : bigSidon ∩ Set.Icc 1 N ⊆
      (((Finset.range (K + 1)).biUnion block : Finset ℕ) : Set ℕ) := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨j, hj⟩ := mem_bigSidon.mp hx1
    rw [Set.mem_Icc] at hx2
    have hjK : j < K + 1 := by
      rcases Nat.lt_or_ge j (K + 1) with h' | h'
      · exact h'
      · exfalso
        have e1 := (block_bounds hj).1
        have e2 := blockN_mono h'
        omega
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK, hj⟩)
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  refine h1.trans (Finset.card_biUnion_le.trans ?_)
  exact Finset.sum_le_sum fun i _ => le_of_eq (card_block i)

private lemma count_eq_zero {N : ℕ} (hN : N < blockN 0) :
    (bigSidon ∩ Set.Icc 1 N).ncard = 0 := by
  have : bigSidon ∩ Set.Icc 1 N = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx1 hx2
    obtain ⟨j, hj⟩ := mem_bigSidon.mp hx1
    have e1 := (block_bounds hj).1
    have e2 := blockN_mono (Nat.zero_le j)
    omega
  rw [this, Set.ncard_empty]

private lemma count_sq_step (K N : ℕ) (h1 : blockN K ≤ N) (h2 : N < blockN (K + 1)) :
    (bigSidon ∩ Set.Icc 1 N).ncard ^ 2 ≤ 4 * N := by
  have hc : (bigSidon ∩ Set.Icc 1 N).ncard ≤ 2 * blockP K := (count_le K N h2).trans (sum_blockP K)
  have hsq : (bigSidon ∩ Set.Icc 1 N).ncard ^ 2 ≤ (2 * blockP K) ^ 2 := Nat.pow_le_pow_left hc 2
  have hN := blockN_ge K
  have he : (2 * blockP K) ^ 2 = 4 * blockP K ^ 2 := by ring
  linarith

private lemma count_sq_le : ∀ (K N : ℕ), N < blockN (K + 1) →
    (bigSidon ∩ Set.Icc 1 N).ncard ^ 2 ≤ 4 * N := by
  intro K
  induction K with
  | zero =>
      intro N hN
      rcases Nat.lt_or_ge N (blockN 0) with h | h
      · rw [count_eq_zero h]; omega
      · exact count_sq_step 0 N h hN
  | succ K ih =>
      intro N hN
      rcases Nat.lt_or_ge N (blockN (K + 1)) with h | h
      · exact ih N h
      · exact count_sq_step (K + 1) N h hN

private lemma count_sq_le_all (N : ℕ) : (bigSidon ∩ Set.Icc 1 N).ncard ^ 2 ≤ 4 * N :=
  count_sq_le N N (lt_of_lt_of_le (Nat.lt_succ_self N) (le_blockN (N + 1)))

/-- The normalized partial densities of `bigSidon` are uniformly bounded. -/
private lemma density_le_two (N : ℕ) : sqrtPartialDensity bigSidon N ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [sqrtPartialDensity]
  · have hcast : (((bigSidon ∩ Set.Icc 1 N).ncard : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by
      exact_mod_cast count_sq_le_all N
    have hsq : (((bigSidon ∩ Set.Icc 1 N).ncard : ℝ) / 2) ^ 2 ≤ (N : ℝ) := by nlinarith
    have hle : ((bigSidon ∩ Set.Icc 1 N).ncard : ℝ) / 2 ≤ Real.sqrt N :=
      (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
    have hpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [sqrtPartialDensity, div_le_iff₀ hpos]
    linarith

private lemma blockM_le_sq : ∀ k : ℕ, blockM k ≤ (2 * blockP k + 1) ^ 2
  | 0 => by rw [blockM_def, blockN_zero, blockP_zero]; norm_num
  | k + 1 => by
      have h1 := blockM_lt_blockP k
      have h2 := blockM_def (k + 1)
      have h3 := blockN_succ k
      nlinarith

/-- At `N = blockM k` the normalized density is at least `p / (2p + 1)` with `p = blockP k`. -/
private lemma density_at (k : ℕ) :
    (blockP k : ℝ) / (2 * blockP k + 1) ≤ sqrtPartialDensity bigSidon (blockM k) := by
  have hMpos : 0 < blockM k := by
    have h1 := blockN_ge_one k
    have h2 := blockN_le_blockM k
    omega
  have hsqrt_le : Real.sqrt (blockM k) ≤ 2 * (blockP k : ℝ) + 1 := by
    have h1 : (blockM k : ℝ) ≤ ((2 * blockP k + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast blockM_le_sq k
    calc Real.sqrt (blockM k) ≤ Real.sqrt (((2 * blockP k + 1 : ℕ) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = ((2 * blockP k + 1 : ℕ) : ℝ) := Real.sqrt_sq (by positivity)
      _ = 2 * (blockP k : ℝ) + 1 := by push_cast; ring
  have hsqrt_pos : 0 < Real.sqrt (blockM k) := Real.sqrt_pos.mpr (by exact_mod_cast hMpos)
  rw [sqrtPartialDensity]
  refine div_le_div₀ (by positivity) ?_ hsqrt_pos hsqrt_le
  exact_mod_cast count_ge k

/-- **Erdős's lower bound (Erdős #329).**  There is a Sidon set `A ⊆ ℕ` with
`limsup_{N→∞} |A ∩ [1,N]| / √N ≥ 1/2`; exactly the formal-conjectures statement
`erdos_329.variants.lower_bound`.  The value of the supremum is open and not claimed. -/
theorem erdos_329_lower_bound : ∃ (A : Set ℕ), IsSidon A ∧ sidonUpperDensity A ≥ 1/2 := by
  refine ⟨bigSidon, bigSidon_isSidon, ?_⟩
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N => sqrtPartialDensity bigSidon N) :=
    Filter.isBoundedUnder_of ⟨2, fun N => density_le_two N⟩
  rw [ge_iff_le, sidonUpperDensity]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfreq : ∃ᶠ N in Filter.atTop, (1 / 2 - ε : ℝ) ≤ sqrtPartialDensity bigSidon N := by
    rw [Filter.frequently_atTop]
    intro m
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / ε)
    refine ⟨blockM (max m n), le_trans (le_max_left m n) (le_blockM _), ?_⟩
    have h1 := density_at (max m n)
    have hx : (1 / ε : ℝ) ≤ (blockP (max m n) : ℝ) := by
      refine hn.trans ?_
      exact_mod_cast le_trans (le_max_right m n) (le_blockP _)
    have h3 : 1 ≤ (blockP (max m n) : ℝ) * ε := (div_le_iff₀ hε).mp hx
    have h2 : (1 / 2 - ε : ℝ) ≤ (blockP (max m n) : ℝ) / (2 * blockP (max m n) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hfin := Filter.le_limsup_of_frequently_le hfreq hbdd
  linarith
