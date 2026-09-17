import Erdos381Lower.Defs

/-!
# Erdős #381 (JSP-000315): from the gap theorem to the counting lower bound

This module carries out §4 of the proof digest.  Erdős's gap theorem — for every large highly
composite `n` the next highly composite number is smaller than `n(1 + (log n)^{-c})` — is taken
here as a hypothesis, in the frozen form `hgap` below; module 5 supplies it.

Given the gap, the chain `b, nextHC b, nextHC (nextHC b), …` of successive highly composite
numbers has logarithms growing by at most `(log n)^{-c}` per step, so `(log ·)^{1+c}` grows by
at most `3` per step (§4.2).  Every chain member up to `N` is counted by `Q N` (§4.3), whence
`Q N ≥ ((log N)^{1+c} - C₀)/3` (§4.4) and finally `(log N)^{1+c/2} ≤ Q N` (§4.5).
-/

namespace Erdos381Lower

open Erdos381 Filter

/-! ## Highly composite numbers are unbounded -/

/-- There is a highly composite number above every bound: if `A` bounds `tau` on `[1, N]`, the
least `m` with `A < tau m` is a strict record for `tau`, and it must exceed `N`. -/
theorem exists_highlyComposite_gt (N : ℕ) : ∃ m : ℕ, N < m ∧ HighlyComposite m := by
  obtain ⟨A, hAle⟩ : ∃ A : ℕ, ∀ j : ℕ, 0 < j → j ≤ N → tau j ≤ A :=
    ⟨(Finset.Icc 1 N).sup tau, fun j hj hjN ↦ Finset.le_sup (Finset.mem_Icc.mpr ⟨hj, hjN⟩)⟩
  have hex : ∃ m : ℕ, 0 < m ∧ A < tau m := by
    refine ⟨2 ^ A, by positivity, ?_⟩
    have h2 : ArithmeticFunction.sigma 0 (2 ^ A) = A + 1 :=
      ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two
    rw [ArithmeticFunction.sigma_zero_apply] at h2
    simp only [tau]
    omega
  have hspec := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, hspec.1, ?_⟩
  · rcases Nat.lt_or_ge N (Nat.find hex) with h | h
    · exact h
    · exact absurd (hAle _ hspec.1 h) (not_le.mpr hspec.2)
  · intro m hm hmlt
    have hmin : tau m ≤ A := by
      by_contra hcon
      exact Nat.find_min hex hmlt ⟨hm, not_le.mp hcon⟩
    exact lt_of_le_of_lt hmin hspec.2

/-- The least highly composite number strictly above `n`. -/
noncomputable def nextHC (n : ℕ) : ℕ := Nat.find (exists_highlyComposite_gt n)

/-- `nextHC n` lies strictly above `n`. -/
theorem lt_nextHC (n : ℕ) : n < nextHC n := (Nat.find_spec (exists_highlyComposite_gt n)).1

/-- `nextHC n` is highly composite. -/
theorem highlyComposite_nextHC (n : ℕ) : HighlyComposite (nextHC n) :=
  (Nat.find_spec (exists_highlyComposite_gt n)).2

/-- Minimality of `nextHC`: no highly composite number lies in the open interval `(n, nextHC n)`. -/
theorem nextHC_le {n m : ℕ} (hnm : n < m) (hm : HighlyComposite m) : nextHC n ≤ m :=
  Nat.find_min' (exists_highlyComposite_gt n) ⟨hnm, hm⟩

/-- A highly composite number above `N` is counted by `Q` beyond everything counted at `N`. -/
theorem Q_lt_Q_of_highlyComposite {N m : ℕ} (hm : HighlyComposite m) (hNm : N < m) :
    Q N < Q m := by
  simp only [Q]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨m, ?_, ?_⟩)
  · intro x hx
    rw [mem_counted_iff] at hx ⊢
    exact ⟨hx.1, hx.2.1.trans hNm.le, hx.2.2⟩
  · rw [mem_counted_iff]
    exact ⟨hm.1, le_rfl, hm⟩
  · rw [mem_counted_iff]
    rintro ⟨-, h, -⟩
    omega

/-- Passing to the next highly composite number increases the counting function by exactly one. -/
theorem Q_nextHC (n : ℕ) : Q (nextHC n) = Q n + 1 := by
  have hkey : (Finset.Icc 1 (nextHC n)).filter HighlyComposite
      = insert (nextHC n) ((Finset.Icc 1 n).filter HighlyComposite) := by
    ext m
    simp only [Finset.mem_insert, mem_counted_iff]
    constructor
    · rintro ⟨hm1, hm2, hm3⟩
      rcases Nat.lt_or_ge n m with h | h
      · exact Or.inl (le_antisymm hm2 (nextHC_le h hm3))
      · exact Or.inr ⟨hm1, h, hm3⟩
    · rintro (rfl | ⟨hm1, hm2, hm3⟩)
      · exact ⟨(highlyComposite_nextHC n).1, le_rfl, highlyComposite_nextHC n⟩
      · exact ⟨hm1, hm2.trans (lt_nextHC n).le, hm3⟩
  have hnot : nextHC n ∉ (Finset.Icc 1 n).filter HighlyComposite := by
    intro h
    rw [mem_counted_iff] at h
    exact absurd h.2.1 (not_le.mpr (lt_nextHC n))
  simp only [Q, hkey, Finset.card_insert_of_notMem hnot]

/-! ## The chain of successive highly composite numbers -/

/-- The `k`-th highly composite number at or above `b`, for `b` highly composite. -/
noncomputable def hcChain (b k : ℕ) : ℕ := nextHC^[k] b

/-- The chain starts at its base. -/
theorem hcChain_zero (b : ℕ) : hcChain b 0 = b := rfl

/-- Each chain member is the next highly composite number after its predecessor. -/
theorem hcChain_succ (b k : ℕ) : hcChain b (k + 1) = nextHC (hcChain b k) :=
  Function.iterate_succ_apply' nextHC k b

/-- Every member of the chain based at a highly composite `b` is highly composite. -/
theorem highlyComposite_hcChain {b : ℕ} (hb : HighlyComposite b) (k : ℕ) :
    HighlyComposite (hcChain b k) := by
  induction k with
  | zero => exact hb
  | succ k _ =>
    rw [hcChain_succ]
    exact highlyComposite_nextHC _

/-- The chain never drops below its base. -/
theorem le_hcChain (b k : ℕ) : b ≤ hcChain b k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [hcChain_succ]
    exact ih.trans (lt_nextHC _).le

/-- The chain enumerates the highly composite numbers: `Q` increases by one along it. -/
theorem Q_hcChain (b k : ℕ) : Q (hcChain b k) = Q b + k := by
  induction k with
  | zero => simp [hcChain_zero]
  | succ k ih =>
    rw [hcChain_succ, Q_nextHC, ih]
    omega

/-- Locating `N` in the chain: the `(Q N - Q b)`-th chain member is the last one `≤ N`. -/
theorem hcChain_le_and_lt {b N : ℕ} (hb : HighlyComposite b) (hbN : b ≤ N) :
    hcChain b (Q N - Q b) ≤ N ∧ N < hcChain b (Q N - Q b + 1) := by
  have hQb : Q b ≤ Q N := Q_mono hbN
  have hk : Q (hcChain b (Q N - Q b)) = Q N := by
    rw [Q_hcChain]
    omega
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge N (hcChain b (Q N - Q b)) with h | h
    · have h2 := Q_lt_Q_of_highlyComposite (highlyComposite_hcChain hb (Q N - Q b)) h
      omega
    · exact h
  · rcases Nat.lt_or_ge N (hcChain b (Q N - Q b + 1)) with h | h
    · exact h
    · have h2 : Q (hcChain b (Q N - Q b + 1)) ≤ Q N := Q_mono h
      rw [Q_hcChain] at h2
      omega

/-! ## The telescoping estimate -/

/-- One step of the telescoping estimate (digest §4.2): if `b` exceeds `a ≥ 1` by at most
`a ^ (-c)` with `0 < c ≤ 1`, then `b ^ (1 + c)` exceeds `a ^ (1 + c)` by at most `3`. -/
theorem rpow_add_one_step {a b c : ℝ} (ha : 1 ≤ a) (hc0 : 0 < c) (hc1 : c ≤ 1) (hab : a ≤ b)
    (hb : b ≤ a + a ^ (-c)) : b ^ (1 + c) ≤ a ^ (1 + c) + 3 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hu0 : (0 : ℝ) < a ^ (-c - 1) := Real.rpow_pos_of_pos ha0 _
  have hu1 : a ^ (-c - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have hfac : a + a ^ (-c) = a * (1 + a ^ (-c - 1)) := by
    have key : a ^ ((1 : ℝ) + (-c - 1)) = a * a ^ (-c - 1) := by
      rw [Real.rpow_add ha0, Real.rpow_one]
    rw [show ((1 : ℝ) + (-c - 1)) = -c by ring] at key
    rw [key, mul_add, mul_one]
  have h1 : b ^ (1 + c) ≤ (a * (1 + a ^ (-c - 1))) ^ (1 + c) :=
    Real.rpow_le_rpow (by linarith) (by rw [← hfac]; exact hb) (by linarith)
  have h2 : (a * (1 + a ^ (-c - 1))) ^ (1 + c)
      = a ^ (1 + c) * (1 + a ^ (-c - 1)) ^ (1 + c) := Real.mul_rpow ha0.le (by linarith)
  have h3 : (1 + a ^ (-c - 1)) ^ (1 + c) ≤ (1 + a ^ (-c - 1)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h4 : (1 + a ^ (-c - 1)) ^ (2 : ℝ)
      = 1 + 2 * a ^ (-c - 1) + a ^ (-c - 1) * a ^ (-c - 1) := by
    rw [Real.rpow_two]
    ring
  have hua : a ^ (-c - 1) * a ^ (1 + c) = 1 := by
    rw [← Real.rpow_add ha0, show (-c - 1 + (1 + c) : ℝ) = 0 by ring, Real.rpow_zero]
  have hnn : (0 : ℝ) ≤ a ^ (1 + c) := Real.rpow_nonneg ha0.le _
  set u : ℝ := a ^ (-c - 1) with hudef
  set A : ℝ := a ^ (1 + c) with hAdef
  clear_value u A
  calc b ^ (1 + c) ≤ A * (1 + u) ^ (1 + c) := by rw [← h2]; exact h1
    _ ≤ A * (1 + 2 * u + u * u) := by rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hnn
    _ = A + 2 * (u * A) + u * (u * A) := by ring
    _ = A + 2 + u := by rw [hua]; ring
    _ ≤ A + 3 := by linarith

/-- Telescoping (digest §4.2): a sequence bounded below by `1` whose increments are at most
`L k ^ (-c)` satisfies `L k ^ (1 + c) ≤ L 0 ^ (1 + c) + 3 * k`. -/
theorem rpow_chain_bound {L : ℕ → ℝ} {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hL1 : ∀ k, 1 ≤ L k)
    (hmono : ∀ k, L k ≤ L (k + 1)) (hstep : ∀ k, L (k + 1) ≤ L k + L k ^ (-c)) (k : ℕ) :
    L k ^ (1 + c) ≤ L 0 ^ (1 + c) + 3 * k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := rpow_add_one_step (hL1 k) hc0 hc1 (hmono k) (hstep k)
    push_cast
    linarith

/-! ## The counting lower bound -/

/-- Erdős 1944 (digest §4): the gap theorem implies `Q N ≥ (log N)^{1+c}` for all large `N`. -/
theorem erdos381_lower_of_gap
    (hgap : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, Erdos381.HighlyComposite n →
      ∃ n' : ℕ, Erdos381.HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop, Real.log N ^ (1 + c) ≤ (Erdos381.Q N : ℝ) := by
  obtain ⟨c₀, hc₀, hev⟩ := hgap
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min c₀ 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact lt_min hc₀ one_pos
  have hc1 : c ≤ 1 := by rw [hcdef]; exact min_le_right _ _
  have hcc : c ≤ c₀ := by rw [hcdef]; exact min_le_left _ _
  have hev' : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n ∧ (HighlyComposite n →
      ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c)) := by
    filter_upwards [hev, tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn hlog
    refine ⟨hlog, fun hHC ↦ ?_⟩
    obtain ⟨n', hn'HC, hlt, hbd⟩ := hn hHC
    refine ⟨n', hn'HC, hlt, lt_of_lt_of_le hbd ?_⟩
    have hmono : Real.log n ^ (-c₀) ≤ Real.log n ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
    linarith [mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) n)]
  rw [eventually_atTop] at hev'
  obtain ⟨N₁, hN₁⟩ := hev'
  obtain ⟨b, hbgt, hbHC⟩ := exists_highlyComposite_gt N₁
  have hmge : ∀ k : ℕ, N₁ ≤ hcChain b k := fun k ↦ hbgt.le.trans (le_hcChain b k)
  have hmHC : ∀ k : ℕ, HighlyComposite (hcChain b k) := highlyComposite_hcChain hbHC
  have hL1 : ∀ k : ℕ, (1 : ℝ) ≤ Real.log (hcChain b k : ℝ) := fun k ↦ (hN₁ _ (hmge k)).1
  have hmono : ∀ k : ℕ, Real.log (hcChain b k : ℝ) ≤ Real.log (hcChain b (k + 1) : ℝ) := by
    intro k
    have hle : hcChain b k ≤ hcChain b (k + 1) := by
      rw [hcChain_succ]
      exact (lt_nextHC _).le
    exact Real.log_le_log (by exact_mod_cast (hmHC k).1) (by exact_mod_cast hle)
  have hstep : ∀ k : ℕ, Real.log (hcChain b (k + 1) : ℝ)
      ≤ Real.log (hcChain b k : ℝ) + Real.log (hcChain b k : ℝ) ^ (-c) := by
    intro k
    obtain ⟨n', hn'HC, hlt, hbd⟩ := (hN₁ _ (hmge k)).2 (hmHC k)
    have hle : (hcChain b (k + 1) : ℝ) ≤ (n' : ℝ) := by
      have : hcChain b (k + 1) ≤ n' := by
        rw [hcChain_succ]
        exact nextHC_le hlt hn'HC
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (hcChain b k : ℝ) := by exact_mod_cast (hmHC k).1
    have hrp : (0 : ℝ) < Real.log (hcChain b k : ℝ) ^ (-c) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (hL1 k)) _
    have hfac : (0 : ℝ) < 1 + Real.log (hcChain b k : ℝ) ^ (-c) := by linarith
    have hexp : (hcChain b k : ℝ) * (1 + Real.log (hcChain b k : ℝ) ^ (-c))
        = (hcChain b k : ℝ) + (hcChain b k : ℝ) * Real.log (hcChain b k : ℝ) ^ (-c) := by ring
    have hprod : (hcChain b (k + 1) : ℝ)
        ≤ (hcChain b k : ℝ) * (1 + Real.log (hcChain b k : ℝ) ^ (-c)) := by
      rw [hexp]
      linarith
    have hlogle := Real.log_le_log (by exact_mod_cast (hmHC (k + 1)).1 : (0:ℝ) < _) hprod
    rw [Real.log_mul (ne_of_gt hmpos) (ne_of_gt hfac)] at hlogle
    linarith [Real.log_le_sub_one_of_pos hfac]
  have hchain : ∀ k : ℕ, Real.log (hcChain b k : ℝ) ^ (1 + c)
      ≤ Real.log (b : ℝ) ^ (1 + c) + 3 * k := by
    intro k
    have h := rpow_chain_bound (L := fun j : ℕ ↦ Real.log (hcChain b j : ℝ)) hc0 hc1 hL1 hmono
      hstep k
    simpa [hcChain_zero] using h
  have hlb : (1 : ℝ) ≤ Real.log (b : ℝ) := by simpa [hcChain_zero] using hL1 0
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, C = Real.log (b : ℝ) ^ (1 + c) + 3 := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    have := Real.rpow_nonneg (le_trans zero_le_one hlb) (1 + c)
    linarith
  refine ⟨c / 2, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop b,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (max 1 ((3 + C₀) ^ (2 / c))))]
    with N hNb hNR
  have hLN1 : (1 : ℝ) ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hNR
  have hLN2 : ((3 + C₀) ^ (2 / c) : ℝ) ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hNR
  have hkey : 3 + C₀ ≤ Real.log (N : ℝ) ^ (c / 2) := by
    have h1 : ((3 + C₀) ^ (2 / c)) ^ (c / 2) ≤ Real.log (N : ℝ) ^ (c / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hLN2 (by linarith)
    rwa [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 3 + C₀),
      show 2 / c * (c / 2) = 1 by field_simp, Real.rpow_one] at h1
  have hloc := (hcChain_le_and_lt hbHC hNb).2
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le hbHC.1 hNb
    exact_mod_cast this
  have hlogN : Real.log (N : ℝ) ≤ Real.log (hcChain b (Q N - Q b + 1) : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hloc.le)
  have hpow : Real.log (N : ℝ) ^ (1 + c)
      ≤ Real.log (hcChain b (Q N - Q b + 1) : ℝ) ^ (1 + c) :=
    Real.rpow_le_rpow (by linarith) hlogN (by linarith)
  have hb2 := hchain (Q N - Q b + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hb2
  have hkQ : ((Q N - Q b : ℕ) : ℝ) ≤ (Q N : ℝ) := by exact_mod_cast Nat.sub_le _ _
  have hmain : Real.log (N : ℝ) ^ (1 + c) ≤ C₀ + 3 * (Q N : ℝ) := by
    rw [hC₀]
    linarith
  have hone : (1 : ℝ) ≤ Real.log (N : ℝ) ^ (1 + c / 2) := Real.one_le_rpow hLN1 (by linarith)
  have hsplit : Real.log (N : ℝ) ^ (1 + c / 2) * Real.log (N : ℝ) ^ (c / 2)
      = Real.log (N : ℝ) ^ (1 + c) := by
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < Real.log (N : ℝ))]
    congr 1
    ring
  rw [← hsplit] at hmain
  have h5 : Real.log (N : ℝ) ^ (1 + c / 2) * (3 + C₀)
      ≤ Real.log (N : ℝ) ^ (1 + c / 2) * Real.log (N : ℝ) ^ (c / 2) :=
    mul_le_mul_of_nonneg_left hkey (le_trans zero_le_one hone)
  have h6 : C₀ ≤ Real.log (N : ℝ) ^ (1 + c / 2) * C₀ := le_mul_of_one_le_left hC₀0 hone
  linarith

/-- The `IsBigO` packaging of the counting lower bound, in plby's idiom. -/
theorem erdos381_lower_isBigO_of_gap
    (hgap : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, Erdos381.HighlyComposite n →
      ∃ n' : ℕ, Erdos381.HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c)) :
    ∃ c : ℝ, 0 < c ∧ (fun N : ℕ ↦ Real.log (N : ℝ) ^ (1 + c))
      =O[Filter.atTop] (fun N : ℕ ↦ (Erdos381.Q N : ℝ)) := by
  obtain ⟨c, hc, hbnd⟩ := erdos381_lower_of_gap hgap
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound 1 ?_⟩
  filter_upwards [hbnd, tendsto_log_nat_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
    with N hN hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Q N : ℝ))]
  exact hN

/-- The two-sided growth statement: Erdős's lower bound (conditional on the gap theorem) together
with Nicolas's polynomial upper bound, proved unconditionally in plby/lean-proofs. -/
theorem erdos381_two_sided_of_gap
    (hgap : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, Erdos381.HighlyComposite n →
      ∃ n' : ℕ, Erdos381.HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c)) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
        Real.log N ^ (1 + c) ≤ (Erdos381.Q N : ℝ)) ∧
      Erdos381.NicolasPolynomialUpperBound :=
  ⟨erdos381_lower_of_gap hgap, nicolasPolynomialUpperBound⟩

end Erdos381Lower
