import Jsp990.Defs

/-!
# JSP-000990 / Erdős #1185 — the doubly exponential sequence and the phase lemma
-/

open Finset

namespace Erdos1185

/-- `b 0 = 1`, `b (l+1) = 256 * b l * b l`: a doubly exponential sequence of powers of two. -/
def b : ℕ → ℕ
  | 0 => 1
  | l + 1 => 256 * b l * b l

/-- The ratio `b (l+1) / b l`. -/
def R (l : ℕ) : ℕ := 256 * b l

/-- `T m = ∑_{l < m} (b (m-1) / b l)^2`. -/
def T (m : ℕ) : ℕ := ∑ l ∈ range m, (b (m - 1) / b l) ^ 2

/-- The modulus `L m = 8 * b (m-1)^2`. -/
def L (m : ℕ) : ℕ := 8 * b (m - 1) * b (m - 1)

@[simp] theorem b_zero : b 0 = 1 := rfl

@[simp] theorem b_succ_eq (l : ℕ) : b (l + 1) = 256 * b l * b l := rfl

theorem b_pos (l : ℕ) : 0 < b l := by
  induction l with
  | zero => norm_num
  | succ n ih => simp only [b_succ_eq]; positivity

theorem one_le_b (l : ℕ) : 1 ≤ b l := b_pos l

theorem b_one_le (l : ℕ) : 1 ≤ b l := b_pos l

theorem b_succ (l : ℕ) : b (l + 1) = R l * b l := by
  simp [R, b_succ_eq, mul_assoc]

theorem two_pow_b (l : ℕ) : ∃ e : ℕ, b l = 2 ^ e := by
  induction l with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨8 + e + e, by rw [b_succ_eq, he]; ring⟩

theorem b_lt_b_succ (l : ℕ) : b l < b (l + 1) := by
  have h := b_pos l
  calc b l = 1 * b l := (one_mul _).symm
    _ < 256 * b l * b l := by
        have : 1 * b l < 256 * b l * b l := by nlinarith
        exact this
    _ = b (l + 1) := (b_succ_eq l).symm

theorem b_strictMono : StrictMono b := strictMono_nat_of_lt_succ b_lt_b_succ

theorem b_le_b {l l' : ℕ} (h : l ≤ l') : b l ≤ b l' := b_strictMono.monotone h

theorem b_lt_b {l l' : ℕ} (h : l < l') : b l < b l' := b_strictMono h

theorem b_dvd_b {l l' : ℕ} (h : l ≤ l') : b l ∣ b l' := by
  induction l' with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
      · exact dvd_trans (ih (Nat.lt_succ_iff.mp h')) ⟨256 * b n, by rw [b_succ_eq]; ring⟩
      · subst h'; exact dvd_rfl

/-- `ratio_dvd`: `b j ∣ b i` whenever `j ≤ i`. -/
theorem ratio_dvd {j i : ℕ} (h : j ≤ i) : b j ∣ b i := b_dvd_b h

theorem R_even (l : ℕ) : 2 ∣ R l := ⟨128 * b l, by simp [R]; ring⟩

theorem R_ge (l : ℕ) : 256 ≤ R l := by
  have := one_le_b l
  simpa [R] using Nat.mul_le_mul_left 256 this

theorem two_mul_b_dvd_R (l : ℕ) : 2 * b l ∣ R l := ⟨128, by simp [R]; ring⟩

/-- The ratio `b i / b l` is divisible by `R l` when `l < i`. -/
theorem R_dvd_ratio {l i : ℕ} (h : l < i) : R l ∣ b i / b l := by
  obtain ⟨k, hk⟩ : b (l + 1) ∣ b i := b_dvd_b h
  refine ⟨k, ?_⟩
  rw [hk, b_succ]
  rw [show R l * b l * k = (R l * k) * b l by ring, Nat.mul_div_cancel _ (b_pos l)]

theorem two_mul_b_dvd_ratio {l i : ℕ} (h : l < i) : 2 * b l ∣ b i / b l :=
  dvd_trans (two_mul_b_dvd_R l) (R_dvd_ratio h)

theorem ratio_pos {j i : ℕ} (h : j ≤ i) : 0 < b i / b j :=
  Nat.div_pos (b_le_b h) (b_pos j)

theorem b_div_b_even {j i : ℕ} (h : j < i) : 2 ∣ b i / b j :=
  dvd_trans ⟨b j, rfl⟩ (two_mul_b_dvd_ratio h)

/-- Alias of `b_div_b_even`: the ratio `b i / b j` is even for `j < i`. -/
theorem ratio_even {j i : ℕ} (h : j < i) : 2 ∣ b i / b j := b_div_b_even h

theorem b_div_b_ge {j i : ℕ} (h : j < i) : 256 ≤ b i / b j :=
  le_trans (R_ge j) (Nat.le_of_dvd (ratio_pos h.le) (R_dvd_ratio h))

theorem b_div_b_mul {j i : ℕ} (h : j ≤ i) : b i / b j * b j = b i :=
  Nat.div_mul_cancel (b_dvd_b h)

/-- `2 * (b l / b j) ∣ b i / b l` for `j < l < i`. -/
theorem two_mul_dvd_ratio {j l i : ℕ} (hjl : j < l) (hli : l < i) :
    2 * (b l / b j) ∣ b i / b l := by
  refine dvd_trans (mul_dvd_mul_left 2 ?_) (two_mul_b_dvd_ratio hli)
  exact ⟨b j, (b_div_b_mul hjl.le).symm⟩


/-! ### Arithmetic helpers -/

/-- Swapping an exact division between the two factors of a product. -/
theorem mul_div_swap {a x y : ℕ} (hx : a ∣ x) (hy : a ∣ y) : x * (y / a) = x / a * y := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    simp
  · obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    rw [Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel_left _ ha]
    ring

/-- Odd squares are `1` mod `8`. -/
theorem odd_sq_eight (c : ℕ) : ∃ q : ℕ, (2 * c + 1) ^ 2 = 8 * q + 1 := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self c
  refine ⟨t, ?_⟩
  have h : (2 * c + 1) ^ 2 = 4 * (c * (c + 1)) + 1 := by ring
  rw [h, ht]; ring

/-- A geometrically decaying sum of naturals is at most twice its first term. -/
theorem geom_sum_le : ∀ (n : ℕ) (f : ℕ → ℕ), (∀ l, 2 * f (l + 1) ≤ f l) →
    ∑ l ∈ range n, f l ≤ 2 * f 0 := by
  intro n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
      intro f hf
      have h := ih (fun l => f (l + 1)) (fun l => hf (l + 1))
      have h0 := hf 0
      rw [Finset.sum_range_succ']
      omega

/-- Splitting a sum into a multiple of `c` plus a remainder sum. -/
theorem sum_split (c : ℕ) (f g : ℕ → ℕ) (s : Finset ℕ) :
    (∀ l ∈ s, ∃ k, f l = c * k + g l) → ∃ K, ∑ l ∈ s, f l = c * K + ∑ l ∈ s, g l := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp⟩
  | insert a s ha ih =>
      intro h
      obtain ⟨k, hk⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨K, hK⟩ := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
      refine ⟨k + K, ?_⟩
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hk, hK]
      ring

/-- The scaled ratios `bm / b l` decay by a factor of at least `256` at each step. -/
theorem M_step (bm l : ℕ) : 256 * (bm / b (l + 1)) ≤ bm / b l := by
  have hb : b (l + 1) = b l * (256 * b l) := by rw [b_succ_eq]; ring
  rw [hb, ← Nat.div_div_eq_div_mul]
  have h1 : 256 * b l * (bm / b l / (256 * b l)) ≤ bm / b l := by
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  have h2 : 256 * (bm / b l / (256 * b l)) ≤ 256 * b l * (bm / b l / (256 * b l)) := by
    apply Nat.mul_le_mul_right
    have := one_le_b l
    nlinarith
  omega

/-- Geometric tail bound: a tail of terms `2 * (x * (bm / b l))^2` starting at `a+1`. -/
theorem small_tail {bm x a n : ℕ} (hx : 256 * (x * (bm / b (a + 1))) ≤ bm) :
    ∑ l ∈ Ico (a + 1) n, 2 * (x * (bm / b l)) ^ 2 ≤ bm * bm := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hdec : ∀ t : ℕ, 2 * (2 * (x * (bm / b (a + 1 + (t + 1)))) ^ 2)
      ≤ 2 * (x * (bm / b (a + 1 + t))) ^ 2 := by
    intro t
    have h := M_step bm (a + 1 + t)
    have h' : 256 * (x * (bm / b (a + 1 + t + 1))) ≤ x * (bm / b (a + 1 + t)) := by
      calc 256 * (x * (bm / b (a + 1 + t + 1))) = x * (256 * (bm / b (a + 1 + t + 1))) := by ring
        _ ≤ x * (bm / b (a + 1 + t)) := Nat.mul_le_mul_left _ h
    have hstep : a + 1 + (t + 1) = a + 1 + t + 1 := by omega
    rw [hstep]
    nlinarith [h', Nat.zero_le (x * (bm / b (a + 1 + t + 1)))]
  have hg := geom_sum_le (n - (a + 1)) (fun t => 2 * (x * (bm / b (a + 1 + t))) ^ 2) hdec
  simp only [Nat.add_zero] at hg
  have hfin : 2 * (2 * (x * (bm / b (a + 1))) ^ 2) ≤ bm * bm := by
    nlinarith [hx, Nat.zero_le (x * (bm / b (a + 1)))]
  omega


/-! ### `T` and `L` -/

theorem T_odd (m : ℕ) (hm : 1 ≤ m) : T m % 2 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hsum : 2 ∣ ∑ l ∈ range n, (b n / b l) ^ 2 := by
    refine Finset.dvd_sum ?_
    intro l hl
    exact dvd_pow (b_div_b_even (Finset.mem_range.mp hl)) (by norm_num)
  have hself : b n / b n = 1 := Nat.div_self (b_pos n)
  have : T (n + 1) = (∑ l ∈ range n, (b n / b l) ^ 2) + 1 := by
    simp only [T, Nat.add_sub_cancel, Finset.sum_range_succ, hself, one_pow]
  obtain ⟨k, hk⟩ := hsum
  omega

theorem L_eq (m : ℕ) : L m = 8 * b (m - 1) * b (m - 1) := rfl

theorem L_pos (m : ℕ) : 0 < L m := by
  have := b_pos (m - 1); simp only [L]; positivity

theorem eight_dvd_L (m : ℕ) : 8 ∣ L m := ⟨b (m - 1) * b (m - 1), by rw [L_eq]; ring⟩

theorem L_div_eight (m : ℕ) : L m / 8 = b (m - 1) * b (m - 1) := by
  rw [L_eq, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]

theorem L_div_four (m : ℕ) : L m / 4 = 2 * (b (m - 1) * b (m - 1)) := by
  rw [L_eq, show 8 * b (m - 1) * b (m - 1) = 4 * (2 * (b (m - 1) * b (m - 1))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]

theorem L_div_two (m : ℕ) : L m / 2 = 4 * (b (m - 1) * b (m - 1)) := by
  rw [L_eq, show 8 * b (m - 1) * b (m - 1) = 2 * (4 * (b (m - 1) * b (m - 1))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem seven_L_div_eight (m : ℕ) : 7 * L m / 8 = 7 * (b (m - 1) * b (m - 1)) := by
  rw [L_eq, show 7 * (8 * b (m - 1) * b (m - 1)) = 8 * (7 * (b (m - 1) * b (m - 1))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]

/-! ### The individual terms of `2 d² T` -/

/-- Terms with `l < j` are divisible by `L`. -/
theorem term_lt_j {bm i j l : ℕ} (hlj : l < j) (hji : j < i) (hl : b l ∣ bm) :
    ∃ k, 2 * (b i - b j) ^ 2 * (bm / b l) ^ 2 = 8 * bm * bm * k := by
  have hli : l < i := hlj.trans hji
  have h1 : b i * (bm / b l) = b i / b l * bm := mul_div_swap (b_dvd_b hli.le) hl
  have h2 : b j * (bm / b l) = b j / b l * bm := mul_div_swap (b_dvd_b hlj.le) hl
  obtain ⟨a1, ha1⟩ := b_div_b_even hli
  obtain ⟨a2, ha2⟩ := b_div_b_even hlj
  have hmono : b j / b l ≤ b i / b l := Nat.div_le_div_right (b_le_b hji.le)
  refine ⟨(a1 - a2) ^ 2, ?_⟩
  have hsub : (b i - b j) * (bm / b l) = 2 * (a1 - a2) * bm := by
    rw [Nat.sub_mul, h1, h2, ha1, ha2, ← Nat.sub_mul]
    congr 1
    omega
  calc 2 * (b i - b j) ^ 2 * (bm / b l) ^ 2 = 2 * ((b i - b j) * (bm / b l)) ^ 2 := by ring
    _ = 2 * (2 * (a1 - a2) * bm) ^ 2 := by rw [hsub]
    _ = 8 * bm * bm * (a1 - a2) ^ 2 := by ring

/-- The term at `l = j` is `L * (2q) + L/4`. -/
theorem term_eq_j {bm i j : ℕ} (hji : j < i) (hj : b j ∣ bm) :
    ∃ q, 2 * (b i - b j) ^ 2 * (bm / b j) ^ 2 = 8 * bm * bm * (2 * q) + 2 * bm * bm := by
  have h1 : b i * (bm / b j) = b i / b j * bm := mul_div_swap (b_dvd_b hji.le) hj
  have h2 : b j * (bm / b j) = bm := Nat.mul_div_cancel' hj
  obtain ⟨s, hs⟩ := b_div_b_even hji
  have hge : 256 ≤ b i / b j := b_div_b_ge hji
  obtain ⟨q, hq⟩ := odd_sq_eight (s - 1)
  refine ⟨q, ?_⟩
  have hsub : (b i - b j) * (bm / b j) = (2 * (s - 1) + 1) * bm := by
    rw [Nat.sub_mul, h1, h2, hs]
    refine Nat.sub_eq_of_eq_add ?_
    have hss : 2 * s = 2 * (s - 1) + 1 + 1 := by omega
    rw [hss]; ring
  calc 2 * (b i - b j) ^ 2 * (bm / b j) ^ 2 = 2 * ((b i - b j) * (bm / b j)) ^ 2 := by ring
    _ = 2 * ((2 * (s - 1) + 1) * bm) ^ 2 := by rw [hsub]
    _ = 2 * ((2 * (s - 1) + 1) ^ 2 * (bm * bm)) := by ring
    _ = 2 * ((8 * q + 1) * (bm * bm)) := by rw [hq]
    _ = 8 * bm * bm * (2 * q) + 2 * bm * bm := by ring

/-- Terms with `j < l < i` are `L * k` plus the small remainder `2 * (b j * (bm / b l))^2`. -/
theorem term_mid {bm i j l : ℕ} (hjl : j < l) (hli : l < i) (hl : b l ∣ bm) :
    ∃ k, 2 * (b i - b j) ^ 2 * (bm / b l) ^ 2
      = 8 * bm * bm * k + 2 * (b j * (bm / b l)) ^ 2 := by
  obtain ⟨p, hp⟩ : ∃ p, b j * (bm / b l) = p := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, b i / b l = Q := ⟨_, rfl⟩
  have h1 : b i * (bm / b l) = Q * bm := by
    rw [mul_div_swap (b_dvd_b hli.le) hl, hQdef]
  have hple : p ≤ Q * bm := by
    rw [← h1, ← hp]
    exact Nat.mul_le_mul_right _ (b_le_b (hjl.trans hli).le)
  obtain ⟨k, hk⟩ := two_mul_dvd_ratio hjl hli
  rw [hQdef] at hk
  have hbl : b l / b j * b j = b l := b_div_b_mul hjl.le
  have hblbm : b l * (bm / b l) = bm := Nat.mul_div_cancel' hl
  have hQp : Q * p = 2 * bm * k := by
    rw [hk, ← hp]
    calc 2 * (b l / b j) * k * (b j * (bm / b l))
        = 2 * k * (b l / b j * b j * (bm / b l)) := by ring
      _ = 2 * k * bm := by rw [hbl, hblbm]
      _ = 2 * bm * k := by ring
  obtain ⟨Q', hQ'def⟩ : ∃ Q', b l / b j * k = Q' := ⟨_, rfl⟩
  have hQ' : Q = 2 * Q' := by rw [hk, ← hQ'def]; ring
  have hQ256 : 256 ≤ Q := by rw [← hQdef]; exact b_div_b_ge hli
  have hsjpos : 0 < b l / b j := ratio_pos hjl.le
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  have hkQ' : k ≤ Q' := by
    rw [← hQ'def]
    calc k = 1 * k := (one_mul k).symm
      _ ≤ b l / b j * k := Nat.mul_le_mul_right k hsjpos
  have hkQ2 : k ≤ Q' * Q' := by nlinarith
  obtain ⟨c, hc⟩ : ∃ c, Q' * Q' = k + c := ⟨Q' * Q' - k, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, Q * bm = p + w := ⟨Q * bm - p, by omega⟩
  have hsub : (b i - b j) * (bm / b l) = w := by
    rw [Nat.sub_mul, h1, hp]
    omega
  refine ⟨c, ?_⟩
  have e1 : 8 * bm * bm * k = 4 * (p + w) * p := by
    calc 8 * bm * bm * k = 4 * bm * (2 * bm * k) := by ring
      _ = 4 * bm * (Q * p) := by rw [hQp]
      _ = 4 * (Q * bm) * p := by ring
      _ = 4 * (p + w) * p := by rw [hw]
  have e2 : 8 * bm * bm * (Q' * Q') = 2 * (p + w) ^ 2 := by
    calc 8 * bm * bm * (Q' * Q') = 2 * (2 * Q' * bm) ^ 2 := by ring
      _ = 2 * (Q * bm) ^ 2 := by rw [← hQ']
      _ = 2 * (p + w) ^ 2 := by rw [hw]
  have main : 2 * w ^ 2 + (4 * p ^ 2 + 4 * p * w)
      = (8 * bm * bm * c + 2 * p ^ 2) + (4 * p ^ 2 + 4 * p * w) := by
    calc 2 * w ^ 2 + (4 * p ^ 2 + 4 * p * w) = 2 * (p + w) ^ 2 + 2 * p ^ 2 := by ring
      _ = 8 * bm * bm * (Q' * Q') + 2 * p ^ 2 := by rw [e2]
      _ = 8 * bm * bm * (k + c) + 2 * p ^ 2 := by rw [hc]
      _ = 8 * bm * bm * k + 8 * bm * bm * c + 2 * p ^ 2 := by ring
      _ = 4 * (p + w) * p + 8 * bm * bm * c + 2 * p ^ 2 := by rw [e1]
      _ = (8 * bm * bm * c + 2 * p ^ 2) + (4 * p ^ 2 + 4 * p * w) := by ring
  calc 2 * (b i - b j) ^ 2 * (bm / b l) ^ 2 = 2 * ((b i - b j) * (bm / b l)) ^ 2 := by ring
    _ = 2 * w ^ 2 := by rw [hsub]
    _ = 8 * bm * bm * c + 2 * p ^ 2 := Nat.add_right_cancel main
    _ = 8 * bm * bm * c + 2 * (b j * (bm / b l)) ^ 2 := by rw [hp]

/-- The term at `l = i`, in additive form. -/
theorem term_eq_i {bm i j : ℕ} (hji : j < i) (hi : b i ∣ bm) :
    2 * (b i - b j) ^ 2 * (bm / b i) ^ 2 + 4 * bm * (b j * (bm / b i))
      = 2 * bm * bm + 2 * (b j * (bm / b i)) ^ 2 := by
  have h1 : b i * (bm / b i) = bm := Nat.mul_div_cancel' hi
  obtain ⟨u, hu⟩ : ∃ u, b j * (bm / b i) = u := ⟨_, rfl⟩
  have hule : u ≤ bm := by
    calc u = b j * (bm / b i) := hu.symm
      _ ≤ b i * (bm / b i) := Nat.mul_le_mul_right _ (b_le_b hji.le)
      _ = bm := h1
  obtain ⟨w, hw⟩ : ∃ w, bm = u + w := ⟨bm - u, by omega⟩
  have hsub : (b i - b j) * (bm / b i) = w := by
    rw [Nat.sub_mul, h1, hu]
    omega
  calc 2 * (b i - b j) ^ 2 * (bm / b i) ^ 2 + 4 * bm * (b j * (bm / b i))
      = 2 * ((b i - b j) * (bm / b i)) ^ 2 + 4 * bm * (b j * (bm / b i)) := by ring
    _ = 2 * w ^ 2 + 4 * bm * u := by rw [hsub, hu]
    _ = 2 * w ^ 2 + 4 * (u + w) * u := by rw [← hw]
    _ = 2 * ((u + w) * (u + w)) + 2 * u ^ 2 := by ring
    _ = 2 * bm * bm + 2 * u ^ 2 := by rw [← hw]; ring
    _ = 2 * bm * bm + 2 * (b j * (bm / b i)) ^ 2 := by rw [hu]


/-! ### The phase lemma -/

/-- **Phase lemma.**  For `j < i < m` the "phase" `2 (b i - b j)^2 T m` is, modulo `L m`,
squeezed into the middle band `[L/8, 7L/8]` (in fact it is within `L/100` of `L/2`). -/
theorem phase (m i j : ℕ) (hij : j < i) (hi : i < m) :
    L m / 8 ≤ (2 * (b i - b j) ^ 2 * T m) % L m ∧
      (2 * (b i - b j) ^ 2 * T m) % L m ≤ 7 * L m / 8 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hin : i ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hbn : 0 < b n := b_pos n
  have hBpos : 0 < b n * b n := by positivity
  set F : ℕ → ℕ := fun l => 2 * (b i - b j) ^ 2 * (b n / b l) ^ 2 with hF
  -- split `∑_{l < n+1}` into the five blocks `l < j`, `l = j`, `j < l < i`, `l = i`, `l > i`
  have e1 : (∑ l ∈ Ico 0 j, F l) + (∑ l ∈ Ico j (n + 1), F l) = ∑ l ∈ Ico 0 (n + 1), F l :=
    Finset.sum_Ico_consecutive F (Nat.zero_le _) (by omega)
  have e2 : ∑ l ∈ Ico j (n + 1), F l = F j + ∑ l ∈ Ico (j + 1) (n + 1), F l :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) F
  have e3 : (∑ l ∈ Ico (j + 1) i, F l) + (∑ l ∈ Ico i (n + 1), F l)
      = ∑ l ∈ Ico (j + 1) (n + 1), F l := Finset.sum_Ico_consecutive F (by omega) (by omega)
  have e4 : ∑ l ∈ Ico i (n + 1), F l = F i + ∑ l ∈ Ico (i + 1) (n + 1), F l :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) F
  have hT : 2 * (b i - b j) ^ 2 * T (n + 1) = ∑ l ∈ Ico 0 (n + 1), F l := by
    rw [← Finset.range_eq_Ico]
    simp only [hF, T, Nat.add_sub_cancel, Finset.mul_sum]
  -- block `l < j`: divisible by `L`
  obtain ⟨KA, hKA⟩ : ∃ KA, ∑ l ∈ Ico 0 j, F l = 8 * b n * b n * KA + ∑ l ∈ Ico 0 j, 0 := by
    refine sum_split _ F (fun _ => 0) _ ?_
    intro l hl
    rw [Finset.mem_Ico] at hl
    obtain ⟨k, hk⟩ := term_lt_j (bm := b n) (i := i) (j := j) (l := l) (by omega) hij
      (b_dvd_b (by omega : l ≤ n))
    exact ⟨k, by simp only [hF, Nat.add_zero]; exact hk⟩
  rw [Finset.sum_const_zero, Nat.add_zero] at hKA
  -- block `l = j`
  obtain ⟨q, hq2⟩ := term_eq_j (bm := b n) hij (b_dvd_b hjn)
  have hq : F j = 8 * b n * b n * (2 * q) + 2 * b n * b n := by simp only [hF]; exact hq2
  -- block `j < l < i`
  obtain ⟨KC, hKC⟩ : ∃ KC, ∑ l ∈ Ico (j + 1) i, F l
      = 8 * b n * b n * KC + ∑ l ∈ Ico (j + 1) i, 2 * (b j * (b n / b l)) ^ 2 := by
    refine sum_split _ F (fun l => 2 * (b j * (b n / b l)) ^ 2) _ ?_
    intro l hl
    rw [Finset.mem_Ico] at hl
    obtain ⟨k, hk⟩ := term_mid (bm := b n) (i := i) (j := j) (l := l) (by omega) (by omega)
      (b_dvd_b (by omega : l ≤ n))
    exact ⟨k, by simp only [hF]; exact hk⟩
  -- block `l = i`
  have hD : F i + 4 * b n * (b j * (b n / b i)) = 2 * b n * b n + 2 * (b j * (b n / b i)) ^ 2 := by
    simp only [hF]; exact term_eq_i (bm := b n) hij (b_dvd_b hin)
  -- bounds on the small terms
  have hbj : b j * (b n / b j) = b n := Nat.mul_div_cancel' (b_dvd_b hjn)
  have hbi : b i * (b n / b i) = b n := Nat.mul_div_cancel' (b_dvd_b hin)
  have hPC : ∑ l ∈ Ico (j + 1) i, 2 * (b j * (b n / b l)) ^ 2 ≤ b n * b n := by
    refine small_tail ?_
    calc 256 * (b j * (b n / b (j + 1))) = b j * (256 * (b n / b (j + 1))) := by ring
      _ ≤ b j * (b n / b j) := Nat.mul_le_mul le_rfl (M_step (b n) j)
      _ = b n := hbj
  have hSE : ∑ l ∈ Ico (i + 1) (n + 1), F l ≤ b n * b n := by
    have hterm : ∀ l ∈ Ico (i + 1) (n + 1), F l ≤ 2 * (b i * (b n / b l)) ^ 2 := by
      intro l _
      simp only [hF]
      have h1 : (b i - b j) ^ 2 ≤ b i ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      calc 2 * (b i - b j) ^ 2 * (b n / b l) ^ 2 ≤ 2 * b i ^ 2 * (b n / b l) ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) le_rfl
        _ = 2 * (b i * (b n / b l)) ^ 2 := by ring
    calc ∑ l ∈ Ico (i + 1) (n + 1), F l
        ≤ ∑ l ∈ Ico (i + 1) (n + 1), 2 * (b i * (b n / b l)) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ b n * b n := by
          refine small_tail ?_
          calc 256 * (b i * (b n / b (i + 1))) = b i * (256 * (b n / b (i + 1))) := by ring
            _ ≤ b i * (b n / b i) := Nat.mul_le_mul le_rfl (M_step (b n) i)
            _ = b n := hbi
  have hu : 256 * (b j * (b n / b i)) ≤ b n := by
    have h : b i / b j * (b j * (b n / b i)) = b n := by
      rw [← mul_assoc, b_div_b_mul hij.le, hbi]
    calc 256 * (b j * (b n / b i)) ≤ b i / b j * (b j * (b n / b i)) :=
          Nat.mul_le_mul (b_div_b_ge hij) le_rfl
      _ = b n := h
  have h2u : 2 * (b j * (b n / b i)) ^ 2 ≤ b n * b n := by nlinarith only [Nat.mul_le_mul hu hu]
  have hcc : 4 * b n * (b j * (b n / b i)) ≤ b n * b n := by
    nlinarith only [Nat.mul_le_mul (le_refl (b n)) hu]
  -- assembly
  obtain ⟨E, hE⟩ : ∃ E, 2 * (b j * (b n / b i)) ^ 2
      + (∑ l ∈ Ico (j + 1) i, 2 * (b j * (b n / b l)) ^ 2)
      + (∑ l ∈ Ico (i + 1) (n + 1), F l) = E := ⟨_, rfl⟩
  have hEle : E ≤ 3 * (b n * b n) := by rw [← hE]; linarith only [h2u, hPC, hSE]
  have hsum : 2 * (b i - b j) ^ 2 * T (n + 1) + 4 * b n * (b j * (b n / b i))
      = 8 * b n * b n * (KA + 2 * q + KC) + 4 * (b n * b n) + E := by
    rw [hT, ← e1, e2, ← e3, e4, hKA, hq, hKC, ← hE]
    linarith only [hD]
  obtain ⟨r, hr⟩ : ∃ r, 4 * (b n * b n) + E = 4 * b n * (b j * (b n / b i)) + r :=
    Nat.exists_eq_add_of_le (by linarith only [hcc, Nat.zero_le E, hBpos])
  have hX : 2 * (b i - b j) ^ 2 * T (n + 1) = 8 * b n * b n * (KA + 2 * q + KC) + r := by
    linarith only [hsum, hr]
  have hrlb : b n * b n ≤ r := by linarith only [hr, hcc]
  have hrub : r ≤ 7 * (b n * b n) := by
    linarith only [hr, hEle, Nat.zero_le (4 * b n * (b j * (b n / b i)))]
  have hrlt : r < 8 * b n * b n := by linarith only [hrub, hBpos]
  have hmod : (2 * (b i - b j) ^ 2 * T (n + 1)) % (8 * b n * b n) = r := by
    rw [hX, show 8 * b n * b n * (KA + 2 * q + KC) + r = r + 8 * b n * b n * (KA + 2 * q + KC) by
      ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have hL : L (n + 1) = 8 * b n * b n := by simp [L]
  have hL8 : L (n + 1) / 8 = b n * b n := by rw [L_div_eight]; simp
  have hL78 : 7 * L (n + 1) / 8 = 7 * (b n * b n) := by rw [seven_L_div_eight]; simp
  rw [hL8, hL78, hL, hmod]
  exact ⟨hrlb, hrub⟩

end Erdos1185
