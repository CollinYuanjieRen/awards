import Erdos193Walk.Definitions

/-! The recursion of the Gaussian-lattice walk and the 2-adic valuation identity (2) of the paper. -/

namespace Erdos193Walk

open Zsqrtd

theorem I_pow_four : I ^ 4 = 1 := by
  have h2 : I * I = -1 := by
    simp [Zsqrtd.ext_iff, I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  calc I ^ 4 = (I * I) * (I * I) := by ring
    _ = 1 := by rw [h2]; ring

/-- `I ^ k` for `k < 4` is one of the four Gaussian units. -/
private lemma I_pow_cases (k : ℕ) (hk : k < 4) :
    I ^ k = 1 ∨ I ^ k = I ∨ I ^ k = -1 ∨ I ^ k = -I := by
  have h2 : (I : G) ^ 2 = -1 := by
    simp [Zsqrtd.ext_iff, I, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  interval_cases k
  · exact Or.inl (pow_zero I)
  · exact Or.inr (Or.inl (pow_one I))
  · exact Or.inr (Or.inr (Or.inl h2))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have h3 : (I : G) ^ 3 = I ^ 2 * I := by ring
    rw [h3, h2]; ring

/-- `I ^ m` only depends on `m % 4`. -/
private lemma I_pow_mod (m : ℕ) : I ^ (m % 4) = I ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 4]
  rw [pow_add, pow_mul, I_pow_four, one_pow, one_mul]

theorem α_lt_four (n : ℕ) : α n < 4 := by
  cases n with
  | zero => simp [α]
  | succ k =>
    rw [α]
    exact Nat.mod_lt _ (by norm_num)

theorem α_two_mul_add (n ε : ℕ) (hε : ε < 2) : α (2 * n + ε) = (ε + α n) % 4 := by
  rcases Nat.eq_zero_or_pos (2 * n + ε) with h | h
  · have hn : n = 0 := by omega
    have he : ε = 0 := by omega
    subst hn; subst he; simp [α]
  · obtain ⟨k, hk⟩ : ∃ k, 2 * n + ε = k + 1 := ⟨2 * n + ε - 1, by omega⟩
    rw [hk, α]
    have h1 : (k + 1) % 2 = ε := by omega
    have h2 : (k + 1) / 2 = n := by omega
    rw [h1, h2]

theorem u_two_mul_add (n ε : ℕ) (hε : ε < 2) : u (2 * n + ε) = I ^ ε * u n := by
  unfold u
  rw [α_two_mul_add n ε hε, I_pow_mod, pow_add]

private lemma z_succ_aux (n : ℕ) : z (n + 1) = z n + u n := by
  simp [z, Finset.sum_range_succ]

theorem z_two_mul (n : ℕ) : z (2 * n) = (1 + I) * z n := by
  induction n with
  | zero => simp [z]
  | succ k ih =>
    have hu0 : u (2 * k) = u k := by
      have := u_two_mul_add k 0 (by norm_num)
      simpa using this
    have hu1 : u (2 * k + 1) = I * u k := by
      have := u_two_mul_add k 1 (by norm_num)
      simpa using this
    have h1 : z (2 * k + 1) = (1 + I) * z k + u k := by
      rw [z_succ_aux (2 * k), ih, hu0]
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, z_succ_aux, h1, hu1, z_succ_aux]
    ring

theorem z_two_mul_add_one (n : ℕ) : z (2 * n + 1) = (1 + I) * z n + u n := by
  have hu0 : u (2 * n) = u n := by
    have := u_two_mul_add n 0 (by norm_num)
    simpa using this
  rw [z_succ_aux (2 * n), z_two_mul, hu0]

theorem z_succ (n : ℕ) : z (n + 1) = z n + u n := z_succ_aux n

/-- The norm on the Gaussian integers is the sum of the squares of the coordinates. -/
private lemma norm_eq (x : G) : norm x = x.re * x.re + x.im * x.im := by
  rw [Zsqrtd.norm_def]; ring

/-- Every `u n` is a Gaussian unit whose coordinate sum is odd. -/
theorem odd_re_add_im_u (n : ℕ) : Odd ((u n).re + (u n).im) := by
  rcases I_pow_cases (α n) (α_lt_four n) with h | h | h | h <;>
    · rw [u, h]
      simp [I]

theorem norm_u (n : ℕ) : norm (u n) = 1 := by
  rcases I_pow_cases (α n) (α_lt_four n) with h | h | h | h <;>
    · rw [u, h]
      norm_num [norm_eq, I]

/-! ### Arithmetic helpers -/

private lemma not_two_dvd_of_odd {N : ℤ} (h : Odd N) : ¬ (2 : ℤ) ∣ N := by
  rw [Int.odd_iff] at h
  intro hd
  rw [Int.dvd_iff_emod_eq_zero] at hd
  omega

private lemma ne_zero_of_odd {N : ℤ} (h : Odd N) : N ≠ 0 := by
  rw [Int.odd_iff] at h
  intro hN
  rw [hN] at h
  norm_num at h

private lemma padicValInt_two_of_odd (o : ℤ) (ho : Odd o) : padicValInt 2 o = 0 :=
  padicValInt.eq_zero_of_not_dvd (by simpa using not_two_dvd_of_odd ho)

private lemma padicValNat_two_of_odd (k : ℕ) (hk : Odd k) : padicValNat 2 k = 0 := by
  refine padicValNat.eq_zero_of_not_dvd ?_
  rw [Nat.odd_iff] at hk
  intro hd
  rw [Nat.dvd_iff_mod_eq_zero] at hd
  omega

private lemma padicValInt_two_val : padicValInt 2 (2 : ℤ) = 1 := by
  have h := padicValInt_self (p := 2)
  simpa using h

private lemma padicValInt_two_mul (N : ℤ) (hN : N ≠ 0) :
    padicValInt 2 (2 * N) = padicValInt 2 N + 1 := by
  rw [padicValInt.mul (a := 2) (by norm_num) hN, padicValInt_two_val]
  omega

private lemma padicValNat_two_mul (k : ℕ) (hk : k ≠ 0) :
    padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
  rw [padicValNat.mul (a := 2) (by norm_num) hk, padicValNat_self]
  omega

/-- The norm of a Gaussian integer with odd coordinate sum is odd. -/
private lemma norm_odd_of_odd_re_add_im (x : G) (hx : Odd (x.re + x.im)) : Odd (norm x) := by
  rw [norm_eq]
  rcases Int.even_or_odd x.re with hr | hr <;> rcases Int.even_or_odd x.im with hi | hi
  · exfalso
    rw [Int.odd_iff] at hx
    have h := Int.even_iff.mp (hr.add hi)
    omega
  · exact (hr.mul_right _).add_odd (hi.mul hi)
  · exact (hr.mul hr).add_even (hi.mul_right _)
  · exfalso
    rw [Int.odd_iff] at hx
    have h := Int.even_iff.mp (hr.add_odd hi)
    omega

private lemma sum_re (s : Finset ℕ) (f : ℕ → G) : (∑ r ∈ s, f r).re = ∑ r ∈ s, (f r).re := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.re_add, ih]

private lemma sum_im (s : Finset ℕ) (f : ℕ → G) : (∑ r ∈ s, f r).im = ∑ r ∈ s, (f r).im := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.im_add, ih]

private lemma sum_emod_two (g : ℕ → ℤ) (hg : ∀ r, g r % 2 = 1) (s : Finset ℕ) :
    (∑ r ∈ s, g r) % 2 = (s.card : ℤ) % 2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have h1 := hg a
      push_cast
      omega

private lemma norm_1_add_I : norm ((1 : G) + I) = 2 := by
  norm_num [norm_eq, I]

private lemma I_ne_zero : (I : G) ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.im h
  simp [I] at this

/-- Auxiliary strong-induction form of identity (2), with the induction carried on `d = n - m`. -/
private lemma norm_z_sub_aux :
    ∀ d : ℕ, ∀ m n : ℕ, n - m = d → m < n → u m = u n →
      norm (z n - z m) ≠ 0 ∧ padicValInt 2 (norm (z n - z m)) = padicValNat 2 (n - m) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m n hd hmn hu
    rcases Nat.even_or_odd d with he | ho
    · -- even case: `m = 2a + ε`, `n = 2b + ε`, and `z n - z m = (1 + I) * (z b - z a)`
      obtain ⟨e, hde⟩ := he
      obtain ⟨ε, a, b, hεlt, hma, hnb, hab, hdab⟩ :
          ∃ ε a b, ε < 2 ∧ m = 2 * a + ε ∧ n = 2 * b + ε ∧ a < b ∧ b - a = e :=
        ⟨m % 2, m / 2, n / 2, by omega, by omega, by omega, by omega, by omega⟩
      have hnm : n - m = 2 * e := by omega
      have hua : u a = u b := by
        have h1 : u m = I ^ ε * u a := by rw [hma]; exact u_two_mul_add a ε hεlt
        have h2 : u n = I ^ ε * u b := by rw [hnb]; exact u_two_mul_add b ε hεlt
        refine mul_left_cancel₀ (pow_ne_zero ε I_ne_zero) ?_
        rw [← h1, ← h2]; exact hu
      have hz : z n - z m = (1 + I) * (z b - z a) := by
        rcases (show ε = 0 ∨ ε = 1 by omega) with h0 | h0 <;> subst h0
        · rw [hma, hnb, Nat.add_zero, Nat.add_zero, z_two_mul, z_two_mul]; ring
        · rw [hma, hnb, z_two_mul_add_one, z_two_mul_add_one, ← hua]; ring
      obtain ⟨hne, hval⟩ := ih e (by omega) a b hdab hab hua
      have hnorm : norm (z n - z m) = 2 * norm (z b - z a) := by
        rw [hz, Zsqrtd.norm_mul, norm_1_add_I]
      refine ⟨?_, ?_⟩
      · rw [hnorm]
        exact mul_ne_zero two_ne_zero hne
      · rw [hnorm, padicValInt_two_mul _ hne, hval, hdab, hnm,
          padicValNat_two_mul e (by omega)]
    · -- odd case: `z n - z m` is a sum of an odd number of units with odd coordinate sum
      have hsum : z n - z m = ∑ r ∈ Finset.Ico m n, u r := by
        simp only [z]
        exact (Finset.sum_Ico_eq_sub u hmn.le).symm
      have hcard : (Finset.Ico m n).card = n - m := Nat.card_Ico m n
      have hnmodd : Odd (n - m) := by rw [hd]; exact ho
      have hoddsum : Odd ((z n - z m).re + (z n - z m).im) := by
        rw [hsum, sum_re, sum_im, ← Finset.sum_add_distrib, Int.odd_iff,
          sum_emod_two (fun r => (u r).re + (u r).im)
            (fun r => Int.odd_iff.mp (odd_re_add_im_u r)), hcard]
        have h : (n - m) % 2 = 1 := Nat.odd_iff.mp hnmodd
        omega
      have hoddnorm : Odd (norm (z n - z m)) := norm_odd_of_odd_re_add_im _ hoddsum
      refine ⟨ne_zero_of_odd hoddnorm, ?_⟩
      rw [padicValInt_two_of_odd _ hoddnorm,
        padicValNat_two_of_odd _ hnmodd]

/-- Identity (2) of the paper: for `m < n` with `u m = u n`, the norm `|z n - z m|²` is nonzero
and its 2-adic valuation equals that of `n - m`. -/
theorem norm_z_sub (m n : ℕ) (hmn : m < n) (hu : u m = u n) :
    norm (z n - z m) ≠ 0 ∧ padicValInt 2 (norm (z n - z m)) = padicValNat 2 (n - m) :=
  norm_z_sub_aux (n - m) m n rfl hmn hu

end Erdos193Walk
