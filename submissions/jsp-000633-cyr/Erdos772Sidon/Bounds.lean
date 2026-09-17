import Erdos772Sidon.Alteration

/-! The lower bound on `H k n` and its asymptotic consequences. -/

namespace Erdos772

open Filter

theorem H_le (k n : ℕ) : H k n ≤ n := by
  refine csSup_le ⟨0, Nat.zero_le _, ?_⟩ (fun r hr => hr.1)
  intro A _ _
  exact ⟨∅, Finset.empty_subset _, by intro a ha; simp at ha, Nat.zero_le _⟩

theorem H_ge (k n r : ℕ) (hr : r ≤ n)
    (h : ∀ A : Finset ℕ, A.card = n → RepBounded k A → ∃ S ⊆ A, IsSidon S ∧ r ≤ S.card) :
    r ≤ H k n :=
  le_csSup ⟨n, fun _ hr' => hr'.1⟩ ⟨hr, h⟩

theorem exists_s (k n : ℕ) (hk : 1 ≤ k) :
    ∃ s, s ≤ n ∧ 6 * k * s ^ 3 ≤ n ^ 2 ∧ n ^ 2 < 6 * k * (s + 1) ^ 3 := by
  have hex : ∃ s : ℕ, n ^ 2 < 6 * k * (s + 1) ^ 3 := by
    refine ⟨n, ?_⟩
    have e : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    have h1 : n ^ 2 < (n + 1) ^ 3 := by
      linarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2), Nat.zero_le n]
    have h2 : (n + 1) ^ 3 ≤ 6 * k * (n + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    linarith
  set s := Nat.find hex with hsdef
  have hspec : n ^ 2 < 6 * k * (s + 1) ^ 3 := Nat.find_spec hex
  have hle : 6 * k * s ^ 3 ≤ n ^ 2 := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · simp [h0]
    · have hmin := Nat.find_min hex (m := s - 1) (by omega)
      rw [show s - 1 + 1 = s by omega] at hmin
      exact not_lt.mp hmin
  have hsn : s ≤ n := by
    have hs3 : s ^ 3 ≤ n ^ 2 := by
      have : s ^ 3 ≤ 6 * k * s ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      have : s ^ 3 ≤ 0 ^ 3 := by simpa using hs3
      simpa using (Nat.pow_le_pow_iff_left (n := 3) (by norm_num)).mp this
    · have hnn : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn0 (by norm_num)
      exact (Nat.pow_le_pow_iff_left (n := 3) (by norm_num)).mp (le_trans hs3 hnn)
  exact ⟨s, hsn, hle, hspec⟩

theorem H_lower (k n : ℕ) (hk : 1 ≤ k) : ∃ s, n ^ 2 < 6 * k * (s + 1) ^ 3 ∧ s ≤ 2 * H k n := by
  obtain ⟨s, hsn, hle, hlt⟩ := exists_s k n hk
  refine ⟨s, hlt, ?_⟩
  have key : (s + 1) / 2 ≤ H k n := by
    refine H_ge k n _ (by omega) ?_
    intro A hA hRep
    obtain ⟨S, hSA, hSid, hS⟩ :=
      exists_sidon_subset k A hRep s (by rw [hA]; exact hsn) (by rw [hA]; exact hle)
    exact ⟨S, hSA, hSid, by omega⟩
  omega

/-- Core real-analytic step: any `y ≥ 1` whose cube is small enough is below `H k n`. -/
private lemma cube_key (k n : ℕ) (hk : 1 ≤ k) (y : ℝ) (hy : 1 ≤ y)
    (h : 6 * (k : ℝ) * (3 * y) ^ 3 ≤ (n : ℝ) ^ 2) : y < (H k n : ℝ) := by
  obtain ⟨s, hs1, hs2⟩ := H_lower k n hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < 6 * k := by linarith
  have hcast : (n : ℝ) ^ 2 < 6 * (k : ℝ) * ((s : ℝ) + 1) ^ 3 := by exact_mod_cast hs1
  have h23 : (2 * y + 1) ^ 3 ≤ (3 * y) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have step : 6 * (k : ℝ) * (2 * y + 1) ^ 3 < 6 * (k : ℝ) * ((s : ℝ) + 1) ^ 3 := by
    have := mul_le_mul_of_nonneg_left h23 (le_of_lt hk0)
    linarith
  have hlt : (2 * y + 1) ^ 3 < ((s : ℝ) + 1) ^ 3 := lt_of_mul_lt_mul_left step (le_of_lt hk0)
  have hys : 2 * y + 1 < (s : ℝ) + 1 :=
    lt_of_pow_lt_pow_left₀ 3 (by positivity) hlt
  have hsH : (s : ℝ) ≤ 2 * (H k n : ℝ) := by exact_mod_cast hs2
  linarith

theorem tendsto_H_div_sqrt (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop := by
  refine Filter.tendsto_atTop.2 (fun M => ?_)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set M' : ℝ := max M 1 with hM'def
  have hM1 : (1 : ℝ) ≤ M' := le_max_right _ _
  have hMM : M ≤ M' := le_max_left _ _
  set c : ℝ := 162 * k * M' ^ 3 with hcdef
  have hM3 : (1 : ℝ) ≤ M' ^ 3 := one_le_pow₀ hM1
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hcdef]; nlinarith
  refine Filter.eventually_atTop.2 ⟨⌈c ^ 2⌉₊ + 1, fun n hn => ?_⟩
  show M ≤ (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hcn : c ^ 2 ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : ⌈c ^ 2⌉₊ ≤ n)
  set x : ℝ := (n : ℝ) ^ (1 / 2 : ℝ) with hxdef
  have hx0 : 0 < x := by
    rw [hxdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hx2 : x ^ 2 = (n : ℝ) := by
    rw [hxdef, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (by linarith)]
    norm_num
  have hcx : c ≤ x := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (le_of_lt hx0) ?_
    rw [hx2]; exact hcn
  have hx1 : (1 : ℝ) ≤ x := le_trans hc1 hcx
  have hmain : 6 * (k : ℝ) * (3 * (M' * x)) ^ 3 ≤ (n : ℝ) ^ 2 := by
    have e1 : 6 * (k : ℝ) * (3 * (M' * x)) ^ 3 = c * x ^ 3 := by rw [hcdef]; ring
    have e2 : (n : ℝ) ^ 2 = x * x ^ 3 := by rw [← hx2]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hcx (by positivity)
  have hy1 : (1 : ℝ) ≤ M' * x := by nlinarith
  have := cube_key k n hk (M' * x) hy1 hmain
  rw [le_div_iff₀ hx0]
  nlinarith

theorem eventually_rpow_lt_H (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) < H k n := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine Filter.eventually_atTop.2 ⟨(162 * k) ^ 4 + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [show (1 / 2 + 1 / 12 : ℝ) = 7 / 12 by norm_num]
  set y : ℝ := (n : ℝ) ^ (7 / 12 : ℝ) with hydef
  have hy1 : (1 : ℝ) ≤ y := by
    have h := Real.rpow_le_rpow zero_le_one hnR (by norm_num : (0:ℝ) ≤ 7 / 12)
    simpa [hydef] using h
  have hd4 : (162 * (k : ℝ)) ^ 4 ≤ (n : ℝ) := by
    have h : ((162 * k) ^ 4 : ℕ) ≤ n := by omega
    have h' : (((162 * k) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hquart : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have hd : (162 * (k : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [hquart]; exact hd4
  have hy3 : y ^ (3 : ℕ) = (n : ℝ) ^ (7 / 4 : ℝ) := by
    rw [hydef, ← Real.rpow_natCast ((n : ℝ) ^ (7 / 12 : ℝ)) 3, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have hsplit : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (7 / 4 : ℝ) = (n : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast (n : ℝ) 2]
    norm_num
  have hmain : 6 * (k : ℝ) * (3 * y) ^ 3 ≤ (n : ℝ) ^ 2 := by
    have e1 : 6 * (k : ℝ) * (3 * y) ^ 3 = (162 * (k : ℝ)) * y ^ (3 : ℕ) := by ring
    rw [e1, hy3, ← hsplit]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  exact cube_key k n hk y hy1 hmain

end Erdos772
