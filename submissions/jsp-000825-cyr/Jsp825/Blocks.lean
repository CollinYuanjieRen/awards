import Jsp825.Params

/-!
# JSP-000825 / Erdős #992 — the blocks of the construction

Basic arithmetic of the parameters `grp, L, r, m, N`, the block structure of the sequence `x`
(`x_eq`, `x_strictMono`), and the block deviation estimate `err_block`.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-! ## Basic parameter estimates -/

theorem grp_le (j : ℕ) (hj : 1 ≤ j) : 2 ^ grp j ≤ j :=
  Nat.pow_log_le_self 2 (by omega)

theorem lt_grp (j : ℕ) : j < 2 ^ (grp j + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) j

theorem two_le_grp (j : ℕ) (hj : 4 ≤ j) : 2 ≤ grp j :=
  Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem twelve_le_L (j : ℕ) (hj : 4 ≤ j) : 12 ≤ L j := by
  have h := two_le_grp j hj
  have h2 : 2 ^ 2 ≤ 2 ^ grp j := Nat.pow_le_pow_right (by norm_num) h
  calc 12 = 3 * 4 := by norm_num
    _ ≤ (grp j + 1) * 2 ^ grp j := Nat.mul_le_mul (by omega) (by simpa using h2)
    _ = L j := rfl

theorem L_ge_six (j : ℕ) (hj : 4 ≤ j) : 6 ≤ L j :=
  le_trans (by norm_num) (twelve_le_L j hj)

/-- `2 ^ r j` exceeds `16 * L j` (note `32 * L j ≤ 2 ^ r j` is **false**, e.g. `L j = 12`). -/
theorem sixteen_L_lt (j : ℕ) : 16 * L j < 2 ^ r j := by
  have h : L j < 2 ^ (Nat.log 2 (L j) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have he : (2:ℕ) ^ r j = 16 * 2 ^ (Nat.log 2 (L j) + 1) := by
    show (2:ℕ) ^ (Nat.log 2 (L j) + 5) = _
    rw [pow_add, pow_add]
    ring
  omega

theorem sixteen_L_le (j : ℕ) : 16 * L j ≤ 2 ^ r j := (sixteen_L_lt j).le

theorem L_lt_pow_r (j : ℕ) : L j < 2 ^ r j := by
  have := sixteen_L_lt j
  have := L_pos j
  omega

theorem m_succ (j : ℕ) : m (j + 1) = m j + r j := rfl

theorem m_mono : Monotone m := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [m_succ]; omega

theorem N_mono : StrictMono N := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have := L_pos (n + 1)
  rw [N_succ]; omega

theorem N_tendsto : Tendsto N atTop atTop := N_mono.tendsto_atTop

theorem N_pred_add (j : ℕ) (hj : 1 ≤ j) : N j = N (j - 1) + L j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa using N_succ k

/-! ## The block structure of `x` -/

theorem blockOf_spec (n : ℕ) :
    N (blockOf n - 1) ≤ n ∧ n < N (blockOf n) ∧ 1 ≤ blockOf n := by
  have h1 : n < N (blockOf n) := Nat.find_spec (exists_lt_N n)
  have h2 : 1 ≤ blockOf n := by
    rcases Nat.eq_zero_or_pos (blockOf n) with h | h
    · rw [h] at h1; simp [N] at h1
    · exact h
  refine ⟨?_, h1, h2⟩
  have h3 : ¬ (n < N (blockOf n - 1)) :=
    Nat.find_min (exists_lt_N n) (m := blockOf n - 1) (show blockOf n - 1 < blockOf n by omega)
  omega

theorem blockOf_eq {j n : ℕ} (hj : 1 ≤ j) (h1 : N (j - 1) ≤ n) (h2 : n < N j) :
    blockOf n = j := by
  obtain ⟨hs1, hs2, hs3⟩ := blockOf_spec n
  have hle : blockOf n ≤ j := Nat.find_le h2
  by_contra hne
  have hlt : blockOf n < j := by omega
  have : N (blockOf n) ≤ N (j - 1) := N_mono.monotone (by omega)
  omega

theorem x_eq {j t : ℕ} (hj : 1 ≤ j) (ht : t < L j) :
    x (N (j - 1) + t) = 2 ^ m j * ((t : ℤ) + 1) := by
  have hb : blockOf (N (j - 1) + t) = j := by
    refine blockOf_eq hj (by omega) ?_
    rw [N_pred_add j hj]; omega
  unfold x
  rw [hb]
  congr 2
  omega

theorem x_pos (n : ℕ) : 0 < x n := by
  unfold x
  have : (0:ℤ) < 2 ^ m (blockOf n) := by positivity
  have h2 : (0:ℤ) ≤ ((n - N (blockOf n - 1) : ℕ) : ℤ) := Int.natCast_nonneg _
  positivity

theorem x_strictMono : StrictMono x := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  obtain ⟨hs1, hs2, hs3⟩ := blockOf_spec n
  set j := blockOf n with hj
  rcases lt_or_ge (n + 1) (N j) with h | h
  · have hb : blockOf (n + 1) = j := blockOf_eq hs3 (by omega) h
    unfold x
    rw [hb, ← hj]
    have hpow : (0:ℤ) < 2 ^ m j := by positivity
    have : ((n + 1 - N (j - 1) : ℕ) : ℤ) = ((n - N (j - 1) : ℕ) : ℤ) + 1 := by
      have : (n + 1 - N (j - 1) : ℕ) = (n - N (j - 1) : ℕ) + 1 := by omega
      rw [this]; push_cast; ring
    rw [this]
    have : ((n - N (j - 1) : ℕ) : ℤ) + 1 < ((n - N (j - 1) : ℕ) : ℤ) + 1 + 1 := by omega
    exact mul_lt_mul_of_pos_left this hpow
  · have hNj : n + 1 = N j := by omega
    -- `x n` is the last element of block `j`
    have hxn : x n = 2 ^ m j * (L j : ℤ) := by
      unfold x
      rw [← hj]
      congr 1
      have hL : N j = N (j - 1) + L j := N_pred_add j hs3
      have : (n - N (j - 1) : ℕ) + 1 = L j := by omega
      omega
    -- `x (n+1)` is the first element of block `j+1`
    have hb : blockOf (n + 1) = j + 1 := by
      refine blockOf_eq (by omega) ?_ ?_
      · simpa using hNj.ge
      · rw [N_pred_add (j + 1) (by omega)]
        have := L_pos (j + 1)
        simp only [Nat.add_sub_cancel]
        omega
    have hxn1 : x (n + 1) = 2 ^ m (j + 1) := by
      unfold x
      rw [hb]
      have : (n + 1 - N (j + 1 - 1) : ℕ) = 0 := by simp only [Nat.add_sub_cancel]; omega
      rw [this]; push_cast; ring
    rw [hxn, hxn1, m_succ, pow_add]
    have hpow : (0:ℤ) < 2 ^ m j := by positivity
    have hLlt : (L j : ℤ) < 2 ^ r j := by
      exact_mod_cast L_lt_pow_r j
    exact mul_lt_mul_of_pos_left hLlt hpow

/-! ## Block deviation -/

/-- The deviation of `α` at the scale of block `j`: the fractional part of `2 ^ (m j) * α`. -/
noncomputable def β (j : ℕ) (α : ℝ) : ℝ := Int.fract ((2 : ℝ) ^ m j * α)

theorem β_nonneg (j : ℕ) (α : ℝ) : 0 ≤ β j α := Int.fract_nonneg _

/-- Inside block `j` the fractional parts of `α * x n` are those of `β j α * (t + 1)`. -/
theorem fract_block (j : ℕ) (α : ℝ) (t : ℕ) (hj : 1 ≤ j) (ht : t < L j) :
    Int.fract (α * (x (N (j - 1) + t) : ℝ)) = Int.fract (β j α * ((t : ℝ) + 1)) := by
  have hx : ((x (N (j - 1) + t) : ℤ) : ℝ) = (2 : ℝ) ^ m j * ((t : ℝ) + 1) := by
    rw [x_eq hj ht]; push_cast; ring
  rw [hx]
  have key : α * ((2 : ℝ) ^ m j * ((t : ℝ) + 1))
      = ((⌊(2 : ℝ) ^ m j * α⌋ * ((t : ℤ) + 1) : ℤ) : ℝ) + β j α * ((t : ℝ) + 1) := by
    simp only [β, Int.fract]
    push_cast
    ring
  rw [key, Int.fract_intCast_add]

open Classical in
/-- If the block deviation lies in `[3/(8L), 5/(8L)]`, then at least `5 L / 8` of the `L` points of
block `j` have fractional part in `I₀ = [0, 1/2)`. -/
theorem count_block (j : ℕ) (α : ℝ) (hj : 4 ≤ j)
    (hβ : β j α ∈ Icc (3 / (8 * L j : ℝ)) (5 / (8 * L j))) :
    5 * (L j : ℝ) / 8 ≤
      (((Finset.range (L j)).filter fun t : ℕ ↦ Int.fract (β j α * ((t : ℝ) + 1)) ∈ I₀).card : ℝ) := by
  classical
  have hL12 : 12 ≤ L j := twelve_le_L j hj
  have hLR : (12 : ℝ) ≤ (L j : ℝ) := by exact_mod_cast hL12
  have hLpos : (0 : ℝ) < (L j : ℝ) := by linarith only [hLR]
  obtain ⟨h1, h2⟩ := hβ
  have hb0 : 0 ≤ β j α := β_nonneg j α
  set k := 4 * L j / 5 - 1 with hk
  have hsub : Finset.range k ⊆ (Finset.range (L j)).filter
      fun t : ℕ ↦ Int.fract (β j α * ((t : ℝ) + 1)) ∈ I₀ := by
    intro t ht
    simp only [Finset.mem_range] at ht
    have htL : t < L j := by omega
    have h5 : 5 * (t + 1) < 4 * L j := by omega
    have h5R : 5 * ((t : ℝ) + 1) < 4 * (L j : ℝ) := by exact_mod_cast h5
    have htpos : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    have hle : β j α * ((t : ℝ) + 1) ≤ 5 / (8 * (L j : ℝ)) * ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h2 htpos
    have hb : 5 / (8 * (L j : ℝ)) * ((t : ℝ) + 1) < 1 / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith only [h5R]
    have hval : β j α * ((t : ℝ) + 1) < 1 / 2 := by linarith only [hle, hb]
    have hnn : 0 ≤ β j α * ((t : ℝ) + 1) := mul_nonneg hb0 htpos
    have hfr : Int.fract (β j α * ((t : ℝ) + 1)) = β j α * ((t : ℝ) + 1) :=
      Int.fract_eq_self.mpr ⟨hnn, by linarith only [hval]⟩
    simp only [Finset.mem_filter, Finset.mem_range, I₀, Set.mem_Ico]
    exact ⟨htL, by rw [hfr]; exact ⟨hnn, hval⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have hkN : 5 * L j ≤ 8 * k := by omega
  have hkR : 5 * (L j : ℝ) ≤ 8 * (k : ℝ) := by exact_mod_cast hkN
  have hcR := (Nat.cast_le (α := ℝ)).mpr hcard
  linarith only [hkR, hcR]

open Classical in
/-- The counting function splits along block `j`. -/
theorem count_split (j : ℕ) (α : ℝ) (hj : 1 ≤ j) :
    count x α (N j) I₀ = count x α (N (j - 1)) I₀ +
      ((Finset.range (L j)).filter fun t : ℕ ↦ Int.fract (β j α * ((t : ℝ) + 1)) ∈ I₀).card := by
  classical
  have hN : N j = N (j - 1) + L j := N_pred_add j hj
  unfold count
  rw [hN]
  simp only [Finset.card_filter]
  rw [Finset.sum_range_add (M := ℕ)]
  congr 1
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  exact if_congr (by rw [fract_block j α t hj (Finset.mem_range.mp ht)]) rfl rfl

theorem volume_I₀ : (volume I₀).toReal = 1 / 2 := by
  rw [I₀, Real.volume_Ico, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- The block deviation estimate: a block whose deviation lies in `[3/(8L), 5/(8L)]` contributes at
least `L j / 8` to the error of the interval `I₀ = [0, 1/2)`. -/
theorem err_block (j : ℕ) (α : ℝ) (hj : 4 ≤ j)
    (hβ : β j α ∈ Icc (3 / (8 * L j : ℝ)) (5 / (8 * L j))) :
    (L j : ℝ) / 8 ≤ err x α (N j) I₀ - err x α (N (j - 1)) I₀ := by
  classical
  have hcount := count_split j α (by omega)
  have hcb := count_block j α hj hβ
  have hN : ((N j : ℕ) : ℝ) = ((N (j - 1) : ℕ) : ℝ) + (L j : ℝ) := by
    rw [N_pred_add j (by omega)]; push_cast; ring
  unfold err
  rw [hcount, volume_I₀, hN]
  push_cast
  linarith only [hcb]

end Erdos992
