import MerLeanExperiment.GridExtraDefinitions
import MerLeanExperiment.GeometricThresholds
import MerLeanExperiment.TwoFamilyIncidence
import Mathlib.Tactic

namespace Erdos441

private lemma sum_Icc_one_cast (n : ℕ) :
    ∑ a ∈ Finset.Icc 1 n, (a : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert (by simp), ih]
      push_cast
      ring

private lemma sum_Icc_two_sub_one_cast (n : ℕ) :
    ∑ a ∈ Finset.Icc 2 n, ((a : ℝ) - 1) = (n : ℝ) * (n - 1) / 2 := by
  by_cases hn : n = 0
  · subst n; simp
  by_cases hn1 : n = 1
  · subst n; simp
  have h2 : 2 ≤ n := by omega
  calc
    _ = (∑ a ∈ Finset.Icc 1 n, (a : ℝ)) - 1 - ((Finset.Icc 2 n).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      have hsplit : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
      simp
    _ = _ := by
      have hcard : (Finset.Icc 2 n).card = n - 1 := by
        simp
      rw [sum_Icc_one_cast]
      rw [hcard]
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      ring

theorem grid_extra4_nonneg (q : ℝ) (hq : 1 < q) (T t : ℤ) :
    0 ≤ gridExtra4 q T t := by
  classical
  simp only [gridExtra4]
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)
  · exact le_rfl

theorem grid_extra4_lower (q : ℝ) (hq : 1 < q) (T t : ℤ) (hT : 0 ≤ T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hu : 2 ≤ q ^ t)
    (hn : (⌊q ^ t⌋₊ : ℝ) < q ^ t - 1 / 2) :
    q ^ t / ((⌊q ^ t⌋₊ : ℝ) + 1) - q * (⌊q ^ t⌋₊ : ℝ) / q ^ t ≤
      gridExtra4 q T t := by
  classical
  let u : ℝ := q ^ t
  let n : ℕ := ⌊u⌋₊
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hu0 : 0 < u := zpow_pos hq0 t
  have hun : (n : ℝ) ≤ u := Nat.floor_le hu0.le
  have hult : u < (n : ℝ) + 1 := Nat.lt_floor_add_one u
  have hn' : (n : ℝ) < u - 1 / 2 := by simpa [n, u] using hn
  have hfloor : ⌊u + 1 / 2⌋₊ = n + 1 := by
    apply le_antisymm
    · have hm : ⌊u + 1 / 2⌋₊ < n + 2 := by
        rw [Nat.floor_lt (by positivity)]
        norm_num at hult ⊢
        linarith
      omega
    · apply Nat.le_floor
      norm_num at hn' ⊢
      linarith
  have hn2 : 2 ≤ n := by
    rw [show n = ⌊u⌋₊ by rfl]
    exact Nat.le_floor hu
  have hs : q ^ (-T) ≤ (n : ℝ) / u := by
    have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
    have hinv : q ^ (-t) = 1 / u := by
      simp [u, one_div]
    rw [hinv] at hp
    have : 1 / u ≤ (n : ℝ) / u := by
      apply div_le_div_of_nonneg_right _ hu0.le
      exact_mod_cast (show 1 ≤ n by omega)
    exact hp.trans this
  have hh0 : 0 < u / ((n : ℝ) + 1) := div_pos hu0 (by positivity)
  have hh1 : u / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).2 hult
  have hband := geom_band_lower q hq T hT ((n : ℝ) / u)
    (u / ((n : ℝ) + 1)) hs hh0 hh1
  have hcond (j : ℤ) :
      ((n + 1 : ℕ) : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j) ↔
        (n : ℝ) / u ≤ q ^ j ∧ q ^ j ≤ u / ((n : ℝ) + 1) := by
    have hp : 0 < q ^ j := zpow_pos hq0 j
    constructor
    · intro h
      have h1 := le_trans h (min_le_left _ _)
      have h2 := le_trans h (min_le_right _ _)
      constructor
      · apply (div_le_iff₀ hu0).2
        norm_num at h1 ⊢
        linarith
      · apply (le_div_iff₀ (by positivity)).2
        have hx := (le_div_iff₀ hp).1 h2
        simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hx
    · rintro ⟨h1, h2⟩
      apply le_min
      · have := (div_le_iff₀ hu0).1 h1
        norm_num at this ⊢
        linarith
      · apply (le_div_iff₀ hp).2
        have hx := (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).1 h2
        simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hx
  change u / ((n : ℝ) + 1) - q * (n : ℝ) / u ≤ gridExtra4 q T t
  rw [gridExtra4]
  change _ ≤ ∑ a ∈ Finset.Icc (n + 1) ⌊u + 1 / 2⌋₊,
    ∑ j ∈ Finset.Icc (-T) (-1),
      if (a : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j)
      then q ^ j * (q - 1) else 0
  rw [hfloor]
  simp only [Finset.Icc_self, Finset.sum_singleton]
  simp_rw [hcond]
  have hband' : u / ((n : ℝ) + 1) - q * (n : ℝ) / u ≤
      ∑ j ∈ (Finset.Icc (-T) (-1)).filter
        (fun j => (n : ℝ) / u ≤ q ^ j ∧ q ^ j ≤ u / ((n : ℝ) + 1)),
        q ^ j * (q - 1) := by
    calc
      _ = u / ((n : ℝ) + 1) - q * ((n : ℝ) / u) := by ring
      _ ≤ _ := hband
  simpa only [Finset.sum_filter] using hband'

theorem grid_case4_negative_columns (q : ℝ) (hq : 1 < q) (T t : ℤ)
    (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T) (hu : 2 ≤ q ^ t) :
    2 * (⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) ^ 2 / q ^ t - q ^ (-T) +
        gridExtra4 q T t ≤
      ∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1) := by
  classical
  let u : ℝ := q ^ t
  let n : ℕ := ⌊u⌋₊
  let m : ℕ := ⌊u + 1 / 2⌋₊
  let J : Finset ℤ := Finset.Icc (-T) (-1)
  let w : ℤ → ℝ := fun j => q ^ j * (q - 1)
  let P : ℕ → ℤ → Prop := fun a j => (a : ℝ) / u ≤ q ^ j
  let Q : ℕ → ℤ → Prop := fun a j =>
    (a : ℝ) ≤ min (u * q ^ j + 1) (u / q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hu0 : 0 < u := by simpa [u] using zpow_pos hq0 t
  have hun : (n : ℝ) ≤ u := by
    dsimp [n]
    exact Nat.floor_le hu0.le
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by simpa [u] using hu)
  have hnm : n ≤ m := by
    apply Nat.floor_mono
    dsimp [u]
    linarith
  have hw : ∀ j ∈ J, 0 ≤ w j := by
    intro j hj
    exact mul_nonneg (zpow_nonneg hq0.le _) (by linarith)
  have hPmem : ∀ a ∈ Finset.Icc 1 n, ∀ j ∈ J, P a j →
      (a : ℤ) ∈ gridA q t j := by
    intro a ha j hj hpa
    have hjle : j ≤ t := by
      have := (Finset.mem_Icc.1 hj).2
      omega
    simp only [gridA, hjle, ↓reduceIte, mem_gridPoints]
    left
    have ha1 : 1 ≤ (a : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    refine ⟨ha1, ?_⟩
    have := (div_le_iff₀ hu0).1 hpa
    simpa [u, mul_comm] using this
  have hQmem : ∀ a ∈ Finset.Icc 1 m, ∀ j ∈ J, Q a j →
      (1 - (a : ℤ)) ∈ gridA q t j := by
    intro a ha j hj hqa
    have hjle : j ≤ t := by
      have := (Finset.mem_Icc.1 hj).2
      omega
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    simp only [gridA, hjle, ↓reduceIte, mem_gridPoints]
    right
    constructor
    · have h1 := le_trans hqa (min_le_left _ _)
      have h2 := le_trans hqa (min_le_right _ _)
      have hm : (a : ℝ) - 1 ≤
          min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) := by
        apply le_min
        · dsimp [u] at h1
          nlinarith
        · dsimp [u] at h2
          linarith
      push_cast
      linarith
    · push_cast
      linarith
  have hinc := weighted_two_family_incidence
    (Finset.Icc 1 n) (Finset.Icc 1 m) J
    (fun a => (a : ℤ)) (fun a => 1 - (a : ℤ)) (fun j => gridA q t j)
    P Q w hw
    (by
      intro a ha b hb hab
      exact Int.ofNat_inj.mp hab)
    (by
      intro a ha b hb hab
      exact Int.ofNat_inj.mp (sub_right_inj.mp hab))
    (by
      intro a ha b hb hab
      have ha1 := (Finset.mem_Icc.1 ha).1
      have hb1 := (Finset.mem_Icc.1 hb).1
      omega)
    hPmem hQmem
  have hPA (a : ℕ) (ha : a ∈ Finset.Icc 1 n) :
      1 - q * ((a : ℝ) / u) ≤ ∑ j ∈ J, if P a j then w j else 0 := by
    have hs : q ^ (-T) ≤ (a : ℝ) / u := by
      have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
      have hinv : q ^ (-t) = 1 / u := by simp [u, one_div]
      rw [hinv] at hp
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
      exact hp.trans (by
        apply div_le_div_of_nonneg_right ha1 hu0.le)
    have htail := geom_tail_lower q hq T hT ((a : ℝ) / u) hs
    simpa only [J, P, w, Finset.sum_filter] using htail
  have hQB (a : ℕ) (ha : a ∈ Finset.Icc 2 n) :
      1 - q * (((a : ℝ) - 1) / u) ≤ ∑ j ∈ J, if Q a j then w j else 0 := by
    have hs : q ^ (-T) ≤ ((a : ℝ) - 1) / u := by
      have hp : q ^ (-T) ≤ q ^ (-t) := zpow_le_zpow_right₀ hq.le (by omega)
      have hinv : q ^ (-t) = 1 / u := by simp [u, one_div]
      rw [hinv] at hp
      have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
      exact hp.trans (by
        apply div_le_div_of_nonneg_right (by linarith) hu0.le)
    have htail := geom_tail_lower q hq T hT (((a : ℝ) - 1) / u) hs
    calc
      _ ≤ ∑ j ∈ J, if ((a : ℝ) - 1) / u ≤ q ^ j then w j else 0 := by
        simpa only [J, w, Finset.sum_filter] using htail
      _ ≤ ∑ j ∈ J, if Q a j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hth hqa
        · exact le_rfl
        · exfalso
          apply hqa
          have hjm1 : j ≤ -1 := (Finset.mem_Icc.1 hj).2
          have hqj0 : 0 < q ^ j := zpow_pos hq0 j
          have hqj1 : q ^ j ≤ 1 := by
            simpa using zpow_le_zpow_right₀ hq.le (by omega : j ≤ 0)
          have han : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 ha).2
          apply le_min
          · have hx := (div_le_iff₀ hu0).1 hth
            nlinarith
          · have hau : (a : ℝ) ≤ u := han.trans hun
            apply (le_div_iff₀ hqj0).2
            nlinarith
        · exact (hw j hj)
        · exact le_rfl
  have hQone : ∑ j ∈ J, w j ≤ ∑ j ∈ J, if Q 1 j then w j else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjm1 : j ≤ -1 := (Finset.mem_Icc.1 hj).2
    have hqj0 : 0 < q ^ j := zpow_pos hq0 j
    have hqj1 : q ^ j ≤ 1 := by
      simpa using zpow_le_zpow_right₀ hq.le (by omega : j ≤ 0)
    have huq : (1 : ℝ) ≤ u / q ^ j := by
      apply (le_div_iff₀ hqj0).2
      nlinarith
    have hQ : Q 1 j := by
      simpa only [Q, Nat.cast_one] using
        (le_min (by nlinarith [mul_pos hu0 hqj0]) huq)
    simp [hQ]
  have hJsum : ∑ j ∈ J, w j = 1 - q ^ (-T) := by
    dsimp [J, w]
    rw [sum_Icc_zpow_mul_sub_one q hq0.ne' (-T) (-1) (by omega)]
    norm_num
  have hbase :
      (n : ℝ) - q * (n : ℝ) * ((n : ℝ) + 1) / (2 * u) +
        ((n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T)) +
        gridExtra4 q T t ≤
      (∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if P a j then w j else 0) +
        ∑ a ∈ Finset.Icc 1 m, ∑ j ∈ J, if Q a j then w j else 0 := by
    have hA : (n : ℝ) - q * (n : ℝ) * ((n : ℝ) + 1) / (2 * u) ≤
        ∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if P a j then w j else 0 := by
      calc
        _ = ∑ a ∈ Finset.Icc 1 n, (1 - q * ((a : ℝ) / u)) := by
          rw [Finset.sum_sub_distrib]
          have hcard : (Finset.Icc 1 n).card = n := by simp
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          have hsumq : (∑ x ∈ Finset.Icc 1 n, q * ((x : ℝ) / u)) =
              q / u * ∑ x ∈ Finset.Icc 1 n, (x : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          rw [hsumq]
          rw [sum_Icc_one_cast]
          ring
        _ ≤ _ := Finset.sum_le_sum fun a ha => hPA a ha
    have hsetn : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hone_not : 1 ∉ Finset.Icc 2 n := by simp
    have hsetm : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Icc (n + 1) m := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) m) := by
      exact Finset.disjoint_left.mpr (by
        intro a ha hb
        have ha' := (Finset.mem_Icc.1 ha).2
        have hb' := (Finset.mem_Icc.1 hb).1
        omega)
    have hB0 :
        (n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T) ≤
          ∑ a ∈ Finset.Icc 1 n, ∑ j ∈ J, if Q a j then w j else 0 := by
      rw [hsetn, Finset.sum_insert hone_not]
      have hrest : (n : ℝ) - 1 - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) ≤
          ∑ a ∈ Finset.Icc 2 n, ∑ j ∈ J, if Q a j then w j else 0 := by
        calc
          _ = ∑ a ∈ Finset.Icc 2 n,
              (1 - q * (((a : ℝ) - 1) / u)) := by
            rw [Finset.sum_sub_distrib]
            have hcard : (Finset.Icc 2 n).card = n - 1 := by simp
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            have hsumq : (∑ x ∈ Finset.Icc 2 n, q * (((x : ℝ) - 1) / u)) =
                q / u * ∑ x ∈ Finset.Icc 2 n, ((x : ℝ) - 1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
            rw [hsumq]
            rw [sum_Icc_two_sub_one_cast]
            have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ n)]
              norm_num
            rw [hcast]
            ring
          _ ≤ _ := Finset.sum_le_sum fun a ha => hQB a ha
      rw [hJsum] at hQone
      linarith
    have hextra : gridExtra4 q T t =
        ∑ a ∈ Finset.Icc (n + 1) m, ∑ j ∈ J, if Q a j then w j else 0 := by
      simp only [gridExtra4]
      change (∑ a ∈ Finset.Icc (n + 1) m,
        ∑ j ∈ J, if Q a j then w j else 0) = _
      rfl
    have hB :
        ((n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / (2 * u) - q ^ (-T)) +
            gridExtra4 q T t ≤
          ∑ a ∈ Finset.Icc 1 m, ∑ j ∈ J, if Q a j then w j else 0 := by
      rw [hsetm, Finset.sum_union hdis, hextra]
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hB0
          (∑ a ∈ Finset.Icc (n + 1) m, ∑ j ∈ J, if Q a j then w j else 0))
    linarith [add_le_add hA hB]
  have := hbase.trans hinc
  dsimp [J, w] at this ⊢
  dsimp [u, n] at this ⊢
  calc
    _ = (⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) * ((⌊q ^ t⌋₊ : ℝ) + 1) /
          (2 * q ^ t) +
        ((⌊q ^ t⌋₊ : ℝ) - q * (⌊q ^ t⌋₊ : ℝ) * ((⌊q ^ t⌋₊ : ℝ) - 1) /
          (2 * q ^ t) - q ^ (-T)) + gridExtra4 q T t := by ring
    _ ≤ ∑ j ∈ Finset.Icc (-T) (-1),
        ((gridA q t j).card : ℝ) * (q ^ j * (q - 1)) := this
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

end Erdos441
