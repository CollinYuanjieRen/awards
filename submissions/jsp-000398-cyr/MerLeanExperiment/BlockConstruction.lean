import MerLeanExperiment.Subdivision

open Classical Set

namespace Erdos492Real

noncomputable section

/-- The integral cutoffs used to separate the rescaled finite divisions. -/
def blockCutoff : ℕ → ℕ
  | 0 => 1
  | k + 1 => 4 * (k + 2) ^ 2 * blockCutoff k

@[simp] theorem blockCutoff_zero : blockCutoff 0 = 1 := rfl

@[simp] theorem blockCutoff_succ (k : ℕ) :
    blockCutoff (k + 1) = 4 * (k + 2) ^ 2 * blockCutoff k := rfl

theorem blockCutoff_pos (k : ℕ) : 0 < blockCutoff k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [blockCutoff_succ]; positivity

theorem blockCutoff_lt_succ (k : ℕ) : blockCutoff k < blockCutoff (k + 1) := by
  rw [blockCutoff_succ]
  have hp : 0 < (k + 2) ^ 2 := pow_pos (by omega) _
  have hk : 1 < 4 * (k + 2) ^ 2 := by omega
  nlinarith [blockCutoff_pos k]

theorem blockCutoff_strictMono : StrictMono blockCutoff :=
  strictMono_nat_of_lt_succ blockCutoff_lt_succ

theorem nat_succ_le_blockCutoff (k : ℕ) : k + 1 ≤ blockCutoff k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 2 ≤ blockCutoff k + 1 := Nat.add_le_add_right ih 1
        _ ≤ blockCutoff (k + 1) := blockCutoff_lt_succ k

/-- The part of the `k`th rescaled division strictly after its left cutoff. -/
def blockEndpoints (P : ℕ → FiniteDivision) (k : ℕ) : Set ℝ :=
  {x | ∃ t ∈ (P k).points,
    (blockCutoff k : ℝ) < (blockCutoff (k + 1) : ℝ) * t ∧
      x = (blockCutoff (k + 1) : ℝ) * t}

/-- Schmidt's global endpoint set obtained by splicing the finite divisions. -/
def globalEndpoints (P : ℕ → FiniteDivision) : Set ℝ :=
  {0, 1} ∪ ⋃ k, blockEndpoints P k

theorem zero_mem_globalEndpoints (P : ℕ → FiniteDivision) :
    0 ∈ globalEndpoints P := by simp [globalEndpoints]

theorem one_mem_globalEndpoints (P : ℕ → FiniteDivision) :
    1 ∈ globalEndpoints P := by simp [globalEndpoints]

theorem blockEndpoint_nonneg {P : ℕ → FiniteDivision} {k : ℕ} {x : ℝ}
    (hx : x ∈ blockEndpoints P k) : 0 ≤ x := by
  obtain ⟨t, ht, -, rfl⟩ := hx
  exact mul_nonneg (Nat.cast_nonneg _) ((P k).mem_unit t ht).1

theorem globalEndpoints_nonneg (P : ℕ → FiniteDivision) :
    globalEndpoints P ⊆ Ici 0 := by
  rintro x (hx | hx)
  · rcases hx with (rfl | rfl) <;> simp
  · simp only [mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    exact blockEndpoint_nonneg hk

theorem cutoff_mem_globalEndpoints (P : ℕ → FiniteDivision) (k : ℕ) :
    (blockCutoff k : ℝ) ∈ globalEndpoints P := by
  cases k with
  | zero => simpa using one_mem_globalEndpoints P
  | succ k =>
      right
      simp only [mem_iUnion]
      refine ⟨k, 1, (P k).one_mem, ?_, by ring⟩
      norm_num
      exact_mod_cast blockCutoff_lt_succ k

theorem globalEndpoints_unbounded (P : ℕ → FiniteDivision) :
    ∀ R : ℝ, ∃ x ∈ globalEndpoints P, R < x := by
  intro R
  obtain ⟨k, hk⟩ := exists_nat_gt R
  refine ⟨blockCutoff k, cutoff_mem_globalEndpoints P k, hk.trans_le ?_⟩
  exact_mod_cast (Nat.le_trans (Nat.le_add_right k 1) (nat_succ_le_blockCutoff k))

theorem blockEndpoints_finite (P : ℕ → FiniteDivision) (k : ℕ) :
    (blockEndpoints P k).Finite := by
  let f : ℝ → ℝ := fun t => (blockCutoff (k + 1) : ℝ) * t
  apply ((P k).points.finite_toSet.image f).subset
  rintro x ⟨t, ht, -, rfl⟩
  exact ⟨t, ht, rfl⟩

theorem globalEndpoints_finite_Iic (P : ℕ → FiniteDivision) (R : ℝ) :
    (globalEndpoints P ∩ Iic R).Finite := by
  obtain ⟨N, hRN⟩ := exists_nat_gt R
  have hlate : ∀ k, N ≤ k → blockEndpoints P k ∩ Iic R = ∅ := by
    intro k hNk
    ext x
    constructor
    · rintro ⟨⟨t, ht, hleft, rfl⟩, hxR⟩
      change (blockCutoff (k + 1) : ℝ) * t ≤ R at hxR
      have hBN : (N : ℝ) ≤ blockCutoff k := by
        exact_mod_cast le_trans hNk
          (Nat.le_trans (Nat.le_add_right k 1) (nat_succ_le_blockCutoff k))
      nlinarith
    · simp
  have hblocks : (⋃ k ∈ (Finset.range N : Set ℕ), blockEndpoints P k).Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet (Finset.range N))
    intro k hk
    exact blockEndpoints_finite P k
  apply Set.Finite.subset ((Set.finite_singleton 1).insert 0 |>.union hblocks)
  rintro x ⟨hxS, hxR⟩
  rcases hxS with hx | hx
  · exact Or.inl hx
  · right
    simp only [mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    have hkN : k < N := by
      by_contra hn
      have : x ∈ blockEndpoints P k ∩ Iic R := ⟨hk, hxR⟩
      rw [hlate k (Nat.le_of_not_gt hn)] at this
      exact this
    exact Set.mem_iUnion_of_mem k
      (Set.mem_iUnion_of_mem (show k ∈ (Finset.range N : Set ℕ) by simpa using hkN) hk)

private theorem blockEndpoint_le_cutoff {P : ℕ → FiniteDivision} {k : ℕ} {x : ℝ}
    (hx : x ∈ blockEndpoints P k) : x ≤ blockCutoff (k + 1) := by
  obtain ⟨t, ht, -, rfl⟩ := hx
  have ht1 := ((P k).mem_unit t ht).2
  have hB : (0 : ℝ) ≤ blockCutoff (k + 1) := Nat.cast_nonneg _
  nlinarith

private theorem blockEndpoint_gt_cutoff {P : ℕ → FiniteDivision} {k : ℕ} {x : ℝ}
    (hx : x ∈ blockEndpoints P k) : (blockCutoff k : ℝ) < x := by
  obtain ⟨t, ht, hlt, rfl⟩ := hx
  exact hlt

/-- Inside the `k`th open block, the global endpoints are exactly the rescaled
endpoints of its finite division. -/
theorem mem_globalEndpoints_open_block_iff (P : ℕ → FiniteDivision) (k : ℕ) {x : ℝ}
    (hleft : (blockCutoff k : ℝ) < x)
    (hright : x ≤ blockCutoff (k + 1)) :
    x ∈ globalEndpoints P ↔
      ∃ t ∈ (P k).points, x = (blockCutoff (k + 1) : ℝ) * t := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with (rfl | rfl)
      · exact False.elim (not_lt_of_ge (Nat.cast_nonneg _) hleft)
      · cases k with
        | zero => simp at hleft
        | succ k =>
            have : (1 : ℝ) < blockCutoff (k + 1) := by
              exact_mod_cast blockCutoff_lt_succ 0 |>.trans_le
                (blockCutoff_strictMono.monotone (Nat.succ_le_succ (Nat.zero_le k)))
            linarith
    · simp only [mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      have hjk : j = k := by
        rcases lt_trichotomy j k with hjlt | rfl | hjgt
        · have hc : blockCutoff (j + 1) ≤ blockCutoff k :=
            blockCutoff_strictMono.monotone (Nat.succ_le_of_lt hjlt)
          have hxle := blockEndpoint_le_cutoff hj
          have hc' : (blockCutoff (j + 1) : ℝ) ≤ blockCutoff k := by exact_mod_cast hc
          exact False.elim (by linarith)
        · rfl
        · have hc : blockCutoff (k + 1) ≤ blockCutoff j :=
            blockCutoff_strictMono.monotone (Nat.succ_le_of_lt hjgt)
          have hxgt := blockEndpoint_gt_cutoff hj
          have hc' : (blockCutoff (k + 1) : ℝ) ≤ blockCutoff j := by exact_mod_cast hc
          exact False.elim (by linarith)
      subst j
      obtain ⟨t, ht, -, rfl⟩ := hj
      exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    right
    exact Set.mem_iUnion_of_mem k ⟨t, ht, hleft, rfl⟩

private theorem finiteDivision_exists_prev (P : FiniteDivision) {t : ℝ}
    (ht : t ∈ P.points) (ht0 : 0 < t) :
    ∃ u, Consecutive (P.points : Set ℝ) u t := by
  let Q := P.points.filter (· < t)
  have hQ : Q.Nonempty := ⟨0, by simp [Q, P.zero_mem, ht0]⟩
  let u := Q.max' hQ
  have huQ : u ∈ Q := Finset.max'_mem Q hQ
  have hut : u < t := (Finset.mem_filter.1 huQ).2
  refine ⟨u, (Finset.mem_filter.1 huQ).1, ht, hut, ?_⟩
  intro c hc huc
  by_contra htc
  have hct : c < t := lt_of_not_ge htc
  have hcmem : c ∈ P.points := hc
  have hcle : c ≤ u := Finset.le_max' Q c (by simp [Q, hcmem, hct])
  exact (not_le_of_gt huc) hcle

private theorem finiteDivision_exists_next (P : FiniteDivision) {t : ℝ}
    (ht : t ∈ P.points) (ht1 : t < 1) :
    ∃ u, Consecutive (P.points : Set ℝ) t u := by
  let Q := P.points.filter (t < ·)
  have hQ : Q.Nonempty := ⟨1, by simp [Q, P.one_mem, ht1]⟩
  let u := Q.min' hQ
  have huQ : u ∈ Q := Finset.min'_mem Q hQ
  have htu : t < u := (Finset.mem_filter.1 huQ).2
  refine ⟨u, ht, (Finset.mem_filter.1 huQ).1, htu, ?_⟩
  intro c hc htc
  by_cases hcu : c < u
  · have hcmem : c ∈ P.points := hc
    have hule : u ≤ c := Finset.min'_le Q c (by simp [Q, hcmem, htc])
    exact False.elim ((not_le_of_gt hcu) hule)
  · exact le_of_not_gt hcu

/-- The mesh requested of the finite division used in block `k`. -/
def blockEpsilon (k : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (k + 4) * blockCutoff (k + 1))

theorem blockEpsilon_pos (k : ℕ) : 0 < blockEpsilon k := by
  unfold blockEpsilon
  have hB : (0 : ℝ) < blockCutoff (k + 1) := by
    exact_mod_cast blockCutoff_pos (k + 1)
  exact div_pos (by norm_num) (mul_pos (pow_pos (by norm_num) _) hB)

private theorem scaled_blockEpsilon_le_one (k : ℕ) :
    (blockCutoff (k + 1) : ℝ) * blockEpsilon k ≤ 1 := by
  have hB : (blockCutoff (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (blockCutoff_pos (k + 1)))
  rw [blockEpsilon, div_eq_mul_inv]
  field_simp
  exact one_le_pow₀ (by norm_num)

/-- Every genuine consecutive gap in the spliced endpoint set has length at
most one. -/
theorem global_consecutive_gap_le_one (P : ℕ → FiniteDivision)
    (hFine : ∀ k, (P k).Fine (blockEpsilon k)) {a b : ℝ}
    (hab : Consecutive (globalEndpoints P) a b) : b - a ≤ 1 := by
  rcases hab.2.1 with hb | hb
  · rcases hb with (rfl | rfl)
    · exact False.elim ((not_lt_of_ge (globalEndpoints_nonneg P hab.1)) hab.2.2.1)
    · have ha0 := globalEndpoints_nonneg P hab.1
      change 0 ≤ a at ha0
      linarith
  · simp only [mem_iUnion] at hb
    obtain ⟨k, t, ht, hBt, rfl⟩ := hb
    have hBpos : (0 : ℝ) < blockCutoff (k + 1) := by
      exact_mod_cast blockCutoff_pos (k + 1)
    have ht0 : 0 < t := by
      have hk : (0 : ℝ) < blockCutoff k := by exact_mod_cast blockCutoff_pos k
      nlinarith
    obtain ⟨u, hut⟩ := finiteDivision_exists_prev (P k) ht ht0
    have hmesh := hFine k u t hut
    have hscaled : (blockCutoff (k + 1) : ℝ) * (t - u) < 1 :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hmesh hBpos)
        (scaled_blockEpsilon_le_one k)
    let c : ℝ := (blockCutoff (k + 1) : ℝ) * u
    have hcb : c < (blockCutoff (k + 1) : ℝ) * t := by
      dsimp [c]
      exact mul_lt_mul_of_pos_left hut.2.2.1 hBpos
    by_cases hcB : (blockCutoff k : ℝ) < c
    · have hcS : c ∈ globalEndpoints P := by
        right
        exact Set.mem_iUnion_of_mem k ⟨u, hut.1, hcB, rfl⟩
      have hca : c ≤ a := by
        by_contra hac
        exact (not_le_of_gt hcb) (hab.2.2.2 c hcS (lt_of_not_ge hac))
      exact le_of_lt <| calc
        (blockCutoff (k + 1) : ℝ) * t - a ≤
            (blockCutoff (k + 1) : ℝ) * t - c := sub_le_sub_left hca _
        _ = (blockCutoff (k + 1) : ℝ) * (t - u) := by dsimp [c]; ring
        _ < 1 := hscaled
    · have hBS := cutoff_mem_globalEndpoints P k
      have hBa : (blockCutoff k : ℝ) ≤ a := by
        by_contra haB
        exact (not_le_of_gt hBt) (hab.2.2.2 _ hBS (lt_of_not_ge haB))
      have hcBle : c ≤ blockCutoff k := le_of_not_gt hcB
      exact le_of_lt <| calc
        (blockCutoff (k + 1) : ℝ) * t - a ≤
            (blockCutoff (k + 1) : ℝ) * t - blockCutoff k := sub_le_sub_left hBa _
        _ ≤ (blockCutoff (k + 1) : ℝ) * t - c := sub_le_sub_left hcBle _
        _ = (blockCutoff (k + 1) : ℝ) * (t - u) := by dsimp [c]; ring
        _ < 1 := hscaled

private theorem consecutive_scale_to_global (P : ℕ → FiniteDivision) (k : ℕ)
    {u v : ℝ} (huBlock : (blockCutoff k : ℝ) < blockCutoff (k + 1) * u)
    (huv : Consecutive ((P k).points : Set ℝ) u v) :
    Consecutive (globalEndpoints P)
      ((blockCutoff (k + 1) : ℝ) * u) ((blockCutoff (k + 1) : ℝ) * v) := by
  have hBpos : (0 : ℝ) < blockCutoff (k + 1) := by
    exact_mod_cast blockCutoff_pos (k + 1)
  have hv1 := ((P k).mem_unit v huv.2.1).2
  refine ⟨?_, ?_, mul_lt_mul_of_pos_left huv.2.2.1 hBpos, ?_⟩
  · right
    exact Set.mem_iUnion_of_mem k ⟨u, huv.1, huBlock, rfl⟩
  · right
    exact Set.mem_iUnion_of_mem k
      ⟨v, huv.2.1, huBlock.trans (mul_lt_mul_of_pos_left huv.2.2.1 hBpos), rfl⟩
  · intro c hc huc
    by_cases hcR : c ≤ blockCutoff (k + 1)
    · obtain ⟨w, hw, hcw⟩ :=
        (mem_globalEndpoints_open_block_iff P k
          (huBlock.trans huc) hcR).1 hc
      rw [hcw]
      exact mul_le_mul_of_nonneg_left
        (huv.2.2.2 w hw (by nlinarith)) hBpos.le
    · have hvB : (blockCutoff (k + 1) : ℝ) * v ≤ blockCutoff (k + 1) := by
        nlinarith
      exact hvB.trans (le_of_not_ge hcR)

private theorem consecutive_scale_from_global (P : ℕ → FiniteDivision) (k : ℕ)
    {u v : ℝ} (hu : u ∈ (P k).points) (hv : v ∈ (P k).points)
    (huBlock : (blockCutoff k : ℝ) < blockCutoff (k + 1) * u)
    (huv : Consecutive (globalEndpoints P)
      ((blockCutoff (k + 1) : ℝ) * u) ((blockCutoff (k + 1) : ℝ) * v)) :
    Consecutive ((P k).points : Set ℝ) u v := by
  have hBpos : (0 : ℝ) < blockCutoff (k + 1) := by
    exact_mod_cast blockCutoff_pos (k + 1)
  have huvlt : u < v := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hBpos.le
    exact (not_le_of_gt huv.2.2.1) hmul
  refine ⟨hu, hv, huvlt, ?_⟩
  intro w hw huw
  have hwBlock : (blockCutoff k : ℝ) < blockCutoff (k + 1) * w :=
    huBlock.trans (mul_lt_mul_of_pos_left huw hBpos)
  have hwS : (blockCutoff (k + 1) : ℝ) * w ∈ globalEndpoints P := by
    right
    exact Set.mem_iUnion_of_mem k ⟨w, hw, hwBlock, rfl⟩
  have hh := huv.2.2.2 _ hwS (mul_lt_mul_of_pos_left huw hBpos)
  by_contra hvw
  have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hvw) hBpos
  exact (not_lt_of_ge hh) hmul

/-- Beyond one unit after the left cutoff, membership in the lower half of a
global cell is exactly membership in the corresponding rescaled finite cell. -/
theorem lowerRegion_global_iff (P : ℕ → FiniteDivision)
    (hFine : ∀ k, (P k).Fine (blockEpsilon k)) (k : ℕ) {x : ℝ}
    (hxL : (blockCutoff k : ℝ) + 1 ≤ x)
    (hxR : x < blockCutoff (k + 1)) :
    x ∈ lowerRegion (globalEndpoints P) (1 / 2) ↔
      x / blockCutoff (k + 1) ∈ lowerRegion ((P k).points : Set ℝ) (1 / 2) := by
  let B : ℝ := blockCutoff (k + 1)
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast blockCutoff_pos (k + 1)
  constructor
  · rintro ⟨a, b, hab, hax, hxab⟩
    have hgap := global_consecutive_gap_le_one P hFine hab
    have habpos := hab.2.2.1
    have haBlock : (blockCutoff k : ℝ) < a := by
      nlinarith
    have hxb : x < b := by nlinarith
    have hbR : b ≤ blockCutoff (k + 1) :=
      hab.2.2.2 _ (cutoff_mem_globalEndpoints P (k + 1)) (by nlinarith)
    have haR : a ≤ blockCutoff (k + 1) := le_trans hax hxR.le
    obtain ⟨u, hu, hau⟩ :=
      (mem_globalEndpoints_open_block_iff P k haBlock haR).1 hab.1
    obtain ⟨v, hv, hbv⟩ :=
      (mem_globalEndpoints_open_block_iff P k (haBlock.trans habpos) hbR).1 hab.2.1
    have huv : Consecutive ((P k).points : Set ℝ) u v := by
      apply consecutive_scale_from_global P k hu hv
      · rw [hau] at haBlock
        exact haBlock
      · simpa [hau, hbv] using hab
    refine ⟨u, v, huv, ?_, ?_⟩
    · rw [hau] at hax
      apply (le_div_iff₀ hBpos).2
      simpa [B, mul_comm] using hax
    · rw [hau, hbv] at hxab
      apply (div_lt_iff₀ hBpos).2
      have heq : (u + 1 / 2 * (v - u)) * B =
          B * u + 1 / 2 * (B * v - B * u) := by ring
      rw [heq]
      simpa [B] using hxab
  · rintro ⟨u, v, huv, huy, hyuv⟩
    have hmesh := hFine k u v huv
    have hscaled : B * (v - u) < 1 :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hmesh hBpos)
        (by simpa [B] using scaled_blockEpsilon_le_one k)
    have huBlock : (blockCutoff k : ℝ) < B * u := by
      have hxy : x < B * (u + (1 / 2) * (v - u)) := by
        apply (div_lt_iff₀ hBpos).mp at hyuv
        nlinarith [hyuv]
      nlinarith
    have hglobal := consecutive_scale_to_global P k huBlock huv
    refine ⟨B * u, B * v, by simpa [B] using hglobal, ?_, ?_⟩
    · have hh := (le_div_iff₀ hBpos).mp huy
      simpa [mul_comm] using hh
    · apply (div_lt_iff₀ hBpos).mp at hyuv
      nlinarith [hyuv]

/-- The actual global division sign agrees with the finite division throughout
the stable part of block `k`. -/
theorem divisionSign_global_eq (P : ℕ → FiniteDivision)
    (hFine : ∀ k, (P k).Fine (blockEpsilon k)) (k : ℕ) (x : ℝ)
    (hxL : (blockCutoff k : ℝ) + 1 ≤ x)
    (hxR : x < blockCutoff (k + 1)) :
    divisionSign (globalEndpoints P) x =
      divisionSign ((P k).points : Set ℝ) (x / blockCutoff (k + 1)) := by
  simp only [divisionSign]
  rw [lowerRegion_global_iff P hFine k hxL hxR]

end

end Erdos492Real
