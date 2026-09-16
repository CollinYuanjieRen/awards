import MerLeanExperiment.Subdivision

open Filter Set
open scoped Topology

namespace Erdos492Real

noncomputable section

private theorem exists_least_greater (S : Set ℝ)
    (hfinite : ∀ R, (S ∩ Iic R).Finite)
    (hunbounded : ∀ R, ∃ x ∈ S, R < x) (x : ℝ) :
    ∃ y ∈ S, x < y ∧ ∀ z ∈ S, x < z → y ≤ z := by
  obtain ⟨b, hbS, hxb⟩ := hunbounded x
  let T : Finset ℝ := (hfinite b).toFinset.filter (x < ·)
  have hbT : b ∈ T := by simp [T, hbS, hxb]
  let y := T.min' ⟨b, hbT⟩
  have hyT : y ∈ T := Finset.min'_mem T ⟨b, hbT⟩
  have hyinfo : y ∈ S ∩ Iic b ∧ x < y := by simpa [T] using hyT
  refine ⟨y, hyinfo.1.1, hyinfo.2, ?_⟩
  intro z hzS hxz
  by_cases hzb : z ≤ b
  · exact Finset.min'_le T z (by simp [T, hzS, hxz, hzb])
  · exact (Finset.min'_le T b hbT).trans (le_of_lt (lt_of_not_ge hzb))

private noncomputable def nextEndpoint (S : Set ℝ)
    (hfinite : ∀ R, (S ∩ Iic R).Finite)
    (hunbounded : ∀ R, ∃ x ∈ S, R < x) (x : ℝ) : ℝ :=
  Classical.choose (exists_least_greater S hfinite hunbounded x)

private theorem nextEndpoint_spec (S : Set ℝ)
    (hfinite : ∀ R, (S ∩ Iic R).Finite)
    (hunbounded : ∀ R, ∃ x ∈ S, R < x) (x : ℝ) :
    nextEndpoint S hfinite hunbounded x ∈ S ∧
      x < nextEndpoint S hfinite hunbounded x ∧
      ∀ z ∈ S, x < z → nextEndpoint S hfinite hunbounded x ≤ z :=
  Classical.choose_spec (exists_least_greater S hfinite hunbounded x)

private noncomputable def endpointSequence (S : Set ℝ)
    (hfinite : ∀ R, (S ∩ Iic R).Finite)
    (hunbounded : ∀ R, ∃ x ∈ S, R < x) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextEndpoint S hfinite hunbounded (endpointSequence S hfinite hunbounded n)

theorem exists_endpoint_enumeration (S : Set ℝ) (hzero : 0 ∈ S)
    (hnonneg : S ⊆ Ici 0) (hfinite : ∀ R, (S ∩ Iic R).Finite)
    (hunbounded : ∀ R, ∃ x ∈ S, R < x) :
    ∃ a : ℕ → ℝ, a 0 = 0 ∧ StrictMono a ∧ range a = S ∧
      Tendsto a atTop atTop := by
  let a := endpointSequence S hfinite hunbounded
  have ha0 : a 0 = 0 := rfl
  have haS : ∀ n, a n ∈ S := by
    intro n
    cases n with
    | zero => exact hzero
    | succ n => exact (nextEndpoint_spec S hfinite hunbounded (a n)).1
  have hstep : ∀ n, a n < a (n + 1) := fun n =>
    (nextEndpoint_spec S hfinite hunbounded (a n)).2.1
  have hmono : StrictMono a := strictMono_nat_of_lt_succ hstep
  have hub : ∀ R : ℝ, ∃ n, R < a n := by
    intro R
    by_contra h
    push Not at h
    have hrangefin : (range a).Finite := (hfinite R).subset <| by
      rintro y ⟨n, rfl⟩
      exact ⟨haS n, h n⟩
    exact (Set.infinite_range_of_injective hmono.injective) hrangefin
  have htend : Tendsto a atTop atTop := by
    rw [hmono.monotone.tendsto_atTop_atTop_iff]
    exact fun R => let ⟨n, hn⟩ := hub R; ⟨n, hn.le⟩
  have hrange : range a = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨n, rfl⟩
      exact haS n
    · intro s hs
      obtain ⟨k, hk⟩ := hub s
      let n := Nat.find (p := fun n => s < a n) ⟨k, hk⟩
      have hn : s < a n := Nat.find_spec (p := fun n => s < a n) ⟨k, hk⟩
      have hn0 : n ≠ 0 := by
        intro hnzero
        have : s < a 0 := hnzero ▸ hn
        exact (not_lt_of_ge (hnonneg hs)) (ha0 ▸ this)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hmle : a m ≤ s := by
        apply le_of_not_gt
        intro hgreater
        have hnle := Nat.find_min' (p := fun n => s < a n) ⟨k, hk⟩ hgreater
        omega
      by_cases hms : a m = s
      · exact ⟨m, hms⟩
      · have hams : a m < s := lt_of_le_of_ne hmle hms
        have hnext := (nextEndpoint_spec S hfinite hunbounded (a m)).2.2 s hs hams
        have hanext : a n = nextEndpoint S hfinite hunbounded (a m) := by
          rw [hm]
          rfl
        exact False.elim ((not_le_of_gt hn) (hanext ▸ hnext))
  exact ⟨a, ha0, hmono, hrange, htend⟩

theorem endpoint_enumeration_consecutive {S : Set ℝ} {a : ℕ → ℝ}
    (hrange : range a = S) (hmono : StrictMono a) (n : ℕ) :
    Consecutive S (a n) (a (n + 1)) := by
  refine ⟨hrange ▸ ⟨n, rfl⟩, hrange ▸ ⟨n + 1, rfl⟩,
    hmono (Nat.lt_succ_self n), ?_⟩
  intro c hc hac
  rw [← hrange] at hc
  obtain ⟨k, rfl⟩ := hc
  exact hmono.monotone (Nat.succ_le_of_lt (hmono.lt_iff_lt.mp hac))

theorem consecutive_eq_adjacent {S : Set ℝ} {a : ℕ → ℝ}
    (hrange : range a = S) (hmono : StrictMono a) {x y : ℝ}
    (hxy : Consecutive S x y) :
    ∃ n, x = a n ∧ y = a (n + 1) := by
  rw [← hrange] at hxy
  obtain ⟨m, rfl⟩ := hxy.1
  obtain ⟨n, rfl⟩ := hxy.2.1
  have hmn : m < n := hmono.lt_iff_lt.mp hxy.2.2.1
  have hle : a n ≤ a (m + 1) := hxy.2.2.2 _ ⟨m + 1, rfl⟩
    (hmono (Nat.lt_succ_self m))
  have hnm : n ≤ m + 1 := hmono.le_iff_le.mp hle
  have hnEq : n = m + 1 := Nat.le_antisymm hnm (Nat.succ_le_of_lt hmn)
  exact ⟨m, rfl, congrArg a hnEq⟩

theorem lowerRegion_eq_sequenceRegion {S : Set ℝ} {a : ℕ → ℝ}
    (hrange : range a = S) (hmono : StrictMono a) (lam : ℝ) :
    lowerRegion S lam = sequenceRegion a lam := by
  ext x
  constructor
  · rintro ⟨u, v, huv, hux, hxv⟩
    obtain ⟨n, rfl, rfl⟩ := consecutive_eq_adjacent hrange hmono huv
    exact ⟨n, hux, hxv⟩
  · rintro ⟨n, hnx, hxn⟩
    exact ⟨a n, a (n + 1), endpoint_enumeration_consecutive hrange hmono n,
      hnx, hxn⟩

theorem tendsto_ratio_of_bounded_gaps {a : ℕ → ℝ} (_ha0 : a 0 = 0)
    (hmono : StrictMono a) (hatTop : Tendsto a atTop atTop)
    (hgap : ∀ n, a (n + 1) - a n ≤ 1) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n in atTop, 0 < a n := hatTop (eventually_gt_atTop 0)
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hatTop
  have hquot : Tendsto (fun n => (a (n + 1) - a n) / a n)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hpos] with n han
      exact div_nonneg (sub_nonneg.mpr (hmono.monotone (Nat.le_succ n))) han.le
    · filter_upwards [hpos] with n han
      simpa [one_div] using div_le_div_of_nonneg_right (hgap n) han.le
    · simpa [one_div] using hinv
  have hadd : Tendsto (fun n => (1 : ℝ) + (a (n + 1) - a n) / a n)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hquot
  apply hadd.congr'
  filter_upwards [hpos] with n han
  field_simp
  ring


end

end Erdos492Real
