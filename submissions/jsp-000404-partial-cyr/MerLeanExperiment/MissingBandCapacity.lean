import MerLeanExperiment.WeightedBandCode

/-!
A missing incident angular band yields one extra Boolean codeword. This is a
finite combinatorial interface for a later geometric endpoint argument.
-/

namespace PlanarMinimax

noncomputable def incidentBand {V : Type*} [LinearOrder V]
    (theta : V → V → ℝ) (h : ℝ) (k : ℕ) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun m ↦
    ∃ w, (w < v ∧ (m : ℝ) ≤ theta w v / h ∧ theta w v / h < (m : ℝ) + 1) ∨
      (v < w ∧ (m : ℝ) ≤ theta v w / h ∧ theta v w / h < (m : ℝ) + 1)

private def bandIncoming {V : Type*} [LinearOrder V]
    (theta : V → V → ℝ) (h : ℝ) (m : Fin k) (v : V) : Prop :=
  ∃ w, w < v ∧ (m : ℝ) ≤ theta w v / h ∧ theta w v / h < (m : ℝ) + 1

theorem missingBand_capacity {V : Type*} [LinearOrder V] [Fintype V]
    (theta : V → V → ℝ) (h : ℝ) (k : ℕ) (hh : 0 < h)
    (hrange : ∀ ⦃i j : V⦄, i < j → 0 ≤ theta i j ∧ theta i j < (k : ℝ) * h)
    (hsep : ∀ ⦃i j l : V⦄, i < j → j < l → h ≤ |theta i j - theta j l|)
    (v : V) (m : Fin k) (hmissing : m ∉ incidentBand theta h k v) :
    Fintype.card V + 1 ≤ 2 ^ k := by
  classical
  let code : V → Fin k → Bool := fun j n ↦ decide (bandIncoming theta h n j)
  have hweighted : ∑ x, 2 ^ (k - (incidentBand theta h k x).card) ≤ 2 ^ k := by
    apply WeightedBandCode.weightedBandCode_capacity code (incidentBand theta h k)
    intro i j hij
    wlog hlt : i < j generalizing i j
    · have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) hij.symm
      obtain ⟨n, hnj, hni, hc⟩ := this j i hij.symm hji
      exact ⟨n, hni, hnj, hc.symm⟩
    have hq0 : 0 ≤ theta i j / h := div_nonneg (hrange hlt).1 hh.le
    have hqk : theta i j / h < (k : ℝ) := by
      rw [div_lt_iff₀ hh]
      simpa [mul_comm] using (hrange hlt).2
    have hnlt : Nat.floor (theta i j / h) < k := (Nat.floor_lt hq0).2 hqk
    let n : Fin k := ⟨Nat.floor (theta i j / h), hnlt⟩
    have hnlo : (n : ℝ) ≤ theta i j / h := by
      simpa [n] using Nat.floor_le hq0
    have hnhi : theta i j / h < (n : ℝ) + 1 := by
      simpa [n] using Nat.lt_floor_add_one (theta i j / h)
    have hni : n ∈ incidentBand theta h k i := by
      simp only [incidentBand, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, Or.inr ⟨hlt, hnlo, hnhi⟩⟩
    have hnj : n ∈ incidentBand theta h k j := by
      simp only [incidentBand, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, Or.inl ⟨hlt, hnlo, hnhi⟩⟩
    have hinj : bandIncoming theta h n j := ⟨i, hlt, hnlo, hnhi⟩
    have hnotin : ¬ bandIncoming theta h n i := by
      rintro ⟨a, hai, halo, hahi⟩
      have hlarge : 1 ≤ |theta a i / h - theta i j / h| := by
        rw [← sub_div, abs_div, abs_of_pos hh]
        calc
          1 = h / h := (div_self hh.ne').symm
          _ ≤ |theta a i - theta i j| / h :=
            (div_le_div_iff_of_pos_right hh).2 (hsep hai hlt)
      have hsmall : |theta a i / h - theta i j / h| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      exact (not_lt_of_ge hlarge) hsmall
    refine ⟨n, hni, hnj, ?_⟩
    simp [code, hnotin, hinj]
  have hmcard : (incidentBand theta h k v).card < k := by
    have hle := Finset.card_le_univ (incidentBand theta h k v)
    have hle' : (incidentBand theta h k v).card ≤ k := by simpa using hle
    have hne : (incidentBand theta h k v).card ≠ k := by
      intro heq
      have hall : incidentBand theta h k v = Finset.univ :=
        Finset.eq_univ_of_card (incidentBand theta h k v) (by simpa using heq)
      exact hmissing (by simp [hall])
    omega
  have hpoint : ∀ x : V, (if x = v then 2 else 1) ≤
      2 ^ (k - (incidentBand theta h k x).card) := by
    intro x
    split_ifs with hx
    · subst x
      have hexp : 1 ≤ k - (incidentBand theta h k v).card := by omega
      simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hexp)
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hlower : Fintype.card V + 1 ≤
      ∑ x, 2 ^ (k - (incidentBand theta h k x).card) := by
    calc
      Fintype.card V + 1 = ∑ x : V, (if x = v then 2 else 1) := by
        simp_rw [show ∀ x : V, (if x = v then 2 else 1) =
            1 + if x = v then 1 else 0 by
          intro x
          split <;> simp_all]
        simp [Finset.sum_add_distrib]
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ hpoint x
  exact hlower.trans hweighted

#print axioms missingBand_capacity

end PlanarMinimax
