import Jsp285.PreparedOccurrences
import Jsp285.OccurrencePartition
import Jsp285.OccupiedBalance

/-! Balanced depth-49 leaves from prepared occurrence indices. -/

namespace Jsp285

/-- Prepared occurrence weights have a depth-49 partition whose leaves retain
divisor diversity and a fixed proportion of the total weight. -/
theorem exists_balanced_occurrence_partition
    {ι : Type*} [DecidableEq ι] (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (_hdn : d ≤ n) (w : ι → ℕ) (S : Finset ι)
    (hbox : ∀ i ∈ S, 0 < w i ∧ w i ≤ n / d)
    (hcount : 39999 * partitionMass * n ≤ S.card)
    (hdiv : ∀ e : ℕ, 1 < e → d * e ≤ n →
      10000 * partitionMass * (Nat.log 2 n + 1) + partitionMass * e ≤
        (S.filter fun i ↦ ¬e ∣ w i).card)
    (hbin : ∀ j : ℕ, (dyadicBin w S j).Nonempty →
      10000 * partitionMass * (Nat.log 2 n + 1) ≤
        (dyadicBin w S j).card) :
    ∃ T : Erdos344.PartitionTree ι 49,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        C ⊆ S ∧
        (∀ e : ℕ, 1 < e → e ≤ n / d →
          e - 1 ≤ (C.filter fun i ↦ ¬e ∣ w i).card) ∧
        89 ^ 49 * (∑ i ∈ S, w i) ≤
          2 * partitionMass * (∑ i ∈ C, w i) ∧
        partitionMass * (∑ i ∈ C, w i) ≤
          2 * 111 ^ 49 * (∑ i ∈ S, w i) := by
  let Q := 10000 * partitionMass * (Nat.log 2 n + 1)
  let E := Finset.Icc 2 (n / d)
  let Jbins := (Finset.range (Nat.log 2 n + 1)).filter fun j ↦
    (dyadicBin w S j).Nonempty
  let m := 1 + E.card + Jbins.card
  have hr : Nat.log 2 n + 1 ≤ n := by
    exact Nat.lt_succ_iff.mp <| Nat.add_lt_add_right
      (Nat.log_lt_self 2 hn.ne') 1
  have hEcard : E.card ≤ n := by
    dsimp only [E]
    rw [Nat.card_Icc]
    have hdivle := Nat.div_le_self n d
    omega
  have hJcard : Jbins.card ≤ n := by
    calc
      Jbins.card ≤ (Finset.range (Nat.log 2 n + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.log 2 n + 1 := by simp
      _ ≤ n := hr
  have hm : m ≤ 3 * n := by
    dsimp only [m]
    omega
  have hQ : Q ≤ S.card := by
    have hscaled := Nat.mul_le_mul_left (10000 * partitionMass) hr
    have hQcount : Q ≤ 39999 * partitionMass * n := by
      dsimp only [Q]
      nlinarith [Nat.zero_le (partitionMass * n)]
    exact hQcount.trans hcount
  have hQthreshold :
      (1000 * (Nat.log 2 (2 * (1 + E.card + Jbins.card) + 1) + 1)) *
          200 ^ 49 ≤ Q := by
    have hthreshold := tracking_threshold_le n m partitionMass hn hm
    simpa only [m, Q, partitionMass] using hthreshold
  have hdivTracked : ∀ e ∈ E, Q ≤ (S.filter fun i ↦ ¬e ∣ w i).card := by
    intro e he
    have heIcc := Finset.mem_Icc.mp he
    have hde : d * e ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp heIcc.2
    exact (Nat.le_add_right Q (partitionMass * e)).trans
      (hdiv e heIcc.1 hde)
  have hbinTracked : ∀ j ∈ Jbins, Q ≤ (dyadicBin w S j).card := by
    intro j hj
    exact hbin j (Finset.mem_filter.mp hj).2
  obtain ⟨T, hTcarrier, hTdisj, hTleaves⟩ :=
    exists_dyadic_diverse_partition w 49 S Q E Jbins hQ hdivTracked
      hbinTracked hQthreshold
  refine ⟨T, hTcarrier, hTdisj, ?_⟩
  refine (hTleaves.and (Erdos344.PartitionTree.allLeaves_subset_carrier T)).mono ?_
  rintro C ⟨hraw, hCcarrier⟩
  have hCS : C ⊆ S := by simpa only [hTcarrier] using hCcarrier
  refine ⟨hCS, ?_, ?_⟩
  · intro e he heN
    have heE : e ∈ E := Finset.mem_Icc.mpr ⟨he, heN⟩
    have hde : d * e ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp heN
    have hclassS := hdiv e he hde
    have hclassRaw := (hraw.2.1 e heE).1
    have hinter : C ∩ (S.filter fun i ↦ ¬e ∣ w i) =
        C.filter fun i ↦ ¬e ∣ w i := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hCS h.1, h.2⟩⟩
    rw [hinter] at hclassRaw
    have hmassPos : 0 < partitionMass := by norm_num [partitionMass]
    have hone : (S.filter fun i ↦ ¬e ∣ w i).card ≤
        89 ^ 49 * (S.filter fun i ↦ ¬e ∣ w i).card := by
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    change 89 ^ 49 * (S.filter fun i ↦ ¬e ∣ w i).card ≤
      partitionMass * (C.filter fun i ↦ ¬e ∣ w i).card at hclassRaw
    change Q + partitionMass * e ≤ _ at hclassS
    have hHe : partitionMass * e ≤
        (S.filter fun i ↦ ¬e ∣ w i).card := by omega
    have hprod : partitionMass * e ≤
        partitionMass * (C.filter fun i ↦ ¬e ∣ w i).card :=
      hHe.trans <| hone.trans hclassRaw
    have heCard := Nat.le_of_mul_le_mul_left hprod hmassPos
    omega
  · have hSbox : ∀ i ∈ S, 0 < w i ∧ w i ≤ n := by
      intro i hi
      exact ⟨(hbox i hi).1, (hbox i hi).2.trans (Nat.div_le_self n d)⟩
    apply dyadic_weight_balance_occupied w S C n (89 ^ 49)
      partitionMass (111 ^ 49) hSbox hCS
    intro j hj hjne
    have hjJ : j ∈ Jbins := Finset.mem_filter.mpr ⟨hj, hjne⟩
    simpa only [partitionMass] using hraw.2.2 j hjJ

end Jsp285
