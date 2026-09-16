import Jsp285.OccurrenceDyadic
import ErdosProblems.Erdos344

/-!
Occurrence-indexed simultaneous divisor and dyadic partition.
Adapted from plby Erdos344.exists_dyadic_diverse_partition with attribution retained.
-/

namespace Jsp285

open Erdos344

/-- Balance the full carrier, divisor classes and specified dyadic bins simultaneously. -/
theorem exists_dyadic_diverse_partition {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (t : ℕ) (S : Finset ι) (Q : ℕ) (E Jbins : Finset ℕ)
    (hwhole : Q ≤ S.card)
    (hdiv : ∀ e ∈ E, Q ≤ (S.filter fun x ↦ ¬e ∣ v x).card)
    (hbin : ∀ j ∈ Jbins,
      Q ≤ (dyadicBin v S j).card)
    (hQ : (1000 * (Nat.log 2
        (2 * (1 + E.card + (Jbins).card) + 1) + 1)) *
        200 ^ t ≤ Q) :
    ∃ T : PartitionTree ι t,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        (89 ^ t * S.card ≤ 200 ^ t * C.card ∧
          200 ^ t * C.card ≤ 111 ^ t * S.card) ∧
        (∀ e ∈ E,
          89 ^ t * (S.filter fun x ↦ ¬e ∣ v x).card ≤
              200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ v x)).card ∧
          200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ v x)).card ≤
              111 ^ t * (S.filter fun x ↦ ¬e ∣ v x).card) ∧
        (∀ j ∈ Jbins,
          89 ^ t * (dyadicBin v S j).card ≤
              200 ^ t * (C ∩ dyadicBin v S j).card ∧
          200 ^ t * (C ∩ dyadicBin v S j).card ≤
              111 ^ t * (dyadicBin v S j).card) := by
  classical
  let κ := Unit ⊕ (ℕ ⊕ ℕ)
  let Jwhole : Finset κ := {Sum.inl ()}
  let Jdiv : Finset κ := E.image fun e ↦ Sum.inr (Sum.inl e)
  let Jbin : Finset κ :=
    (Jbins).image fun j ↦ Sum.inr (Sum.inr j)
  let J := Jwhole ∪ Jdiv ∪ Jbin
  let F : κ → Finset ι
    | Sum.inl _ => S
    | Sum.inr (Sum.inl e) => S.filter fun x ↦ ¬e ∣ v x
    | Sum.inr (Sum.inr j) => dyadicBin v S j
  have hJcard : J.card ≤
      1 + E.card + (Jbins).card := by
    calc
      J.card ≤ (Jwhole ∪ Jdiv).card + Jbin.card := Finset.card_union_le _ _
      _ ≤ (Jwhole.card + Jdiv.card) + Jbin.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 1 + E.card + (Jbins).card := by
        have hdivCard : Jdiv.card ≤ E.card := by
          dsimp only [Jdiv]
          exact Finset.card_image_le
        have hbinCard : Jbin.card ≤ (Jbins).card := by
          dsimp only [Jbin]
          exact Finset.card_image_le
        simp only [Jwhole, Finset.card_singleton]
        omega
  have hlog : Nat.log 2 (2 * J.card + 1) ≤
      Nat.log 2
        (2 * (1 + E.card + (Jbins).card) + 1) := by
    apply Nat.log_mono_right
    omega
  have hsub : ∀ z ∈ J, F z ⊆ S := by
    intro z hz
    rcases z with _ | z
    · exact Finset.Subset.rfl
    · rcases z with e | j
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
  have hlarge : ∀ z ∈ J,
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
        89 ^ t * (F z).card := by
    intro z hz
    have hthreshold :
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := by
      calc
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
            (1000 * (Nat.log 2
              (2 * (1 + E.card +
                (Jbins).card) + 1) + 1)) * 200 ^ t := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add_right hlog 1
        _ ≤ Q := hQ
    have hFQ : Q ≤ (F z).card := by
      rcases z with z | z
      · simpa [F] using hwhole
      · rcases z with e | j
        · have hzdiv : Sum.inr (Sum.inl e) ∈ Jdiv := by
            have hz' : Sum.inr (Sum.inl e) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inl e) ∈ Jbin := Finset.mem_union.mp hz
            rcases hz' with hz' | hzbin
            · exact (Finset.mem_union.mp hz').resolve_left (by simp [Jwhole])
            · exfalso
              simp [Jbin] at hzbin
          have he : e ∈ E := by simpa [Jdiv] using hzdiv
          simpa [F] using hdiv e he
        · have hzbin : Sum.inr (Sum.inr j) ∈ Jbin := by
            have hz' : Sum.inr (Sum.inr j) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inr j) ∈ Jbin := Finset.mem_union.mp hz
            exact hz'.resolve_left (by
              intro h
              rcases Finset.mem_union.mp h with hw | hd
              · simp [Jwhole] at hw
              · simp [Jdiv] at hd)
          have hj : j ∈ Jbins := by
            simpa [Jbin] using hzbin
          simpa [F] using hbin j hj
    calc
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := hthreshold
      _ ≤ (F z).card := hFQ
      _ = 1 * (F z).card := by simp
      _ ≤ 89 ^ t * (F z).card :=
        Nat.mul_le_mul_right (F z).card (one_le_pow₀ (by omega))
  obtain ⟨T, hTcarrier, hTdisj, hTleaves⟩ :=
    PartitionTree.exists_tight_partition t S J F hsub hlarge
  refine ⟨T, hTcarrier, hTdisj, ?_⟩
  refine (hTleaves.and (PartitionTree.allLeaves_subset_carrier T)).mono ?_
  rintro C ⟨hC, hCsub⟩
  have hCS : C ⊆ S := by simpa [hTcarrier] using hCsub
  have hwholeMem : Sum.inl () ∈ J := by simp [J, Jwhole]
  have hwholeRatio := hC (Sum.inl ()) hwholeMem
  have hwholeInter : C ∩ S = C := Finset.inter_eq_left.mpr hCS
  refine ⟨by simpa [F, hwholeInter] using hwholeRatio, ?_, ?_⟩
  · intro e he
    have hz : Sum.inr (Sum.inl e) ∈ J := by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inl e)) hz
  · intro j hj
    have hz : Sum.inr (Sum.inr j) ∈ J := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inr j)) hz


end Jsp285
