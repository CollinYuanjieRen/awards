import ErdosProblems.Erdos344

/-!
Occurrence-preserving divisor extraction for the finite multiset theorem.
Adapts the credited plby Erdos344 descent, retaining indices with equal weights.
-/

namespace Jsp285

/-- Finite divisor descent that retains occurrence indices, so repeated weights never merge. -/
theorem exists_divisorExtractionAux {ι : Type*} [DecidableEq ι]
    (B L K d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ι) (v : ι → ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ι, ∃ w : ι → ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧ Z ⊆ Y ∧
      (∀ i ∈ Z, q * w i = v i) ∧
      Y.card - Z.card ≤ L * factors.length + K * factors.sum ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ (Z.filter fun i ↦ ¬e ∣ w i).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y v with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (Y.filter fun i ↦ ¬e ∣ v i).card < L + K * e
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := Y.filter fun i ↦ e ∣ v i
        let v' : ι → ℕ := fun i ↦ v i / e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, w, factors, hq, hqprod, hfactors, hdqB, hZY', hscale,
            hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' v' rfl
        refine ⟨e * q, Z, w, e :: factors, Nat.mul_pos hepos hq, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun hae ↦ hae ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · exact hZY'.trans (Finset.filter_subset _ _)
        · intro i hi
          have hiY' : i ∈ Y' := hZY' hi
          have hediv : e ∣ v i := (Finset.mem_filter.mp hiY').2
          calc
            (e * q) * w i = e * (q * w i) := by ring
            _ = e * v' i := by rw [hscale i hi]
            _ = v i := by
              simp only [v']
              exact Nat.mul_div_cancel' hediv
        · have hZle : Z.card ≤ Y'.card :=
            Finset.card_le_card hZY'
          have hY'le : Y'.card ≤ Y.card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          have hfilter : Y'.card + (Y.filter fun i ↦ ¬e ∣ v i).card = Y.card := by
            simpa only [Y'] using
              Finset.card_filter_add_card_filter_not (s := Y) (fun i ↦ e ∣ v i)
          have hfirst : Y.card - Y'.card ≤ L + K * e := by omega
          rw [hsplit]
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e) +
                  (L * factors.length + K * factors.sum) :=
              Nat.add_le_add hfirst hloss
            _ = L * (e :: factors).length + K * (e :: factors).sum := by
              simp only [List.length_cons, List.sum_cons]
              ring
        · intro a ha hbound
          exact hdiverse a ha (by simpa [mul_assoc] using hbound)
      · refine ⟨1, Y, v, [], by omega, by simp, by simp, ?_, by simp, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using Nat.lt_of_not_ge hnot

end Jsp285
