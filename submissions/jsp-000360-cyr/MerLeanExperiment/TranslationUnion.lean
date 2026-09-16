import MerLeanExperiment.TranslationDefinitions
import MerLeanExperiment.TranslationCollision

namespace Erdos441

theorem translated_good_union_card {K : ℕ} (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r) (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) (hleft : ∀ i, a i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ)) (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ (shiftParityWeight (r i) (r j) : ℝ) * a i * a j) (A : Finset ℕ) (hA : LcmBounded N A) (H : ℤ) : (goodTranslateUnion A (shiftProductNat M r ell) (shiftedPoint M r ell) H).card ≤ H.toNat := by
  classical
  unfold goodTranslateUnion
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 H,
        ((Finset.univ.filter fun i => (shiftedPoint M r ell i + 2 * h).natAbs ∈ A ∧
          Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
            (shiftProductNat M r ell)).image fun i =>
              (shiftedPoint M r ell i + 2 * h).natAbs).card := Finset.card_biUnion_le
    _ ≤ ∑ _h ∈ Finset.Icc 1 H, 1 := by
      apply Finset.sum_le_sum
      intro h hh
      exact Finset.card_image_le.trans
        (at_most_one_translated_shift M N hM hN r ell hr hsize a ha hleft hsep A hA h
          (by have := (Finset.mem_Icc.mp hh).1; omega))
    _ = H.toNat := by simp

end Erdos441

#print axioms Erdos441.translated_good_union_card
