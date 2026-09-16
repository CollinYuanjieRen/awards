import MerLeanExperiment.SquarePartition
import MerLeanExperiment.SignedCollision

/-! Canonical square component of Erdős 318, as stated in formal-conjectures
40e7c98697de6f66b8cbdbf641749ab39ed9c152. The source's `answer(True)` elaborates
to `True` with a metadata annotation. The definition `Erdos318.P₁` is copied
verbatim in Erdos318Definitions; no reference theorem is imported. -/

namespace Erdos318

/-- Every nonconstant signing of the squares other than one has a finite,
nonempty subset with signed reciprocal sum zero. -/
theorem erdos_318.parts.ii : True ↔ P₁ ({n | IsSquare n} \ {1}) := by
  constructor
  · intro _ f hplus hminus hrange
    obtain ⟨hx, hy⟩ := ReciprocalSquares.signed_square_color_witnesses
      f hplus hminus hrange
    obtain ⟨x, hxgt, hxsq, hxf⟩ := hx
    obtain ⟨y, hygt, hysq, hyf⟩ := hy
    obtain ⟨A, B, hAne, _hBne, hA, hB, heq⟩ :=
      ReciprocalSquares.square_partition {n | f n = 1}
        ⟨x, hxgt, hxsq, hxf⟩ ⟨y, hygt, hysq, by simpa only [Set.mem_ofPred_eq, hyf] using (by norm_num : (-1 : ℝ) ≠ 1)⟩
    apply ReciprocalSquares.signed_zero_sum_of_equal_reciprocals f A B hAne hA
      (fun n hn => ?_) heq
    obtain ⟨hn, hsq, hnot⟩ := hB n hn
    have hsigned : f n = 1 ∨ f n = -1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        hrange (Set.mem_range_self n)
    exact ⟨hn, hsq, hsigned.resolve_left hnot⟩
  · intro _
    trivial

end Erdos318
