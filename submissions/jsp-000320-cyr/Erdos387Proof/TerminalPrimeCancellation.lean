import Erdos387Proof.MaskedReciprocalPhase
import ErdosProblems.Erdos387.RationalStepanovExtensionSum

/-!
# Complete prime sums with the original denominator mask

The paired-shift and simple-pole results are from pinned plby/lean-proofs
8822f7ddef30fadbd92e1c6ab4ed897af356af5e. This adapter retains the original
unit mask of `MaskedReciprocalPhase`, even where rational poles cancel.
No bound on the size or sign of an integer shift is assumed.
-/

namespace Erdos387Proof.TerminalPrimeCancellation

open scoped BigOperators ComplexConjugate
open Erdos387
open MaskedReciprocalPhase

noncomputable def originalRoots (p : ℕ) [NeZero p] (a : ℤ) :
    List (ℤ × ℤ) → Finset (ZMod p)
  | [] => {-(a : ZMod p)}
  | (u,v)::hs =>
      (originalRoots p a hs).image (fun x => x - (u : ZMod p)) ∪
      (originalRoots p a hs).image (fun x => x - (v : ZMod p))

noncomputable def coefficients (p : ℕ) [NeZero p] (c a : ℤ)
    (hs : List (ℤ × ℤ)) : ZMod p → ZMod p :=
  InverseRational.iteratedDifferenceCoefficient
    (InverseRational.singlePoleCoefficient (c : ZMod p) (-(a : ZMod p)))
    (hs.map fun uv => ((uv.1 : ZMod p), (uv.2 : ZMod p)))

private theorem mem_image_sub_iff {p : ℕ} [NeZero p]
    (R : Finset (ZMod p)) (t x : ZMod p) :
    x ∈ R.image (fun r => r-t) ↔ x+t ∈ R := by
  classical
  constructor
  · intro hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
    simpa using hr
  · intro hx
    exact Finset.mem_image.mpr ⟨x+t,hx,by ring⟩

theorem card_originalRoots_le (p : ℕ) [NeZero p] (a : ℤ)
    (hs : List (ℤ × ℤ)) : (originalRoots p a hs).card ≤ 2^hs.length := by
  classical
  induction hs with
  | nil => simp [originalRoots]
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    calc
      (originalRoots p a ((u,v)::hs)).card ≤
          ((originalRoots p a hs).image (fun x => x-(u : ZMod p))).card +
          ((originalRoots p a hs).image (fun x => x-(v : ZMod p))).card :=
        Finset.card_union_le _ _
      _ ≤ (originalRoots p a hs).card + (originalRoots p a hs).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ ≤ 2^hs.length + 2^hs.length := Nat.add_le_add ih ih
      _ = 2^((u,v)::hs).length := by simp [pow_succ]; omega

/-- Failure of the exact denominator mask is a union of at most `2^j` roots. -/
theorem good_iff_not_mem_originalRoots (p : ℕ) [NeZero p] [Fact p.Prime]
    (a : ℤ) (hs : List (ℤ × ℤ)) (n : ℤ) :
    good p a hs n ↔ (n : ZMod p) ∉ originalRoots p a hs := by
  classical
  induction hs generalizing n with
  | nil =>
    simp only [good, isUnit_iff_ne_zero, originalRoots, Finset.mem_singleton,
      Int.cast_add]
    constructor
    · intro h he
      apply h
      rw [he]
      ring
    · intro h he
      apply h
      linear_combination he
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    simp only [good, ih, originalRoots, Finset.mem_union, mem_image_sub_iff,
      Int.cast_add, not_or]

/-- The totalized rational phase identity holds even at denominator roots. -/
theorem phase_eq_simplePolePhase (p : ℕ) [NeZero p] (c a : ℤ)
    (hs : List (ℤ × ℤ)) (n : ℤ) :
    phase p c a hs n = InverseRational.simplePolePhase (coefficients p c a hs)
      (n : ZMod p) := by
  induction hs generalizing n with
  | nil =>
    simpa [coefficients, phase, InverseRational.iteratedDifferenceCoefficient] using
      (InverseRational.simplePolePhase_singlePoleCoefficient_neg
        (c : ZMod p) (a : ZMod p) (n : ZMod p)).symm
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    change phase p c a hs (n+u) - phase p c a hs (n+v) =
      InverseRational.simplePolePhase
        (InverseRational.differenceCoefficient (coefficients p c a hs)
          (u : ZMod p) (v : ZMod p)) (n : ZMod p)
    rw [InverseRational.simplePolePhase_differenceCoefficient, ih, ih]
    simp

/-- Surviving poles lie among the original denominator roots. -/
theorem poleSupport_subset_originalRoots (p : ℕ) [NeZero p]
    (c a : ℤ) (hs : List (ℤ × ℤ)) :
    InverseRational.poleSupport (coefficients p c a hs) ⊆ originalRoots p a hs := by
  classical
  induction hs with
  | nil =>
    intro x hx
    simp only [coefficients, List.map_nil, InverseRational.iteratedDifferenceCoefficient,
      InverseRational.mem_poleSupport, InverseRational.singlePoleCoefficient] at hx
    by_cases he : x = -(a : ZMod p)
    · simpa [originalRoots] using he
    · simp [he] at hx
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    intro x hx
    change x ∈ InverseRational.poleSupport
      (InverseRational.differenceCoefficient (coefficients p c a hs)
        (u : ZMod p) (v : ZMod p)) at hx
    have hu := InverseRational.poleSupport_differenceCoefficient_subset
      (coefficients p c a hs) (u : ZMod p) (v : ZMod p) hx
    simp only [Finset.mem_union, InverseRational.mem_poleSupport,
      InverseRational.translatedCoefficient] at hu
    simp only [originalRoots, Finset.mem_union, mem_image_sub_iff]
    rcases hu with hu | hv
    · exact Or.inl (ih (InverseRational.mem_poleSupport _ _ |>.mpr hu))
    · exact Or.inr (ih (InverseRational.mem_poleSupport _ _ |>.mpr hv))

theorem poleSupport_nonempty (p : ℕ) [NeZero p] [Fact p.Prime]
    (c a : ℤ) (hs : List (ℤ × ℤ)) (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^hs.length < p) :
    (InverseRational.poleSupport (coefficients p c a hs)).Nonempty := by
  apply InverseRational.singlePole_iteratedDifference_nonempty hc
  · intro uv huv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp huv
    exact hdistinct w hw
  · simpa using hsmall

/-- Comparing the original mask with the surviving-pole mask costs at most
one per original denominator root, including roots cancelled by differencing. -/
theorem norm_sum_mask_difference_le (p : ℕ) [NeZero p] [Fact p.Prime]
    (c a : ℤ) (hs : List (ℤ × ℤ)) :
    ‖(∑ x : ZMod p, seq p c a hs (x.val : ℤ)) -
      ∑ x : ZMod p, if x ∈ InverseRational.poleSupport (coefficients p c a hs)
        then 0 else ZMod.stdAddChar
          (InverseRational.simplePolePhase (coefficients p c a hs) x)‖ ≤
      (originalRoots p a hs).card := by
  classical
  let R := originalRoots p a hs
  let P := InverseRational.poleSupport (coefficients p c a hs)
  have hval (x : ZMod p) : (((x.val : ℤ) : ZMod p)) = x := by simp
  have hpoint (x : ZMod p) :
      ‖seq p c a hs (x.val : ℤ) -
        (if x ∈ P then 0 else ZMod.stdAddChar
          (InverseRational.simplePolePhase (coefficients p c a hs) x))‖ ≤
        if x ∈ R then (1 : ℝ) else 0 := by
    have hg := good_iff_not_mem_originalRoots p a hs (x.val : ℤ)
    rw [hval] at hg
    have hp := phase_eq_simplePolePhase p c a hs (x.val : ℤ)
    rw [hval] at hp
    by_cases hx : x ∈ R
    · have hng : ¬good p a hs (x.val : ℤ) := fun h => (hg.mp h) hx
      simp only [seq, if_neg hng, if_pos hx, zero_sub, norm_neg]
      split_ifs <;> simp [AddChar.norm_apply]
    · have hgood := hg.mpr hx
      have hnp : x ∉ P := fun hp => hx (poleSupport_subset_originalRoots p c a hs hp)
      simp only [seq, if_pos hgood, if_neg hx, if_neg hnp, hp, sub_self, norm_zero,
        le_refl]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ x : ZMod p, if x ∈ R then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (originalRoots p a hs).card := by simp [R]

/-- Sharp complete prime sum, with its actual pole conductor and original mask. -/
theorem norm_sum_seq_le_actual_conductor (p : ℕ) [NeZero p] [Fact p.Prime]
    (c a : ℤ) (hs : List (ℤ × ℤ)) (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^hs.length < p) :
    ‖∑ x : ZMod p, seq p c a hs (x.val : ℤ)‖ ≤
      ((2*(InverseRational.poleSupport (coefficients p c a hs)).card-1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) + (originalRoots p a hs).card := by
  classical
  have hne := poleSupport_nonempty p c a hs hc hdistinct hsmall
  have hcard : (InverseRational.poleSupport (coefficients p c a hs)).card < p :=
    (Finset.card_le_card (poleSupport_subset_originalRoots p c a hs)).trans_lt
      ((card_originalRoots_le p a hs).trans_lt hsmall)
  have hweil := RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
    (Fact.out : p.Prime).one_lt (coefficients p c a hs) hne hcard
  have herr := norm_sum_mask_difference_le p c a hs
  have htri := norm_add_le
    ((∑ x : ZMod p, seq p c a hs (x.val : ℤ)) -
      ∑ x : ZMod p, if x ∈ InverseRational.poleSupport (coefficients p c a hs)
        then 0 else ZMod.stdAddChar
          (InverseRational.simplePolePhase (coefficients p c a hs) x))
    (∑ x : ZMod p, if x ∈ InverseRational.poleSupport (coefficients p c a hs)
        then 0 else ZMod.stdAddChar
          (InverseRational.simplePolePhase (coefficients p c a hs) x))
  rw [sub_add_cancel] at htri
  linarith

/-- The explicit depth-only bound used at the final prime conductor. -/
theorem norm_sum_seq_le (p : ℕ) [NeZero p] [Fact p.Prime]
    (c a : ℤ) (hs : List (ℤ × ℤ)) (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^hs.length < p) :
    ‖∑ x : ZMod p, seq p c a hs (x.val : ℤ)‖ ≤
      ((2*2^hs.length-1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) + (2^hs.length : ℕ) := by
  have h := norm_sum_seq_le_actual_conductor p c a hs hc hdistinct hsmall
  have hr := card_originalRoots_le p a hs
  have hp := (Finset.card_le_card (poleSupport_subset_originalRoots p c a hs)).trans hr
  apply h.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hp) 1
  · exact_mod_cast hr

end Erdos387Proof.TerminalPrimeCancellation
