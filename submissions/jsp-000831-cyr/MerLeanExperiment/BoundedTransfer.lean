import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! A bounded measurable transfer from uniformly bounded Birkhoff sums. -/

namespace Kesten

/-- Uniformly bounded measurable Birkhoff sums admit a bounded measurable transfer. -/
theorem exists_bounded_transfer {X : Type*} [MeasurableSpace X] (T : X → X) (f : X → ℝ)
    (C : ℝ) (hT : Measurable T) (hf : Measurable f)
    (hbound : ∀ (x : X) (n : ℕ), |birkhoffSum T f n x| ≤ C) :
    ∃ h : X → ℝ, Measurable h ∧ (∀ x : X, |h x| ≤ C) ∧
      ∀ x : X, h (T x) = h x - f x := by
  let h : X → ℝ := fun x ↦ Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop
  have hsum_measurable : ∀ n : ℕ, Measurable (birkhoffSum T f n) := by
    intro n
    change Measurable fun x ↦ ∑ k ∈ Finset.range n, f ((T^[k]) x)
    exact Finset.measurable_sum (Finset.range n) fun k _ ↦ hf.comp (hT.iterate k)
  refine ⟨h, Measurable.liminf hsum_measurable, ?_, ?_⟩
  · intro x
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f n x) :=
      Filter.isBoundedUnder_of ⟨C, fun n ↦ (abs_le.mp (hbound x n)).2⟩
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f n x) :=
      Filter.isBoundedUnder_of ⟨-C, fun n ↦ (abs_le.mp (hbound x n)).1⟩
    apply abs_le.mpr
    constructor
    · exact Filter.le_liminf_of_le hbddAbove.isCoboundedUnder_ge
        (Filter.Eventually.of_forall fun n ↦ (abs_le.mp (hbound x n)).1)
    · exact Filter.liminf_le_of_frequently_le
        (Filter.Frequently.of_forall fun n ↦ (abs_le.mp (hbound x n)).2) hbddBelow
  · intro x
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f (n + 1) x) :=
      Filter.isBoundedUnder_of ⟨C, fun n ↦ (abs_le.mp (hbound x (n + 1))).2⟩
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f (n + 1) x) :=
      Filter.isBoundedUnder_of ⟨-C, fun n ↦ (abs_le.mp (hbound x (n + 1))).1⟩
    change Filter.liminf (fun n ↦ birkhoffSum T f n (T x)) Filter.atTop =
      Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop - f x
    calc
      Filter.liminf (fun n ↦ birkhoffSum T f n (T x)) Filter.atTop =
          Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x + -f x) Filter.atTop := by
        apply Filter.liminf_congr
        filter_upwards [] with n
        rw [birkhoffSum_succ_apply']
        ring
      _ = Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x) Filter.atTop + -f x :=
        liminf_add_const Filter.atTop _ _ hbddAbove.isCoboundedUnder_ge hbddBelow
      _ = Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop - f x := by
        have hshift := Filter.liminf_nat_add (fun n ↦ birkhoffSum T f n x) 1
        rw [show Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x) Filter.atTop =
          Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop by exact hshift]
        ring

/-- Almost-everywhere bounded Birkhoff sums admit an almost-everywhere bounded transfer. -/
theorem exists_ae_bounded_transfer {X : Type*} [MeasurableSpace X] (T : X → X) (f : X → ℝ)
    (C : ℝ) (μ : MeasureTheory.Measure X) (hT : Measurable T) (hf : Measurable f)
    (hbound : ∀ᵐ x ∂μ, ∀ n : ℕ, |birkhoffSum T f n x| ≤ C) :
    ∃ h : X → ℝ, Measurable h ∧ (∀ᵐ x ∂μ, |h x| ≤ C) ∧
      ∀ᵐ x ∂μ, h (T x) = h x - f x := by
  let h : X → ℝ := fun x ↦ Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop
  have hsum_measurable : ∀ n : ℕ, Measurable (birkhoffSum T f n) := by
    intro n
    change Measurable fun x ↦ ∑ k ∈ Finset.range n, f ((T^[k]) x)
    exact Finset.measurable_sum (Finset.range n) fun k _ ↦ hf.comp (hT.iterate k)
  refine ⟨h, Measurable.liminf hsum_measurable, ?_, ?_⟩
  · filter_upwards [hbound] with x hx
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f n x) :=
      Filter.isBoundedUnder_of ⟨C, fun n ↦ (abs_le.mp (hx n)).2⟩
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f n x) :=
      Filter.isBoundedUnder_of ⟨-C, fun n ↦ (abs_le.mp (hx n)).1⟩
    apply abs_le.mpr
    constructor
    · exact Filter.le_liminf_of_le hbddAbove.isCoboundedUnder_ge
        (Filter.Eventually.of_forall fun n ↦ (abs_le.mp (hx n)).1)
    · exact Filter.liminf_le_of_frequently_le
        (Filter.Frequently.of_forall fun n ↦ (abs_le.mp (hx n)).2) hbddBelow
  · filter_upwards [hbound] with x hx
    have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f (n + 1) x) :=
      Filter.isBoundedUnder_of ⟨C, fun n ↦ (abs_le.mp (hx (n + 1))).2⟩
    have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n ↦ birkhoffSum T f (n + 1) x) :=
      Filter.isBoundedUnder_of ⟨-C, fun n ↦ (abs_le.mp (hx (n + 1))).1⟩
    change Filter.liminf (fun n ↦ birkhoffSum T f n (T x)) Filter.atTop =
      Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop - f x
    calc
      Filter.liminf (fun n ↦ birkhoffSum T f n (T x)) Filter.atTop =
          Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x + -f x) Filter.atTop := by
        apply Filter.liminf_congr
        filter_upwards [] with n
        rw [birkhoffSum_succ_apply']
        ring
      _ = Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x) Filter.atTop + -f x :=
        liminf_add_const Filter.atTop _ _ hbddAbove.isCoboundedUnder_ge hbddBelow
      _ = Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop - f x := by
        have hshift := Filter.liminf_nat_add (fun n ↦ birkhoffSum T f n x) 1
        rw [show Filter.liminf (fun n ↦ birkhoffSum T f (n + 1) x) Filter.atTop =
          Filter.liminf (fun n ↦ birkhoffSum T f n x) Filter.atTop by exact hshift]
        ring

end Kesten
