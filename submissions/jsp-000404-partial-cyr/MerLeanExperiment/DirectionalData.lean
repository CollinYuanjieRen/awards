import Mathlib.Data.Real.Basic

/-!
Primitive necessary constraints for ordered planar directions, measured in
units of the angle deficit. A sharp cardinality bound is not a field here.
-/

namespace OrderedDirections

/-- Direction data on any linearly ordered index type. -/
structure Data (V : Type*) [LinearOrder V] (width : ℝ) where
  value : V → V → ℝ
  nonnegative : ∀ {i j}, i < j → 0 ≤ value i j
  below_width : ∀ {i j}, i < j → value i j < width
  between : ∀ {i j k}, i < j → j < k →
    (value i j ≤ value i k ∧ value i k ≤ value j k) ∨
    (value j k ≤ value i k ∧ value i k ≤ value i j)
  separated : ∀ {i j k}, i < j → j < k →
    1 ≤ |value i j - value j k|
  first_gap : ∀ {i j k}, i < j → j < k →
    |value i j - value i k| ≤ width - 1
  last_gap : ∀ {i j k}, i < j → j < k →
    |value i k - value j k| ≤ width - 1

end OrderedDirections
