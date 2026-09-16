import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Replacing one old item by two fresh distinct items increases cardinality by one. -/
theorem card_replace_one_by_two (s : Finset α) {q a b : α}
    (hq : q ∈ s) (ha : a ∉ s.erase q) (hb : b ∉ s.erase q) (hab : a ≠ b) :
    (insert a (insert b (s.erase q))).card = s.card + 1 := by
  rw [card_insert_of_notMem (by simp [ha, hab]), card_insert_of_notMem hb,
    card_erase_add_one hq]

/-- The weight of a one-to-two replacement differs by the removed and added weights. -/
theorem sum_replace_one_by_two (s : Finset α) (w : α → ℕ) {q a b : α}
    (hq : q ∈ s) (ha : a ∉ s.erase q) (hb : b ∉ s.erase q) (hab : a ≠ b) :
    (∑ x ∈ insert a (insert b (s.erase q)), w x) + w q =
      (∑ x ∈ s, w x) + w a + w b := by
  rw [sum_insert (by simp [ha, hab]), sum_insert hb]
  have hsum := sum_erase_add s w hq
  omega

end Finset
