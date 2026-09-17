import Erdos732Designs.Design

/-!
# Non-vertical lines of the affine plane over `ZMod p`

For a prime `p` we work in the affine plane `ZMod p × ZMod p` and consider the non-vertical
lines `L(a, b) = {(x, y) | y = a * x + b}`.  Two facts are needed for the lower bound of
Erdős Problem 732: every such line has exactly `p` points (`card_line`), and two distinct
lines meet in at most one point (`line_inter_card_le_one`).  Together these say that the family
of lines is a partial design on the point set of the plane.
-/

namespace Erdos732Lower

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- The non-vertical line `y = a x + b` of the affine plane over `ZMod p`. -/
def line (a b : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun q => q.2 = a * q.1 + b

@[simp]
theorem mem_line (a b : ZMod p) (q : ZMod p × ZMod p) :
    q ∈ line p a b ↔ q.2 = a * q.1 + b := by
  simp [line]

/-- A non-vertical line is the graph of `x ↦ a * x + b`. -/
theorem line_eq_image (a b : ZMod p) :
    line p a b = Finset.univ.image fun x : ZMod p => (x, a * x + b) := by
  ext ⟨x, y⟩
  simp only [mem_line, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨x, rfl, h.symm⟩
  · rintro ⟨x', rfl, rfl⟩
    rfl

theorem card_line (a b : ZMod p) : (line p a b).card = p := by
  have hinj : Function.Injective fun x : ZMod p => (x, a * x + b) := fun x y h =>
    congrArg Prod.fst h
  rw [line_eq_image, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

theorem line_inter_card_le_one {a b a' b' : ZMod p} (h : (a, b) ≠ (a', b')) :
    (line p a b ∩ line p a' b').card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  rintro ⟨x, y⟩ hq ⟨x', y'⟩ hq'
  simp only [Finset.mem_inter, mem_line] at hq hq'
  obtain ⟨h1, h2⟩ := hq
  obtain ⟨h1', h2'⟩ := hq'
  by_cases hx : x = x'
  · subst hx
    rw [h1, h1']
  · exfalso
    have haa : a = a' := by
      have hz : (a - a') * (x - x') = 0 := by linear_combination h2 - h1 + h1' - h2'
      rcases mul_eq_zero.1 hz with h0 | h0
      · exact sub_eq_zero.1 h0
      · exact absurd (sub_eq_zero.1 h0) hx
    rw [haa] at h1
    have hbb : b = b' := by linear_combination h2 - h1
    exact h (by rw [haa, hbb])

end Erdos732Lower
