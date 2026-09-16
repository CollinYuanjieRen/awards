import Mathlib

namespace ReciprocalSquares

/-- The total rational weight of a list. -/
def listMass {ι : Type*} (w : ι → ℚ) (xs : List ι) : ℚ :=
  (xs.map w).sum

/-- Greedy deletion with a reserved tail keeps the residual target positive
and its ratio to the remaining mass in a fixed compact interval. -/
theorem exists_greedy_sublist
    {ι : Type*} (w : ι → ℚ) (xs : List ι)
    (a b c ε A : ℚ)
    (hc : 1 < c) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcap : c ≤ ε * A)
    (hweight : ∀ x ∈ xs, 0 ≤ w x)
    (hslack : ∀ (pre : List ι) (x : ι) (post : List ι),
      xs = pre ++ x :: post →
      c * w x < (1 - ε) * (a + listMass w post))
    (hb : 0 < b)
    (hlow : c * b < a + listMass w xs)
    (hupp : a + listMass w xs ≤ A * b) :
    ∃ selected : List ι,
      selected.Sublist xs ∧
      0 < b - listMass w selected ∧
      c * (b - listMass w selected) < a ∧
      a ≤ A * (b - listMass w selected) := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hA0 : 0 < A := by
    by_contra hAnot
    have hAle : A ≤ 0 := le_of_not_gt hAnot
    have hεA : ε * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε0.le hAle
    linarith
  induction xs generalizing b with
  | nil =>
    refine ⟨[], by simp, ?_⟩
    simpa [listMass] using And.intro hb (And.intro hlow hupp)
  | cons x tail ih =>
    have hv : 0 ≤ w x := hweight x (by simp)
    have hweight_tail : ∀ y ∈ tail, 0 ≤ w y := by
      intro y hy
      exact hweight y (by simp [hy])
    have hslack_tail : ∀ (pre : List ι) (y : ι) (post : List ι),
        tail = pre ++ y :: post →
        c * w y < (1 - ε) * (a + listMass w post) := by
      intro pre y post hdecomp
      apply hslack (x :: pre) y post
      simp [hdecomp]
    have hxslack : c * w x < (1 - ε) * (a + listMass w tail) := by
      exact hslack [] x tail (by simp)
    have hmass : listMass w (x :: tail) = w x + listMass w tail := by
      simp [listMass]
    rw [hmass] at hlow hupp
    by_cases htake : a + listMass w tail ≤ c * b
    · have hεcomp : 0 ≤ 1 - ε := by linarith
      have hscaled :
          (1 - ε) * (a + listMass w tail) ≤ (1 - ε) * (c * b) :=
        mul_le_mul_of_nonneg_left htake hεcomp
      have hvscaled : c * w x < c * ((1 - ε) * b) := by
        calc
          c * w x < (1 - ε) * (a + listMass w tail) := hxslack
          _ ≤ (1 - ε) * (c * b) := hscaled
          _ = c * ((1 - ε) * b) := by ring
      have hvbound : w x < (1 - ε) * b :=
        lt_of_mul_lt_mul_left hvscaled hc0.le
      have hεb0 : 0 < ε * b := mul_pos hε0 hb
      have hεb : ε * b < b - w x := by nlinarith
      have hb' : 0 < b - w x := hεb0.trans hεb
      have hcv : 0 ≤ (c - 1) * w x := mul_nonneg (by linarith) hv
      have hlow' : c * (b - w x) < a + listMass w tail := by
        nlinarith
      have hcapb : c * b ≤ (ε * A) * b :=
        mul_le_mul_of_nonneg_right hcap hb.le
      have hAstep : A * (ε * b) < A * (b - w x) :=
        mul_lt_mul_of_pos_left hεb hA0
      have hupp' : a + listMass w tail ≤ A * (b - w x) := by
        calc
          a + listMass w tail ≤ c * b := htake
          _ ≤ (ε * A) * b := hcapb
          _ = A * (ε * b) := by ring
          _ ≤ A * (b - w x) := hAstep.le
      obtain ⟨selected, hsub, hpos, hlow_selected, hupp_selected⟩ :=
        ih (b - w x) hweight_tail hslack_tail hb' hlow' hupp'
      have hresidual :
          b - listMass w (x :: selected) =
            (b - w x) - listMass w selected := by
        simp [listMass]
        ring
      refine ⟨x :: selected, hsub.cons_cons x, ?_⟩
      rw [hresidual]
      exact ⟨hpos, hlow_selected, hupp_selected⟩
    · have hlow' : c * b < a + listMass w tail := lt_of_not_ge htake
      have hupp' : a + listMass w tail ≤ A * b := by
        nlinarith
      obtain ⟨selected, hsub, hpos, hlow_selected, hupp_selected⟩ :=
        ih b hweight_tail hslack_tail hb hlow' hupp'
      exact ⟨selected, hsub.cons x, hpos, hlow_selected, hupp_selected⟩

end ReciprocalSquares
