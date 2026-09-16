import MerLeanExperiment.AngularBandCapacity
import MerLeanExperiment.UpperHalfPlaneDirection
import MerLeanExperiment.CapSemantics
import Mathlib.Order.PiLex
import Mathlib.Tactic

namespace PlanarMinimax

private noncomputable def lexKey {N : ℕ} (p : Fin N → Plane) (i : Fin N) :
    Lex (Fin 2 → ℝ) := toLex ![p i 1, p i 0]

private theorem lexKey_injective {N : ℕ} {p : Fin N → Plane}
    (hp : Function.Injective p) : Function.Injective (lexKey p) := by
  intro i j h
  apply hp
  ext q
  fin_cases q
  · exact congrFun (congrArg ofLex h) 1
  · exact congrFun (congrArg ofLex h) 0

private structure OrderedVertex {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) where val : Fin N

private noncomputable instance {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} : Fintype (OrderedVertex p hp) :=
  Fintype.ofEquiv (Fin N)
    { toFun := fun i ↦ ⟨i⟩
      invFun := fun i ↦ i.val
      left_inv := fun _ ↦ rfl
      right_inv := by intro i; cases i; rfl }

private theorem orderedVertex_val_injective {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} :
    Function.Injective (fun i : OrderedVertex p hp ↦ i.val) := by
  intro i j h
  cases i
  cases j
  congr

private noncomputable instance {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} : LinearOrder (OrderedVertex p hp) :=
  LinearOrder.lift' (fun i ↦ lexKey p i.val)
    ((lexKey_injective hp).comp orderedVertex_val_injective)

private theorem forward_shape {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) (i j : OrderedVertex p hp) (hij : i < j) :
    0 < (p j.val - p i.val) 1 ∨
      ((p j.val - p i.val) 1 = 0 ∧ 0 < (p j.val - p i.val) 0) := by
  change lexKey p i.val < lexKey p j.val at hij
  change Pi.Lex (· < ·) (· < ·) (![p i.val 1, p i.val 0])
    (![p j.val 1, p j.val 0]) at hij
  rcases hij with ⟨a, hprev, hlt⟩
  fin_cases a
  · exact Or.inl (by simpa using sub_pos.mpr hlt)
  · have heq := hprev (0 : Fin 2) (by simp)
    exact Or.inr ⟨by simpa using sub_eq_zero.mpr heq.symm,
      by simpa using sub_pos.mpr hlt⟩

theorem classical_capacity {N k : ℕ} (hk : 1 ≤ k) (p : Fin N → Plane)
    (hp : Function.Injective p)
    (hcap : ∀ i j l : Fin N, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (p i) (p j) (p l) ≤ Real.pi - Real.pi / k) :
    N ≤ 2 ^ k := by
  let q : OrderedVertex p hp → Plane := fun i ↦ p i.val
  let theta : OrderedVertex p hp → OrderedVertex p hp → ℝ := fun i j ↦
    if 0 < (q j - q i) 1 then upperDirectionAngle (q j - q i) else 0
  let scale : OrderedVertex p hp → OrderedVertex p hp → ℝ := fun i j ↦ ‖q j - q i‖
  have hq : Function.Injective q := hp.comp orderedVertex_val_injective
  have hrange : ∀ ⦃i j : OrderedVertex p hp⦄, i < j →
      0 ≤ theta i j ∧ theta i j < (k : ℝ) * (Real.pi / k) := by
    intro i j hij
    have heq : (k : ℝ) * (Real.pi / k) = Real.pi := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      field_simp
    rw [heq]
    rcases forward_shape p hp i j hij with hy | ⟨hy, _⟩
    · have hyq : 0 < (q j - q i) 1 := by simpa [q] using hy
      have hcond : q i 1 < q j 1 := by simpa using hyq
      simp [theta, hcond]
      exact ⟨(upperDirectionAngle_pos hyq).le, upperDirectionAngle_lt_pi hyq⟩
    · have hyq : (q j - q i) 1 = 0 := by simpa [q] using hy
      have hyq' : q j 1 - q i 1 = 0 := by simpa using hyq
      have hcond : ¬ q i 1 < q j 1 := by linarith
      simp [theta, hcond, Real.pi_pos]
  have hs : ∀ ⦃i j : OrderedVertex p hp⦄, i < j → 0 < scale i j := by
    intro i j hij
    change 0 < ‖q j - q i‖
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (hq.ne (ne_of_lt hij)).symm
  have he : ∀ ⦃i j : OrderedVertex p hp⦄, i < j →
      q j - q i = scale i j • unitDirection (theta i j) := by
    intro i j hij
    rcases forward_shape p hp i j hij with hy | ⟨hy, hx⟩
    · have hyq : 0 < (q j - q i) 1 := by simpa [q] using hy
      have hcond : q i 1 < q j 1 := by simpa using hyq
      simpa [theta, scale, hcond] using upperDirectionAngle_reconstruct hyq
    · have hn : ‖q j - q i‖ = (q j - q i) 0 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
        have hyq : (q j - q i) 1 = 0 := by simpa [q] using hy
        have hxq : 0 < (q j - q i) 0 := by simpa [q] using hx
        have hxq' : 0 < q j 0 - q i 0 := by simpa using hxq
        rw [hyq]
        simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hxq'.le]
      have hyq : (q j - q i) 1 = 0 := by simpa [q] using hy
      have hyq' : q j 1 - q i 1 = 0 := by simpa using hyq
      have hcond : ¬ q i 1 < q j 1 := by linarith
      ext a
      fin_cases a <;> simp [theta, scale, hcond, hyq, unitDirection, hn]
  have hc : ∀ i j l : OrderedVertex p hp, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (q i) (q j) (q l) ≤ Real.pi - Real.pi / k := by
    intro i j l hij hjl hil
    exact hcap i.val j.val l.val
      (fun h ↦ hij (orderedVertex_val_injective h))
      (fun h ↦ hjl (orderedVertex_val_injective h))
      (fun h ↦ hil (orderedVertex_val_injective h))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have card := geometricAngularBand_capacity q theta scale 0 (Real.pi / k) k hq
    (div_pos Real.pi_pos hkpos) (by simpa using hrange)
    (le_of_eq (by field_simp)) hs he hc
  let e : OrderedVertex p hp ≃ Fin N :=
    { toFun := fun i ↦ i.val
      invFun := fun i ↦ ⟨i⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; rfl }
  have hecard : Fintype.card (OrderedVertex p hp) = N := by
    simpa using Fintype.card_congr e
  rwa [hecard] at card

theorem classical_minimax_lower {N k : ℕ} (hk : 1 ≤ k) (hN : 2 ^ k < N) :
    Real.pi * (1 - 1 / (k : ℝ)) ≤ minimaxAngle N := by
  have hpow : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hN3 : 3 ≤ N := by omega
  rw [le_minimaxAngle_iff_guaranteed hN3]
  intro p hp
  by_contra hn
  push Not at hn
  have hc : ∀ i j l : Fin N, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (p i) (p j) (p l) ≤ Real.pi - Real.pi / k := by
    intro i j l hij hjl hil
    have h := hn i j l hij hjl hil
    have heq : Real.pi * (1 - 1 / (k : ℝ)) = Real.pi - Real.pi / k := by ring
    rw [heq] at h
    exact h.le
  exact (not_le_of_gt hN) (classical_capacity hk p hp hc)

#print axioms classical_capacity
#print axioms classical_minimax_lower

end PlanarMinimax
