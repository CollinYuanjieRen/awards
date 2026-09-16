import MerLeanExperiment.ShiftDefinitions
import MerLeanExperiment.UniformAvoidance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos441

/-- Uniform selection of shifted points whose pair factors have no small prime
divisors.  The threshold is fixed before the finite family and its translations. -/
theorem exists_rough_shifted_points (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x → ∀ K : ℕ, 2 * K ≤ M →
      ∀ r : Fin K → ℤ, Function.Injective r →
      (∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) →
      ∀ c : Fin K → ℝ, (∀ i, c0 ≤ c i) → ∃ ell : Fin K → ℤ,
        (∀ i, c i * Real.sqrt x < (shiftedPoint M r ell i : ℝ) ∧
          (shiftedPoint M r ell i : ℝ) <
            c i * (Real.sqrt x + x ^ (1 / 4 : ℝ))) ∧
        ∀ i j, i < j → ∀ p : ℕ, p.Prime →
          (p : ℤ) ∣ shiftFactor M r ell i j →
            Real.log x / (8 * Real.log M) < (p : ℝ) := by
  classical
  let FR : ℝ := M.factorial
  have hFR : 0 < FR := by
    dsimp [FR]
    exact_mod_cast Nat.factorial_pos M
  have hcScaled : 0 < c0 / FR := div_pos hc0 hFR
  obtain ⟨X0, hX0, havoid⟩ :=
    chen_uniform_linear_avoidance M hM (c0 / FR) hcScaled
  refine ⟨X0, hX0, ?_⟩
  intro x hx K
  induction K with
  | zero =>
      intro hKM r hrInj hrDist c hc
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ K ih =>
      intro hKM r hrInj hrDist c hc
      let rOld : Fin K → ℤ := fun i ↦ r i.castSucc
      let cOld : Fin K → ℝ := fun i ↦ c i.castSucc
      have hKold : 2 * K ≤ M := by omega
      have hrOldInj : Function.Injective rOld := by
        intro i j hij
        apply Fin.castSucc_injective
        apply hrInj
        simpa [rOld] using hij
      have hrOldDist : ∀ i j, i ≠ j → 2 * (rOld j - rOld i).natAbs ≤ M := by
        intro i j hij
        apply hrDist i.castSucc j.castSucc
        exact fun h ↦ hij (Fin.castSucc_injective K h)
      have hcOld : ∀ i, c0 ≤ cOld i := fun i ↦ hc i.castSucc
      obtain ⟨ellOld, hpointOld, hroughOld⟩ :=
        ih hKold rOld hrOldInj hrOldDist cOld hcOld
      let last : Fin (K + 1) := Fin.last K
      let d : Fin K → ℤ := fun i ↦ r last - r i.castSucc
      let A : Fin K → ℤ := fun i ↦ (M.factorial : ℤ) / d i
      let B : Fin K → ℤ := fun i ↦ 1 - A i * ellOld i
      have hd (i : Fin K) : d i ≠ 0 := by
        dsimp [d, last]
        exact sub_ne_zero.mpr (Ne.symm (hrInj.ne (Fin.castSucc_ne_last i)))
      have hdSize (i : Fin K) : 2 * (d i).natAbs ≤ M := by
        exact hrDist i.castSucc last (Fin.castSucc_ne_last i)
      have hspec (i : Fin K) :
          d i * A i = (M.factorial : ℤ) ∧ IsCoprime (A i) (B i) ∧
            ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ, ¬ (p : ℤ) ∣ A i * n + B i := by
        simpa [A, B] using factorial_linear_spec M (d i) (hd i) (hdSize i) (ellOld i)
      have hprim : ∀ i, IsCoprime (A i) (B i) := fun i ↦ (hspec i).2.1
      have hsmall : ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
          ¬ (p : ℤ) ∣ ∏ i, (A i * n + B i) := by
        intro p hp hpM n
        exact (Nat.prime_iff_prime_int.mp hp).not_dvd_finsetProd
          (fun i _ ↦ (hspec i).2.2 p hp hpM n)
      have hcLast : c0 / FR ≤ c last / FR := by
        exact (div_le_div_iff_of_pos_right hFR).2 (hc last)
      obtain ⟨k, hkLower, hkUpper, hkRough⟩ :=
        havoid x hx (c last / FR) (-((r last : ℤ) : ℝ) / FR) hcLast K hKold
          A B hprim hsmall
      let ell : Fin (K + 1) → ℤ := Fin.lastCases k ellOld
      refine ⟨ell, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun q ↦ ?_) i
        · have hkL := hkLower
          have hkU := hkUpper
          rw [← Real.sqrt_eq_rpow] at hkL hkU
          have hlowRewrite :
              c last / FR * Real.sqrt x + -((r last : ℤ) : ℝ) / FR =
                (c last * Real.sqrt x - (r last : ℝ)) / FR := by
            field_simp [hFR.ne']; ring
          have huppRewrite :
              c last / FR * (Real.sqrt x + x ^ (1 / 4 : ℝ)) +
                  -((r last : ℤ) : ℝ) / FR =
                (c last * (Real.sqrt x + x ^ (1 / 4 : ℝ)) - (r last : ℝ)) / FR := by
            field_simp [hFR.ne']; ring
          rw [hlowRewrite] at hkL
          rw [huppRewrite] at hkU
          have hkL' := (div_lt_iff₀ hFR).mp hkL
          have hkU' := (lt_div_iff₀ hFR).mp hkU
          constructor
          · change c last * Real.sqrt x <
              (((M.factorial : ℤ) * ell last + r last : ℤ) : ℝ)
            simp [ell, last]
            nlinarith
          · change (((M.factorial : ℤ) * ell last + r last : ℤ) : ℝ) <
              c last * (Real.sqrt x + x ^ (1 / 4 : ℝ))
            simp [ell, last]
            nlinarith
        · simpa [ell, shiftedPoint, rOld, cOld] using hpointOld q
      · intro i j hij p hp hpDiv
        cases j using Fin.lastCases with
        | last =>
            cases i using Fin.lastCases with
            | last => exact (lt_irrefl _ hij).elim
            | cast iOld =>
                have hfactor :
                    shiftFactor M r ell iOld.castSucc (Fin.last K) =
                      A iOld * k + B iOld := by
                  simp [shiftFactor, ell, A, B, d, last]
                  ring
                have hpForm : (p : ℤ) ∣ A iOld * k + B iOld := by
                  rwa [hfactor] at hpDiv
                have hformProd : A iOld * k + B iOld ∣ ∏ u, (A u * k + B u) :=
                  Finset.dvd_prod_of_mem (fun u ↦ A u * k + B u)
                    (Finset.mem_univ iOld)
                exact hkRough p hp (hpForm.trans hformProd)
        | cast jOld =>
            cases i using Fin.lastCases with
            | last => exact (not_lt_of_ge (Fin.le_last jOld.castSucc) hij).elim
            | cast iOld =>
                have hqq : iOld < jOld := by simpa using hij
                apply hroughOld iOld jOld hqq p hp
                simpa [shiftFactor, ell, rOld] using hpDiv

end Erdos441
