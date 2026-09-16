/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Erdos387Proof.IndexedConvenientMoment
import Mathlib.Algebra.Order.Floor.Div

/-!
# Hölder extraction and an integral convenient-moment choice

The first part turns the indexed `ell`-moment estimate into a first-moment
bound with every finite cardinal and scale factor still visible.  The second
part replaces the invalid floor choice in the source argument by natural
ceiling division on dyadic exponents.  It also records an integral power
form of the resulting positive `R`-saving.
-/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators

namespace ConvenientMomentSaving

/-- The sigma-indexed set of all actual outer-certificate/short-variable
pairs. -/
noncomputable def indexedPairs
    {J : Type*} [DecidableEq J]
    (I : Finset J) (Rbox : J → Finset ℕ) : Finset (Σ _j : J, ℕ) := by
  classical
  exact I.sigma Rbox

/-- Hölder followed by a supplied squared `ell`-moment estimate, for
modulus-dependent finite short boxes. -/
theorem indexed_holder_cauchy_of_moment_sq_le
    {J : Type*} [DecidableEq J]
    (I : Finset J) (Rbox : J → Finset ℕ)
    (f : J → ℕ → ℝ) (ell : ℕ) (hell : 1 ≤ ell)
    (hf : ∀ j ∈ I, ∀ r ∈ Rbox j, 0 ≤ f j r) {B : ℝ}
    (hmoment : (∑ j ∈ I, ∑ r ∈ Rbox j, (f j r) ^ ell) ^ 2 ≤ B) :
    (∑ j ∈ I, ∑ r ∈ Rbox j, f j r) ^ (2 * ell) ≤
      ((∑ j ∈ I, (Rbox j).card : ℕ) : ℝ) ^ (2 * (ell - 1)) * B := by
  let F : (Σ _j : J, ℕ) → ℝ := fun jr => f jr.1 jr.2
  have hF : ∀ jr ∈ indexedPairs I Rbox, 0 ≤ F jr := by
    intro jr hjr
    rw [indexedPairs, Finset.mem_sigma] at hjr
    exact hf jr.1 hjr.1 jr.2 hjr.2
  have h := Erdos387.ConvenientMoment.holder_cauchy_of_moment_sq_le
    (indexedPairs I Rbox) F ell hell hF (B := B) (by
      simpa [indexedPairs, F, Finset.sum_sigma] using hmoment)
  simpa [indexedPairs, F, Finset.sum_sigma, Finset.card_sigma] using h

/-- First-absolute-moment consequence of the fully indexed convenient-moment
estimate.  No outer certificate or residue is identified with another; the
only multiplicity loss is the explicit fixed-divisor fibre bound `m`. -/
theorem firstMoment_pow_le
    {J : Type*} [DecidableEq J]
    {ell N k T m : ℕ} (hk : 0 < k) (hell : 1 ≤ ell)
    (I : Finset J) (D : J → ℕ)
    (modulus : ℕ → ℕ) [∀ d, NeZero (modulus d)]
    (frequency scale : J → ℕ)
    (Sbox Rbox : J → Finset ℕ) (U : Finset ℕ)
    (Rbound : J → ℕ) (beta : J → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hTle : T ≤ SubpowerScale.medium N k)
    (hDpos : ∀ j ∈ I, 0 < D j)
    (hDmod : ∀ j ∈ I, D j ∣ modulus (D j))
    (hDrough : ∀ j ∈ I, IsZRough (SubpowerScale.z N k) (D j))
    (hbox : ∀ j ∈ I, Sbox j ⊆ U)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough (SubpowerScale.z N k) u)
    (hScop : ∀ j ∈ I, ∀ s ∈ Sbox j, s.Coprime (modulus (D j)))
    (hfibre : ∀ d ∈ I.image D,
      (I.filter fun j => D j = d).card ≤ m)
    (hbeta : ∀ j ∈ I, ∀ s ∈ Sbox j, ‖beta j s‖ ≤ 1)
    (hscale : ∀ j ∈ I, (scale j).Coprime (D j))
    (hRcop : ∀ j ∈ I, ∀ r ∈ Rbox j, r.Coprime (modulus (D j)))
    (hRle : ∀ j ∈ I, ∀ r ∈ Rbox j, r ≤ Rbound j)
    (hshort : ∀ j ∈ I,
      Rbound j < D j / Nat.gcd (D j) (frequency j)) :
    (∑ j ∈ I, ∑ r ∈ Rbox j,
        ‖∑ s ∈ Sbox j,
          beta j s * ZMod.stdAddChar
            ((frequency j : ZMod (modulus (D j))) *
              (scale j : ZMod (modulus (D j))) *
              (r : ZMod (modulus (D j)))⁻¹ *
              (s : ZMod (modulus (D j)))⁻¹)‖) ^ (2 * ell) ≤
      ((∑ j ∈ I, (Rbox j).card : ℕ) : ℝ) ^ (2 * (ell - 1)) *
        (((m * ((I.image D).card * T ^ ell + U.card ^ (2 * ell)) *
            SubpowerScale.base N k) *
          (∑ j ∈ I, modulus (D j) * (Rbox j).card) : ℕ) : ℝ) := by
  let f : J → ℕ → ℝ := fun j r =>
    ‖∑ s ∈ Sbox j,
      beta j s * ZMod.stdAddChar
        ((frequency j : ZMod (modulus (D j))) *
          (scale j : ZMod (modulus (D j))) *
          (r : ZMod (modulus (D j)))⁻¹ *
          (s : ZMod (modulus (D j)))⁻¹)‖
  have hmoment :=
    IndexedConvenientMoment.subpower_sum_norm_reciprocalCharacter_pow_sq_le
      hk I D modulus frequency scale Sbox Rbox U Rbound beta hN hTle
        hDpos hDmod hDrough hbox hUpos hUle hUrough hScop hfibre hbeta
        hscale hRcop hRle hshort
  exact indexed_holder_cauchy_of_moment_sq_le I Rbox f ell hell
    (fun _j _hj _r _hr => norm_nonneg _) (by simpa [f] using hmoment)

/-- Integral replacement for `ceil(log E / log S)` when `E=2^e` and
`S=2^s`. -/
def dyadicMoment (e s : ℕ) : ℕ := e ⌈/⌉ s

theorem le_mul_dyadicMoment {e s : ℕ} (hs : 0 < s) :
    e ≤ s * dyadicMoment e s := by
  simpa [dyadicMoment, nsmul_eq_mul] using
    (le_smul_ceilDiv (α := ℕ) (β := ℕ) hs (b := e))

theorem dyadicMoment_le_iff {e s L : ℕ} (hs : 0 < s) :
    dyadicMoment e s ≤ L ↔ e ≤ s * L := by
  exact ceilDiv_le_iff_le_mul hs

theorem dyadicMoment_pos {e s : ℕ} (he : 0 < e) (hs : 0 < s) :
    0 < dyadicMoment e s := by
  by_contra hzero
  have hz : dyadicMoment e s = 0 := Nat.eq_zero_of_not_pos hzero
  have := le_mul_dyadicMoment (e := e) hs
  rw [hz, mul_zero] at this
  omega

theorem dyadicMoment_two_le {e s : ℕ} (hs : 0 < s) (hse : s < e) :
    2 ≤ dyadicMoment e s := by
  by_contra hnot
  have hone : dyadicMoment e s ≤ 1 := by omega
  have heS : e ≤ s := by simpa using (dyadicMoment_le_iff hs).1 hone
  omega

/-- The corrected ceiling choice gives the intended diagonal ratio. -/
theorem pow_le_pow_dyadicMoment {e s : ℕ} (hs : 0 < s) :
    2 ^ e ≤ (2 ^ s) ^ dyadicMoment e s := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (le_mul_dyadicMoment hs)

theorem dyadic_ratio_le_one {e s : ℕ} (hs : 0 < s) :
    (2 ^ e : ℝ) / ((2 ^ s : ℝ) ^ dyadicMoment e s) ≤ 1 := by
  apply (div_le_one (by positivity)).2
  exact_mod_cast pow_le_pow_dyadicMoment hs

/-- Ceiling adds at most one `S`-power, so the off-diagonal numerator range
remains within the same polynomial envelope. -/
theorem two_mul_dyadicMoment_exponent_le {e s : ℕ} (hs : 0 < s) :
    s * (2 * dyadicMoment e s) ≤ 2 * s + 2 * e := by
  rw [dyadicMoment, Nat.ceilDiv_eq_add_pred_div]
  have hdiv : ((e + s - 1) / s) * s ≤ e + s - 1 :=
    Nat.div_mul_le_self _ _
  calc
    s * (2 * ((e + s - 1) / s)) =
        2 * (((e + s - 1) / s) * s) := by ring
    _ ≤ 2 * (e + s - 1) := Nat.mul_le_mul_left 2 hdiv
    _ ≤ 2 * s + 2 * e := by omega

theorem square_pow_dyadicMoment_le {e s : ℕ} (hs : 0 < s) :
    (2 ^ s) ^ (2 * dyadicMoment e s) ≤
      (2 ^ s) ^ 2 * (2 ^ e) ^ 2 := by
  rw [← pow_mul]
  calc
    2 ^ (s * (2 * dyadicMoment e s)) ≤ 2 ^ (2 * s + 2 * e) :=
      Nat.pow_le_pow_right (by norm_num)
        (two_mul_dyadicMoment_exponent_le hs)
    _ = (2 ^ s) ^ 2 * (2 ^ e) ^ 2 := by
      rw [pow_add, ← pow_mul, ← pow_mul]
      simp only [mul_comm]

/-- Base-two logarithm exponents of the exact integral `X` and `y` scales. -/
def xLog (N k : ℕ) : ℕ :=
  SubpowerScale.scalePower N k * BPZScale.xExp k

def yLog (N k : ℕ) : ℕ :=
  SubpowerScale.scalePower N k * BPZScale.yExp k

theorem xLog_eq_yLog_mul_pow (N k : ℕ) :
    xLog N k = yLog N k * k ^ 100 := by
  unfold xLog yLog BPZScale.xExp BPZScale.yExp
  ring

theorem y_eq_pow_two (N k : ℕ) :
    SubpowerScale.y N k = 2 ^ yLog N k := by
  simp [SubpowerScale.y, BPZScale.y, SubpowerScale.base,
    SubpowerScale.scalePower, yLog, pow_mul]

/-- Actual convenient-scale bounds force the corrected moment order to be at
most `k^100`. -/
theorem dyadicMoment_le_k_pow
    {N k e s : ℕ} (hN : 0 < N) (_hk : 0 < k)
    (heX : e ≤ xLog N k) (hys : yLog N k ≤ s) :
    dyadicMoment e s ≤ k ^ 100 := by
  have hyPos : 0 < yLog N k := by
    unfold yLog SubpowerScale.scalePower BPZScale.yExp
    positivity
  apply (dyadicMoment_le_iff (hyPos.trans_le hys)).2
  calc
    e ≤ xLog N k := heX
    _ = yLog N k * k ^ 100 := xLog_eq_yLog_mul_pow N k
    _ ≤ s * k ^ 100 := Nat.mul_le_mul_right _ hys

/-- Integral power form of the positive saving usually written
`R^(-1/(2ell)) ≤ X^(-1/k^201)`. -/
theorem X_pow_two_mul_dyadicMoment_le_R_pow
    {N k e s R : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (heX : e ≤ xLog N k) (hys : yLog N k ≤ s)
    (hR : SubpowerScale.y N k ≤ R) :
    SubpowerScale.X N k ^ (2 * dyadicMoment e s) ≤ R ^ (k ^ 201) := by
  have hell : dyadicMoment e s ≤ k ^ 100 :=
    dyadicMoment_le_k_pow hN (by omega) heX hys
  have hyPos : 0 < yLog N k := by
    unfold yLog SubpowerScale.scalePower BPZScale.yExp
    positivity
  have hExp : xLog N k * (2 * dyadicMoment e s) ≤
      yLog N k * k ^ 201 := by
    rw [xLog_eq_yLog_mul_pow]
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    calc
      k ^ 100 * (2 * dyadicMoment e s) ≤
          k ^ 100 * (2 * k ^ 100) := by gcongr
      _ ≤ k ^ 100 * (k * k ^ 100) := by
        gcongr
      _ = k ^ 201 := by
        rw [show k ^ 201 = k ^ 100 * (k * k ^ 100) by
          rw [← pow_succ', ← pow_add]]
  calc
    SubpowerScale.X N k ^ (2 * dyadicMoment e s) =
        2 ^ (xLog N k * (2 * dyadicMoment e s)) := by
      rw [SubpowerScale.X_eq_pow_two, ← pow_mul]
      congr 1
      simp [xLog, SubpowerScale.scalePower, mul_comm]
    _ ≤ 2 ^ (yLog N k * k ^ 201) :=
      Nat.pow_le_pow_right (by norm_num) hExp
    _ = SubpowerScale.y N k ^ (k ^ 201) := by
      rw [y_eq_pow_two, ← pow_mul]
    _ ≤ R ^ (k ^ 201) := Nat.pow_le_pow_left hR _

theorem inverse_R_pow_saving
    {N k e s R : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (heX : e ≤ xLog N k) (hys : yLog N k ≤ s)
    (hR : SubpowerScale.y N k ≤ R) :
    ((R : ℝ)⁻¹) ^ (k ^ 201) ≤
      (((SubpowerScale.X N k : ℕ) : ℝ)⁻¹) ^
        (2 * dyadicMoment e s) := by
  have hpow := X_pow_two_mul_dyadicMoment_le_R_pow
    hN hk heX hys hR
  have hXpos : (0 : ℝ) < SubpowerScale.X N k := by
    rw [SubpowerScale.X_eq_pow_two]
    positivity
  have hRpos : (0 : ℝ) < R := by
    have hy : 0 < SubpowerScale.y N k := by
      rw [y_eq_pow_two]
      positivity
    exact_mod_cast hy.trans_le hR
  simp only [inv_pow]
  exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by exact_mod_cast hpow)

end ConvenientMomentSaving

end Erdos387Proof
