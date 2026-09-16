import Erdos387Proof.SeparatedKeyMass
import Erdos387Proof.SeparatedRoughBound
import Erdos387Proof.SeparatedFibreBound

/-! Complete nonnegative summation of the finite separated fibre envelope.
The dyadic key and reciprocal complement mass are both charged explicitly. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedOuterBound
open Erdos387 Erdos387.CoverBPZ SeparatedPrimeFibre SeparatedKeyMass
open SeparatedFibreBound SeparatedRoughBound SeparatedCertificateEnlargement
open scoped BigOperators

noncomputable def envelopeConstant (B : ℕ) : ℝ :=
  (4*(32*(B : ℝ)+2048*(B : ℝ)^2))*(1+Real.log 5)*boundConstant

theorem envelopeConstant_nonneg (B : ℕ) : 0≤envelopeConstant B := by
  have hc := boundConstant_pos
  unfold envelopeConstant
  positivity

theorem envelope_le {B k t H Q X : ℕ} (ht : 1≤t) (hH : 1≤H) (hX : 1≤X)
    (hyX : BPZScale.y t k≤X) (hQX : Q≤2*X) :
    envelope B k t H Q≤envelopeConstant B*H*((Q : ℝ)/Real.sqrt (t : ℝ))*
      (1+Real.log (X : ℝ))^4 := by
  have hHr : (1 : ℝ)≤H := by exact_mod_cast hH
  have hR := roughBound_le ht hX hyX hQX
  have hlog : Real.log (Q-Q/2+1 : ℕ)+1≤(1+Real.log 5)*(1+Real.log (X : ℝ)) := by
    rw [add_comm]
    apply log_linear_le (by exact_mod_cast hX) (by positivity)
    have hnat : Q-Q/2+1≤5*X := by omega
    exact_mod_cast hnat
  have hcoef : 4*(8*(4*(B : ℝ))+128*(H : ℝ)*(4*(B : ℝ))^2)≤
      (4*(32*(B : ℝ)+2048*(B : ℝ)^2))*H := by nlinarith
  have hL : 0≤1+Real.log (X : ℝ) := by positivity
  have hJ : 0≤1+Real.log (5 : ℝ) := by positivity
  have hbc := boundConstant_pos
  unfold envelope
  calc
    _ ≤ ((4*(32*(B : ℝ)+2048*(B : ℝ)^2))*H)*
        ((1+Real.log 5)*(1+Real.log (X : ℝ)))*
          (boundConstant*((Q : ℝ)/Real.sqrt (t : ℝ))*(1+Real.log (X : ℝ))^3) := by
      apply mul_le_mul
      · exact mul_le_mul hcoef hlog (by positivity) (by positivity)
      · exact hR
      · exact roughBound_nonneg k t Q (by omega)
      · positivity
    _ = _ := by unfold envelopeConstant; ring

theorem sum_keys_envelope_le {B K X z t medium second gap H : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) (ht : 1≤t) (hH : 1≤H) (hX : 1≤X)
    (hyX : BPZScale.y t S.k≤X) :
    (∑ c∈(keys S X z (BPZScale.y t S.k) medium second gap i).attach,
      envelope B S.k t H (blockUpper (representative c).2.2))≤
      envelopeConstant B*H*((2*(X : ℝ))/Real.sqrt (t : ℝ))*
        (1+Real.log (X : ℝ))^4*(Nat.log2 X+1 : ℕ)*roughReciprocalMass z X^S.k := by
  classical
  let A := keys S X z (BPZScale.y t S.k) medium second gap i
  let C : ℝ := envelopeConstant B*H*((2*(X : ℝ))/Real.sqrt (t : ℝ))*
    (1+Real.log (X : ℝ))^4
  have hC : 0≤C := by
    have hc := envelopeConstant_nonneg B
    dsimp [C]
    positivity
  have hper (c : {c // c∈A}) : envelope B S.k t H (blockUpper (representative c).2.2)≤
      C*keyWeight c.val := by
    have ha := representative_mem c
    have hb := split_bounds ha
    apply (envelope_le ht hH hX hyX (blockUpper_le_twice hb.2.2.1 hb.2.2.2)).trans
    have hQ := blockUpper_le_weight ha
    rw [key_representative] at hQ
    calc
      _ ≤ envelopeConstant B*H*((2*(X : ℝ)*keyWeight c.val)/Real.sqrt (t : ℝ))*
          (1+Real.log (X : ℝ))^4 := by
        gcongr
        exact mul_nonneg (envelopeConstant_nonneg B) (Nat.cast_nonneg H)
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ ∑ c∈A.attach,C*keyWeight c.val := Finset.sum_le_sum (fun c hc => hper c)
    _ = C*∑ c∈A,keyWeight c := by rw [← Finset.mul_sum,Finset.sum_attach]
    _ ≤ C*((Nat.log2 X+1 : ℕ)*roughReciprocalMass z X^S.k) :=
      mul_le_mul_of_nonneg_left (sum_keys_weight_le S i) hC
    _ = _ := by dsimp [C]; ring

end Erdos387Proof.SeparatedOuterBound
