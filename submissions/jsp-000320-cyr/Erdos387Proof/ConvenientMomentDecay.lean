import Erdos387Proof.ConvenientMomentEstimate
import Erdos387Proof.MediumOscillatoryDecay

/-! Fixed-power losses in the actual convenient moment remain subpower.
The common final moment order is fixed before the dyadic boxes are chosen. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMomentDecay
open Erdos387 Erdos387.CoverBPZ MediumOscillatoryDecay MediumMainTermDecay Filter
open scoped Topology

/-- Includes the full complementary-vector multiplicity and a power of the
reciprocal-density envelope, in addition to all fixed Fourier/sieve losses. -/
theorem eventually_core_loss_le_base (k a b c d q : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      loss a b c d N k^q*(k^(N^2))^q*2^(q*N^2)*SubpowerScale.z N k^(2*N) ≤
        SubpowerScale.base N k := by
  let u := Nat.log 2 k+1
  have hkbase : k ≤ 2^u := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k).le
  let C := (8*a*q+2*b*q+2)*BPZScale.xExp k+c*q+u*d*q+u*q+q
  filter_upwards [eventually_ge_atTop (1 : ℕ),eventually_ge_atTop C] with N hN1 hN
  let E := SubpowerScale.roughPower N k*(8*N*a*q)+
    SubpowerScale.roughPower N k*(2*b*N*q)+c*N^2*q+u*(d*N*q)+
    u*(N^2*q)+q*N^2+SubpowerScale.roughPower N k*(2*N)
  have hcost : loss a b c d N k^q*(k^(N^2))^q*2^(q*N^2)*SubpowerScale.z N k^(2*N) ≤ 2^E := by
    calc
      _ ≤ (MediumFourierTailDecay.height N k^a*SubpowerScale.z N k^(2*b*N)*
          2^(c*N^2)*(2^u)^(d*N))^q*((2^u)^(N^2))^q*
          2^(q*N^2)*SubpowerScale.z N k^(2*N) := by
        unfold loss
        gcongr
      _ = _ := by
        unfold MediumFourierTailDecay.height SubpowerScale.z
        simp only [← pow_mul,← pow_add]
        congr 1
        dsimp [E]
        ring
  have hpow1 : N ≤ N^(2*k+4) := by
    simpa using Nat.pow_le_pow_right hN1 (by omega : 1 ≤ 2*k+4)
  have hpow2 : N^2 ≤ N^(2*k+4) := Nat.pow_le_pow_right hN1 (by omega)
  have hr : SubpowerScale.roughPower N k*(8*N*a*q)+
      SubpowerScale.roughPower N k*(2*b*N*q)+SubpowerScale.roughPower N k*(2*N) =
      ((8*a*q+2*b*q+2)*BPZScale.xExp k)*N^(2*k+4) := by
    unfold SubpowerScale.roughPower
    rw [show 2*k+4=(2*k+3)+1 by omega,pow_succ]
    ring
  have he : E ≤ SubpowerScale.scalePower N k := by
    have hE : E=((8*a*q+2*b*q+2)*BPZScale.xExp k)*N^(2*k+4)+
        c*N^2*q+u*(d*N*q)+u*(N^2*q)+q*N^2 := by
      dsimp [E]
      nlinarith only [hr]
    rw [hE]
    calc
      _ ≤ ((8*a*q+2*b*q+2)*BPZScale.xExp k)*N^(2*k+4)+
          c*N^(2*k+4)*q+u*(d*N^(2*k+4)*q)+u*(N^(2*k+4)*q)+q*N^(2*k+4) := by gcongr
      _ = C*N^(2*k+4) := by dsimp [C]; ring
      _ ≤ N*N^(2*k+4) := Nat.mul_le_mul_right _ hN
      _ = SubpowerScale.scalePower N k := by
        unfold SubpowerScale.scalePower
        rw [show 2*k+5=(2*k+4)+1 by omega,pow_succ]
        ring
  exact hcost.trans (Nat.pow_le_pow_right (by norm_num) he)

theorem eventually_polynomial_le_base (k p : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C*(N : ℝ)^p ≤ SubpowerScale.base N k := by
  have hlim : Tendsto (fun N : ℕ => C*((N : ℝ)^p/(2 : ℝ)^N)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt p
      (by norm_num : (1 : ℝ) < 2)).const_mul C
  have hsmall := (tendsto_order.mp hlim).2 1 (by norm_num)
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hpoly : C*(N : ℝ)^p ≤ (2 : ℝ)^N := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2^N)).mp
    simpa only [mul_div_assoc] using hN.le
  have hpower : N ≤ SubpowerScale.scalePower N k := by
    unfold SubpowerScale.scalePower
    simpa using Nat.pow_le_pow_right hN1 (by omega : 1 ≤ 2*k+5)
  apply hpoly.trans
  unfold SubpowerScale.base
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hpower

theorem eventually_log_polynomial_le_base {k : ℕ} (hk : 0 < k)
    (C : ℝ) (hC : 0 ≤ C) (e f : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      C*((N : ℝ)+1)^e*(1+Real.log (SubpowerScale.X N k))^f ≤ SubpowerScale.base N k := by
  obtain ⟨C0,hC0,hpoly⟩ := exists_mass_log_polynomial_bound hk
  let D := C*(2 : ℝ)^e*C0^f
  filter_upwards [eventually_polynomial_le_base k (e+(2*k+5)*f) D,
    eventually_ge_atTop (1 : ℕ)] with N hbound hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := (hpoly N (by omega)).2
  calc
    _ ≤ C*(2*(N : ℝ))^e*(C0*(N : ℝ)^(2*k+5))^f := by gcongr; linarith
    _ = D*(N : ℝ)^(e+(2*k+5)*f) := by
      dsimp [D]
      simp only [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ _ := hbound

/-- The inverse refined density is raised to the same fixed power as the
full multiplicity and all Fourier/sieve losses. -/
theorem eventually_core_loss_div_density_le_base {B K : ℕ}
    (S : BPZSection6Input B K) (a b c d q : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ g ≤ SubpowerScale.z N S.k^(2*N),
      (loss a b c d N S.k : ℝ)^q*((S.k^(N^2) : ℕ) : ℝ)^q*g /
        (refinedDensity S (SubpowerScale.z N S.k))^q ≤ SubpowerScale.base N S.k := by
  filter_upwards [eventually_core_loss_le_base S.k a b c d q,
    MediumEndpointDecay.eventually_one_le_pow_mul_refinedDensity S] with N hcore hden
  intro g hg
  have hV := MediumMainTermDecay.refinedDensity_pos S (SubpowerScale.z N S.k)
  have hinv : (refinedDensity S (SubpowerScale.z N S.k))⁻¹ ≤ (2 : ℝ)^(N^2) := by
    rw [← one_div]
    exact (div_le_iff₀ hV).mpr hden
  have hpow : ((refinedDensity S (SubpowerScale.z N S.k))⁻¹)^q ≤ (2 : ℝ)^(q*N^2) := by
    calc
      _ ≤ ((2 : ℝ)^(N^2))^q := pow_le_pow_left₀ (inv_nonneg.mpr hV.le) hinv q
      _ = _ := by rw [← pow_mul,mul_comm (N^2) q]
  have hnat : loss a b c d N S.k^q*(S.k^(N^2))^q*g*2^(q*N^2) ≤ SubpowerScale.base N S.k := by
    calc
      _ = loss a b c d N S.k^q*(S.k^(N^2))^q*2^(q*N^2)*g := by ring
      _ ≤ loss a b c d N S.k^q*(S.k^(N^2))^q*2^(q*N^2)*SubpowerScale.z N S.k^(2*N) := by gcongr
      _ ≤ _ := hcore
  calc
    _ = (loss a b c d N S.k : ℝ)^q*((S.k^(N^2) : ℕ) : ℝ)^q*g *
        ((refinedDensity S (SubpowerScale.z N S.k))⁻¹)^q := by rw [div_eq_mul_inv,inv_pow]
    _ ≤ (loss a b c d N S.k : ℝ)^q*((S.k^(N^2) : ℕ) : ℝ)^q*g*(2 : ℝ)^(q*N^2) := by gcongr
    _ ≤ _ := by exact_mod_cast hnat

/-- Reusable fixed-power loss bound, without the complementary multiplicity.
In particular the fourth power is available for the E5 square-root saving. -/
theorem eventually_pow_loss_div_density_le_base {B K : ℕ}
    (S : BPZSection6Input B K) (a b c d q : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((loss a b c d N S.k : ℝ) /
        refinedDensity S (SubpowerScale.z N S.k))^q ≤ SubpowerScale.base N S.k := by
  filter_upwards [eventually_core_loss_div_density_le_base S a b c d q] with N hcore
  have hV := MediumMainTermDecay.refinedDensity_pos S (SubpowerScale.z N S.k)
  have hm : (1 : ℝ) ≤ ((S.k^(N^2) : ℕ) : ℝ)^q := by
    have hk : 1 ≤ S.k := by have := S.hk3; omega
    exact_mod_cast (Nat.one_le_pow q _ (Nat.one_le_pow (N^2) S.k hk))
  have hg : 1 ≤ SubpowerScale.z N S.k^(2*N) :=
    Nat.one_le_pow _ _ (SubpowerScale.z_pos N S.k)
  calc
    _ = (loss a b c d N S.k : ℝ)^q /
        (refinedDensity S (SubpowerScale.z N S.k))^q := div_pow _ _ _
    _ ≤ (loss a b c d N S.k : ℝ)^q*((S.k^(N^2) : ℕ) : ℝ)^q*1 /
        (refinedDensity S (SubpowerScale.z N S.k))^q := by
      apply div_le_div_of_nonneg_right ?_ (pow_nonneg hV.le q)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (loss a b c d N S.k : ℝ)^q by positivity)
    _ ≤ _ := by simpa only [Nat.cast_one] using hcore 1 hg

end Erdos387Proof.ConvenientMomentDecay
