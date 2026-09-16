import Erdos387Proof.MediumOscillatoryMass
import Erdos387Proof.MediumFourierTailDecay

/-! Actual complementary completion shapes retain a fixed-power saving.
Explicit fixed powers of the Fourier cutoff, sieve support, prime-factor
budget, local multiplicity, and logarithms can therefore be absorbed. -/

namespace Erdos387Proof.MediumOscillatoryDecay

open Erdos387 Erdos387.CoverBPZ MediumOscillatoryMass MediumMainTermDecay
open Filter
open scoped BigOperators Topology

def scaleUnit (k : ℕ) : ℕ := 3 ^ k * k ^ 100

theorem scaleUnit_pos {k : ℕ} (hk : 0 < k) : 0 < scaleUnit k := by
  unfold scaleUnit
  positivity

theorem X_eq_upper_mul_medium (N k : ℕ) :
    SubpowerScale.X N k = SubpowerScale.base N k ^ (398 * scaleUnit k) * SubpowerScale.medium N k := by
  unfold SubpowerScale.X BPZScale.X SubpowerScale.medium BPZScale.medium
  rw [← pow_add]
  congr 1
  unfold BPZScale.xExp BPZScale.mediumExp scaleUnit
  ring

theorem maxComplement_le_pow (N k : ℕ) :
    maxComplement (SubpowerScale.X N k) (SubpowerScale.medium N k) ≤
      SubpowerScale.base N k ^ (398 * scaleUnit k) := by
  have hm : 0 < SubpowerScale.medium N k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  apply Nat.le_of_mul_le_mul_right ?_ hm
  calc
    _ ≤ maxComplement (SubpowerScale.X N k) (SubpowerScale.medium N k) *
        (SubpowerScale.medium N k + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ SubpowerScale.X N k := Nat.div_mul_le_self _ _
    _ = _ := X_eq_upper_mul_medium N k

/-- Any budget a strictly below the exact last-period margin xExp/200
leaves one complete base power after summing the completion shape. -/
theorem eventually_pow_le_minComplement {B k a : ℕ} (hB : 0 < B) (hk : 0 < k)
    (ha : a < 3 * scaleUnit k) :
    ∀ᶠ N : ℕ in atTop, SubpowerScale.base N k ^ (2 * (a + 1)) ≤
      minComplement B (SubpowerScale.X N k) (SubpowerScale.large N k) := by
  filter_upwards [MediumFourierTailDecay.eventually_const_le_base k (2 * B)] with N hBbase
  have ht : 1 ≤ SubpowerScale.base N k := by
    unfold SubpowerScale.base
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hl : 0 < SubpowerScale.large N k := by
    unfold SubpowerScale.large BPZScale.large SubpowerScale.base
    positivity
  have hu := scaleUnit_pos hk
  have he : 2 * (a + 1) + 1 + BPZScale.largeExp k ≤ BPZScale.xExp k := by
    have hlarge : BPZScale.largeExp k = 303 * scaleUnit k := by
      unfold BPZScale.largeExp scaleUnit
      ring
    have hx : BPZScale.xExp k = 600 * scaleUnit k := by
      unfold BPZScale.xExp scaleUnit
      ring
    rw [hlarge, hx]
    omega
  have hprod : SubpowerScale.base N k ^ (2 * (a + 1)) * (B * SubpowerScale.large N k) * 2 ≤
      SubpowerScale.X N k := by
    calc
      _ = SubpowerScale.base N k ^ (2 * (a + 1)) * (2 * B) * SubpowerScale.large N k := by ring
      _ ≤ SubpowerScale.base N k ^ (2 * (a + 1)) * SubpowerScale.base N k *
          SubpowerScale.large N k := by gcongr
      _ = SubpowerScale.base N k ^ (2 * (a + 1) + 1 + BPZScale.largeExp k) := by
        unfold SubpowerScale.large BPZScale.large
        rw [pow_add, pow_add, pow_one]
      _ ≤ SubpowerScale.base N k ^ BPZScale.xExp k := Nat.pow_le_pow_right ht he
      _ = SubpowerScale.X N k := rfl
  have hfloor : SubpowerScale.base N k ^ (2 * (a + 1)) ≤
      (SubpowerScale.X N k / 2) / (B * SubpowerScale.large N k) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hB hl)).mpr
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr hprod
  exact hfloor.trans (Nat.le_succ _)

theorem log_maxComplement_le_log_X (N k : ℕ) :
    Real.log (maxComplement (SubpowerScale.X N k) (SubpowerScale.medium N k) : ℝ) ≤
      Real.log (SubpowerScale.X N k : ℝ) := by
  by_cases hzero : maxComplement (SubpowerScale.X N k) (SubpowerScale.medium N k) = 0
  · simp only [hzero, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact_mod_cast Nat.div_le_self (SubpowerScale.X N k) (SubpowerScale.medium N k + 1)

theorem envelope_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 ≤ envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) := by
  unfold envelope roughReciprocalMass
  positivity

theorem eventually_budgeted_envelope_le {B K : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) {a : ℕ} (ha : a < 3 * scaleUnit S.k) :
    ∀ᶠ N : ℕ in atTop,
      (SubpowerScale.base N S.k : ℝ)^a *
        envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) /
            (SubpowerScale.X N S.k : ℝ) ≤
      (roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1) +
        (1 + Real.log (SubpowerScale.X N S.k : ℝ)) ^ (S.k - 1)) /
          (SubpowerScale.base N S.k : ℝ) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [eventually_pow_le_minComplement hB hk ha] with N hmin
  let t : ℝ := SubpowerScale.base N S.k
  have ht : 0 < t := by dsimp [t]; unfold SubpowerScale.base; positivity
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact_mod_cast (show 1 ≤ SubpowerScale.base N S.k by
      unfold SubpowerScale.base
      exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
  have hX : (0 : ℝ) < SubpowerScale.X N S.k := by exact_mod_cast SubpowerScale.X_pos N S.k
  have hmin0 : (0 : ℝ) < minComplement B (SubpowerScale.X N S.k) (SubpowerScale.large N S.k) := by
    exact_mod_cast (Nat.succ_pos ((SubpowerScale.X N S.k / 2) /
      (B * SubpowerScale.large N S.k)))
  have hsqrtmin : t ^ (a + 1) ≤ Real.sqrt
      (minComplement B (SubpowerScale.X N S.k) (SubpowerScale.large N S.k)) := by
    apply Real.le_sqrt_of_sq_le
    dsimp [t]
    rw [← pow_mul, mul_comm (a + 1) 2]
    exact_mod_cast hmin
  have hsqrtmax : Real.sqrt (maxComplement (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)) ≤
      t ^ (199 * scaleUnit S.k) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [← pow_mul, show 199 * scaleUnit S.k * 2 = 398 * scaleUnit S.k by omega]
    dsimp [t]
    exact_mod_cast maxComplement_le_pow N S.k
  have hmax : (maxComplement (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) : ℝ) ≤
      t ^ (398 * scaleUnit S.k) := by
    dsimp [t]
    exact_mod_cast maxComplement_le_pow N S.k
  have hfirst : t ^ (a + 1) * ((SubpowerScale.X N S.k : ℝ) /
      Real.sqrt (minComplement B (SubpowerScale.X N S.k) (SubpowerScale.large N S.k))) ≤
      SubpowerScale.X N S.k := by
    rw [← mul_div_assoc, div_le_iff₀ (Real.sqrt_pos.mpr hmin0)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hsqrtmin hX.le
  have hsecond : t ^ (a + 1) *
      (Real.sqrt (maxComplement (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)) *
        maxComplement (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)) ≤
      SubpowerScale.X N S.k := by
    calc
      _ ≤ t ^ (a + 1) * (t ^ (199 * scaleUnit S.k) * t ^ (398 * scaleUnit S.k)) := by gcongr
      _ = t ^ (a + 1 + 597 * scaleUnit S.k) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ t ^ BPZScale.xExp S.k := by
        apply pow_le_pow_right₀ ht1
        have hx : BPZScale.xExp S.k = 600 * scaleUnit S.k := by unfold BPZScale.xExp scaleUnit; ring
        rw [hx]
        omega
      _ = (SubpowerScale.X N S.k : ℝ) := by simp [t, SubpowerScale.X, BPZScale.X]
  have hlogpow :
      (1 + Real.log (maxComplement (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) : ℝ)) ^ (S.k - 1) ≤
      (1 + Real.log (SubpowerScale.X N S.k : ℝ)) ^ (S.k - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith [log_maxComplement_le_log_X N S.k]) _
  have hR : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) := by
    unfold roughReciprocalMass; positivity
  have he := add_le_add
    (mul_le_mul_of_nonneg_right hfirst (pow_nonneg hR (S.k - 1)))
    (mul_le_mul hsecond hlogpow (by positivity) hX.le)
  apply (div_le_div_iff₀ hX ht).mpr
  simpa only [envelope, pow_succ, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using he

/-- Explicit exponential losses: fixed cutoff and sieve-support powers,
a fixed multiple of the prime-factor budget, and depth-linear local roots. -/
def loss (a b c d N k : ℕ) : ℕ :=
  MediumFourierTailDecay.height N k ^ a * SubpowerScale.z N k ^ (2 * b * N) *
    2 ^ (c * N ^ 2) * k ^ (d * N)

theorem eventually_loss_mul_densityPower_le_base (k a b c d : ℕ) :
    ∀ᶠ N : ℕ in atTop, loss a b c d N k * 2 ^ (N ^ 2) ≤ SubpowerScale.base N k := by
  let q := Nat.log 2 k + 1
  have hkbase : k ≤ 2 ^ q := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k).le
  let C := (8 * a + 2 * b) * BPZScale.xExp k + c + q * d + 1
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop C] with N hN1 hN
  let E := SubpowerScale.roughPower N k * (8 * N * a) +
    SubpowerScale.roughPower N k * (2 * b * N) + c * N ^ 2 + q * (d * N) + N ^ 2
  have hcost : loss a b c d N k * 2 ^ (N ^ 2) ≤ 2 ^ E := by
    calc
      _ ≤ (MediumFourierTailDecay.height N k ^ a * SubpowerScale.z N k ^ (2 * b * N) *
          2 ^ (c * N ^ 2) * (2 ^ q) ^ (d * N)) * 2 ^ (N ^ 2) := by
        unfold loss
        gcongr
      _ = _ := by
        unfold MediumFourierTailDecay.height SubpowerScale.z
        simp only [← pow_mul, ← pow_add]
        congr 1
        dsimp [E]
        ring
  have hpow1 : N ≤ N ^ (2 * k + 4) := by
    simpa using Nat.pow_le_pow_right hN1 (by omega : 1 ≤ 2 * k + 4)
  have hpow2 : N ^ 2 ≤ N ^ (2 * k + 4) := Nat.pow_le_pow_right hN1 (by omega)
  have hr : SubpowerScale.roughPower N k * (8 * N * a) +
      SubpowerScale.roughPower N k * (2 * b * N) =
      ((8 * a + 2 * b) * BPZScale.xExp k) * N ^ (2 * k + 4) := by
    unfold SubpowerScale.roughPower
    rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega, pow_succ]
    ring
  have he : E ≤ SubpowerScale.scalePower N k := by
    dsimp [E]
    rw [hr]
    calc
      _ ≤ ((8 * a + 2 * b) * BPZScale.xExp k) * N ^ (2 * k + 4) +
          c * N ^ (2 * k + 4) + q * (d * N ^ (2 * k + 4)) + N ^ (2 * k + 4) := by gcongr
      _ = C * N ^ (2 * k + 4) := by dsimp [C]; ring
      _ ≤ N * N ^ (2 * k + 4) := Nat.mul_le_mul_right _ hN
      _ = SubpowerScale.scalePower N k := by
        unfold SubpowerScale.scalePower
        rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]
        ring
  exact hcost.trans (Nat.pow_le_pow_right (by norm_num) he)

/-- The density reciprocal is included in the proven loss budget. -/
theorem eventually_loss_div_density_le_base {B K : ℕ}
    (S : BPZSection6Input B K) (a b c d : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (loss a b c d N S.k : ℝ) / refinedDensity S (SubpowerScale.z N S.k) ≤
        (SubpowerScale.base N S.k : ℝ) := by
  filter_upwards [eventually_loss_mul_densityPower_le_base S.k a b c d,
    MediumEndpointDecay.eventually_one_le_pow_mul_refinedDensity S] with N hloss hV
  have hVR := refinedDensity_pos S (SubpowerScale.z N S.k)
  apply (div_le_iff₀ hVR).mpr
  calc
    _ ≤ (loss a b c d N S.k : ℝ) *
        ((2 : ℝ)^(N^2) * refinedDensity S (SubpowerScale.z N S.k)) :=
      le_mul_of_one_le_right (by positivity) hV
    _ = ((loss a b c d N S.k : ℝ) * (2 : ℝ)^(N^2)) *
        refinedDensity S (SubpowerScale.z N S.k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hloss) hVR.le

/-- A single fixed polynomial bounds both the actual reciprocal mass and
all logarithmic factors needed in this envelope. -/
theorem exists_mass_log_polynomial_bound {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      roughReciprocalMass (SubpowerScale.z N k) (SubpowerScale.X N k) ≤ C * (N : ℝ)^(2*k+5) ∧
      1 + Real.log (SubpowerScale.X N k : ℝ) ≤ C * (N : ℝ)^(2*k+5) := by
  obtain ⟨A, hA, hmass⟩ := exists_full_roughMass_quadratic_bound hk
  let C : ℝ := A + 1 + (BPZScale.xExp k : ℝ) * Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0 < BPZScale.xExp k := by unfold BPZScale.xExp; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ)^2 ≤ (N : ℝ)^(2*k+5) := pow_le_pow_right₀ hNR (by omega)
  have hp1 : (1 : ℝ) ≤ (N : ℝ)^(2*k+5) := one_le_pow₀ hNR
  constructor
  · have hAC : A ≤ C := by
      dsimp [C]
      have h : 0 ≤ (BPZScale.xExp k : ℝ) * Real.log 2 := by positivity
      linarith
    exact (hmass N hN).trans (mul_le_mul hAC hp (by positivity) hC.le)
  · rw [SubpowerScale.log_X_eq]
    push_cast
    dsimp [C]
    nlinarith

noncomputable def normalizedEnvelope {B K : ℕ} (S : BPZSection6Input B K)
    (a b c d e f N : ℕ) : ℝ :=
  (loss a b c d N S.k : ℝ) * ((N : ℝ) + 1)^f * (1 + Real.log (SubpowerScale.X N S.k : ℝ))^e *
    envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) /
    ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) / refinementModulus S)

/-- Every displayed frequency, support, divisor, root and logarithm loss is
explicit and derived. The original completion shape has enough margin. -/
theorem tendsto_normalizedEnvelope_zero {B K : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (a b c d e f : ℕ) :
    Tendsto (normalizedEnvelope S a b c d e f) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  obtain ⟨C, hC, hpoly⟩ := exists_mass_log_polynomial_bound hk
  let r := S.k - 1
  let s := 2 * S.k + 5
  let D : ℝ := 2 * refinementModulus S * (2 : ℝ)^f * C ^ (r + e)
  have hlim : Tendsto (fun N : ℕ => D * ((N : ℝ)^(s*(r+e)+f) / (2 : ℝ)^N)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt
      (s * (r + e) + f) (by norm_num : (1 : ℝ) < 2)).const_mul D
  have ha : 1 < 3 * scaleUnit S.k := by have := scaleUnit_pos hk; omega
  apply squeeze_zero' (g := fun N : ℕ => D * ((N : ℝ)^(s*(r+e)+f) / (2 : ℝ)^N)) _ _ hlim
  · apply Filter.Eventually.of_forall
    intro N
    unfold normalizedEnvelope
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    have hE := envelope_nonneg S N
    positivity
  · filter_upwards [eventually_budgeted_envelope_le S hB ha,
      eventually_loss_div_density_le_base S a b c d, eventually_ge_atTop (1 : ℕ)]
      with N henv hloss hN
    have hM : (0 : ℝ) < refinementModulus S := by exact_mod_cast refinementModulus_pos S
    have hX : (0 : ℝ) < SubpowerScale.X N S.k := by exact_mod_cast SubpowerScale.X_pos N S.k
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    have ht : (0 : ℝ) < SubpowerScale.base N S.k := by unfold SubpowerScale.base; positivity
    have hE := envelope_nonneg S N
    have hR : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) := by
      unfold roughReciprocalMass; positivity
    have hL : 0 ≤ 1 + Real.log (SubpowerScale.X N S.k : ℝ) := by positivity
    have hp := hpoly N (by omega)
    have hRpow := pow_le_pow_left₀ hR hp.1 r
    have hLpow := pow_le_pow_left₀ hL hp.2 r
    have hLextra := pow_le_pow_left₀ hL hp.2 e
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNextra : ((N : ℝ) + 1)^f ≤ (2 : ℝ)^f * (N : ℝ)^f := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) f
    have hbase : (2 : ℝ)^N ≤ SubpowerScale.base N S.k := by
      have hn : N ≤ SubpowerScale.scalePower N S.k := by
        unfold SubpowerScale.scalePower
        simpa using Nat.pow_le_pow_right hN (by omega : 1 ≤ 2*S.k+5)
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    have hbudget : (SubpowerScale.base N S.k : ℝ) *
        (envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) / (SubpowerScale.X N S.k : ℝ)) ≤
        (roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^r +
          (1 + Real.log (SubpowerScale.X N S.k : ℝ))^r) / (SubpowerScale.base N S.k : ℝ) := by
      simpa only [pow_one, r, mul_div_assoc] using henv
    unfold normalizedEnvelope
    calc
      _ = (refinementModulus S : ℝ) * ((N : ℝ) + 1)^f * (1 + Real.log (SubpowerScale.X N S.k : ℝ))^e *
          ((loss a b c d N S.k : ℝ) / refinedDensity S (SubpowerScale.z N S.k) *
            (envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
              (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) / (SubpowerScale.X N S.k : ℝ))) := by
        field_simp
      _ ≤ (refinementModulus S : ℝ) * ((N : ℝ) + 1)^f * (1 + Real.log (SubpowerScale.X N S.k : ℝ))^e *
          ((SubpowerScale.base N S.k : ℝ) *
            (envelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
              (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) / (SubpowerScale.X N S.k : ℝ))) := by
        gcongr
      _ ≤ (refinementModulus S : ℝ) * ((N : ℝ) + 1)^f * (1 + Real.log (SubpowerScale.X N S.k : ℝ))^e *
          ((roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^r +
            (1 + Real.log (SubpowerScale.X N S.k : ℝ))^r) / (SubpowerScale.base N S.k : ℝ)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ ≤ (refinementModulus S : ℝ) * ((2 : ℝ)^f * (N : ℝ)^f) * (C * (N : ℝ)^s)^e *
          (((C * (N : ℝ)^s)^r + (C * (N : ℝ)^s)^r) / (SubpowerScale.base N S.k : ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hNextra hM.le) hLextra
            (by positivity) (by positivity)
        · exact div_le_div_of_nonneg_right (add_le_add hRpow hLpow) ht.le
        · positivity
        · positivity
      _ = D * (N : ℝ)^(s*(r+e)+f) / (SubpowerScale.base N S.k : ℝ) := by
        dsimp [D]
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        simp only [pow_add, mul_add]
        ring
      _ ≤ _ := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_left (by dsimp [D]; positivity) (by positivity) hbase

end Erdos387Proof.MediumOscillatoryDecay
