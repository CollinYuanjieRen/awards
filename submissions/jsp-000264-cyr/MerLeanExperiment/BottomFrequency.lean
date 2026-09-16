import MerLeanExperiment.ResidueLowerBounds
import MerLeanExperiment.SquareSubproducts
import MerLeanExperiment.FrequencySummation

namespace ReciprocalSquares

/-- Frequencies in the bottom range have uniformly large residue energy on
the square denominators coming from the bottom prime interval. -/
theorem bottom_frequency_energy_lower
    (M : ℕ) (hM : 262144 ≤ M) (h : ℤ)
    (hlo : (M : ℝ)^16 ≤ |(h : ℝ)|)
    (hhi : 2 * |(h : ℝ)| ≤ (M : ℝ)^20) :
    (M : ℝ) / 64 ≤
      residueEnergy (squareD (M^10)) (fun d => (h : ℝ) / (d : ℝ)) := by
  let N := M ^ 10
  let P := widePrimes N
  let E := P.image (fun p => p ^ 2)
  let U : ℝ := 16 * (M : ℝ) ^ 20
  have hMpos : 0 < M := by omega
  have hmpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hN3 : 3 ≤ N := by
    have hself : M ≤ M ^ 10 :=
      le_self_pow₀ (by omega) (by decide : (10 : ℕ) ≠ 0)
    dsimp [N]
    omega
  have hlarge : P ⊆ largePrimes N := by
    exact widePrimes_subset_largePrimes N hN3
  have hEsub : E ⊆ squareD N := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    have hsingleton : ({p} : Finset ℕ) ⊆ largePrimes N := by
      intro q hq
      simpa only [Finset.mem_singleton.mp hq] using hlarge hp
    simpa using square_subproduct_mem_squareD N (by omega)
      ({p} : Finset ℕ) hsingleton (Finset.singleton_nonempty p)
  have hinj : Function.Injective (fun p : ℕ => p ^ 2) :=
    Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
  have hcardE : E.card = P.card := by
    simpa only [E] using Finset.card_image_of_injective P hinj
  have hreserveNat : 4 * M ^ 9 ≤ P.card := by
    dsimp [P, N]
    exact widePrimes_card_pure_power M (M ^ 10) hM le_rfl (by nlinarith)
  have hreserve : 4 * (M : ℝ) ^ 9 ≤ (E.card : ℝ) := by
    rw [hcardE]
    exact_mod_cast hreserveNat
  have hNpow : (N : ℝ) ^ 2 = (M : ℝ) ^ 20 := by
    dsimp [N]
    push_cast
    ring
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hbounds : ∀ d ∈ E, 2 * |(h : ℝ)| < (d : ℝ) ∧ (d : ℝ) ≤ U := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    have hpP : p ∈ widePrimes N := hp
    obtain ⟨hp4, hpnot⟩ := Finset.mem_sdiff.mp hpP
    obtain ⟨hpupper, hpprime⟩ := Nat.mem_primesLE.mp hp4
    have hpN : N < p := by
      by_contra hpbad
      exact hpnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    have hpNreal : (N : ℝ) < p := by exact_mod_cast hpN
    have hpupperReal : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hpupper
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    have hpnonneg : (0 : ℝ) ≤ p := by positivity
    have hsqlo : (N : ℝ) ^ 2 < (p : ℝ) ^ 2 := by
      exact pow_lt_pow_left₀ hpNreal hNnonneg (by decide)
    have hsqupp : (p : ℝ) ^ 2 ≤ (4 * (N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hpnonneg hpupperReal 2
    constructor
    · norm_num [Nat.cast_pow]
      rw [hNpow] at hsqlo
      exact hhi.trans_lt hsqlo
    · calc
        (((p ^ 2 : ℕ) : ℝ)) = (p : ℝ) ^ 2 := by norm_num
        _ ≤ (4 * (N : ℝ)) ^ 2 := hsqupp
        _ = 16 * (N : ℝ) ^ 2 := by ring
        _ = U := by rw [hNpow]
  have henergy := residueEnergy_ge_card_mul_ratio_sq
    (squareD N) E (h : ℝ) U hEsub hU hbounds
  have hratio : (M : ℝ) ^ 16 / U ≤ |(h : ℝ)| / U :=
    div_le_div_of_nonneg_right hlo hU.le
  have hratio0 : 0 ≤ (M : ℝ) ^ 16 / U := by positivity
  have hratioSq : ((M : ℝ) ^ 16 / U) ^ 2 ≤ (|(h : ℝ)| / U) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hcombined :
      4 * (M : ℝ) ^ 9 * (((M : ℝ) ^ 16 / U) ^ 2) ≤
        (E.card : ℝ) * ((|(h : ℝ)| / U) ^ 2) := by
    calc
      4 * (M : ℝ) ^ 9 * (((M : ℝ) ^ 16 / U) ^ 2) ≤
          (E.card : ℝ) * (((M : ℝ) ^ 16 / U) ^ 2) :=
        mul_le_mul_of_nonneg_right hreserve (sq_nonneg _)
      _ ≤ (E.card : ℝ) * ((|(h : ℝ)| / U) ^ 2) :=
        mul_le_mul_of_nonneg_left hratioSq (by positivity)
  calc
    (M : ℝ) / 64 =
        4 * (M : ℝ) ^ 9 * (((M : ℝ) ^ 16 / U) ^ 2) := by
      dsimp [U]
      field_simp
      ring
    _ ≤ (E.card : ℝ) * ((|(h : ℝ)| / U) ^ 2) := hcombined
    _ ≤ residueEnergy (squareD N) (fun d => (h : ℝ) / (d : ℝ)) := henergy

/-- The bottom-frequency energy lower bound gives uniform exponential decay
for every Bernoulli parameter with variance at least `κ`. -/
theorem bottom_frequency_centeredProduct_norm_le
    (M : ℕ) (hM : 262144 ≤ M) (p κ : ℝ) (h : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ p * (1 - p))
    (hlo : (M : ℝ)^16 ≤ |(h : ℝ)|)
    (hhi : 2 * |(h : ℝ)| ≤ (M : ℝ)^20) :
    ‖centeredProduct (squareD (M^10)) p h‖ ≤
      Real.exp (-κ * (M : ℝ) / 8) := by
  have henergy := bottom_frequency_energy_lower M hM h hlo hhi
  have hbound := norm_centeredProduct_le_of_energy_lower
    (squareD (M ^ 10)) p κ ((M : ℝ) / 64) h hp0 hp1 hκ0 hκ henergy
  calc
    ‖centeredProduct (squareD (M ^ 10)) p h‖ ≤
        Real.exp (-8 * κ * ((M : ℝ) / 64)) := hbound
    _ = Real.exp (-κ * (M : ℝ) / 8) := by
      congr 1
      ring

end ReciprocalSquares
