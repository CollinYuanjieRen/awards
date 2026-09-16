import Erdos387Proof.GcdFactorReindex
import Erdos387Proof.MediumZeroMode

/-! The zero Fourier coefficients of every overlapping sieve residue,
reindexed exactly by the gcd and divided factor interval. -/

namespace Erdos387Proof.MediumZeroModeIdentity

open GcdFactorReindex MediumZeroMode
open scoped BigOperators

theorem sum_interval_eq_sum_gcd_fibres (A B Q g : ℕ) (hg : 0 < g)
    (F : ℕ → ℝ) :
    (∑ d ∈ interval A B Q, F d) =
      ∑ u ∈ g.divisors,
        ∑ d ∈ (interval A B Q).filter (fun d => Nat.gcd g d = u), F d := by
  classical
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro d hd
  exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left g d, hg.ne'⟩

/-- Exact total zero mode for a single squarefree sieve product. This is
valid for arbitrary interval endpoints and keeps every gcd stratum. -/
theorem sum_zeroCoefficients_eq_zeroMode {g Q k A B : ℕ}
    (hg : 0 < g) (hcop : Nat.Coprime g Q) (mass : ℝ) :
    (∑ d ∈ interval A B Q,
      (k : ℝ) ^ (g / Nat.gcd g d).primeFactors.card *
        (mass / (Q * (g / Nat.gcd g d) * d : ℕ))) =
      zeroMode g Q k A B mass := by
  classical
  rw [sum_interval_eq_sum_gcd_fibres A B Q g hg]
  unfold zeroMode
  apply Finset.sum_congr rfl
  intro u hu
  have hudvd := Nat.dvd_of_mem_divisors hu
  have hu0 := Nat.pos_of_mem_divisors hu
  have huQ := hcop.of_dvd_left hudvd
  have hguv : u * (g / u) = g := Nat.mul_div_cancel' hudvd
  have hgf : (interval A B Q).filter (fun d => Nat.gcd g d = u) =
      (interval A B Q).filter (fun d => Nat.gcd (u * (g / u)) d = u) := by
    rw [hguv]
  rw [hgf, sum_filter_gcd_eq hu0 huQ]
  unfold harmonicBlock
  rw [Finset.mul_sum]
  have hset : interval (A / u) (B / u) (Q * (g / u)) =
      (Finset.Ioc (A / u) (B / u)).filter (fun t => Nat.Coprime (Q * (g / u)) t) := by
    ext t
    simp only [interval, Finset.mem_filter]
    exact and_congr_right (fun _ => Nat.coprime_comm)
  rw [hset]
  apply Finset.sum_congr rfl
  intro t ht
  have htv := (Nat.coprime_mul_iff_left.mp (Finset.mem_filter.mp ht).2).2
  have hgd : Nat.gcd g (u * t) = u := by
    rw [← hguv]
    exact (gcd_mul_split_iff hu0).mpr htv
  rw [hgd]
  have hden : Q * (g / u) * (u * t) = (Q * g) * t := by
    calc
      _ = Q * (u * (g / u)) * t := by ring
      _ = _ := by rw [hguv]
  rw [hden]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

end Erdos387Proof.MediumZeroModeIdentity
