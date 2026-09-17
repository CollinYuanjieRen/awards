import Erdos381Lower.Defs

/-!
# Erdős #381 (JSP-000315), lower bound: trial numbers

Erdős's 1944 argument perturbs a highly composite number `n` by raising the exponent of every
prime in a finite set `Up` by one and lowering the exponent of every prime in a finite set `Dn`
by one.  The resulting *trial number* is `n * ∏ Up / ∏ Dn`, an exact natural division.

This module is the workhorse: exactness of the division (`dn_dvd`, `trial_mul`, `trial_pos`),
the prime valuations of a trial number (`factorization_trial`), the divisor-count identity in
cross-multiplied `ℕ` form (`tau_trial_mul`) and in `ℝ` form (`tau_trial_eq`), and the additive
behaviour of the logarithm (`log_trial`).
-/

namespace Erdos381Lower

open Erdos381

variable {n : ℕ} {Up Dn : Finset ℕ}

/-- The trial number built from `n` by multiplying in the primes of `Up` and dividing out the
primes of `Dn`.  The division is exact whenever every prime of `Dn` divides `n`. -/
def trial (n : ℕ) (Up Dn : Finset ℕ) : ℕ := (n * ∏ r ∈ Up, r) / ∏ r ∈ Dn, r

/-- The `p`-adic valuation of a product of distinct primes is the indicator of the index set. -/
theorem factorization_prod_primes {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (p : ℕ) :
    (∏ r ∈ S, r).factorization p = if p ∈ S then 1 else 0 := by
  classical
  have hterm : ∀ r ∈ S, (Nat.factorization r) p = if r = p then 1 else 0 := by
    intro r hr
    rw [(hS r hr).factorization, Finsupp.single_apply]
  rw [Nat.factorization_prod fun r hr ↦ (hS r hr).ne_zero, Finset.sum_apply',
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq']

/-- The product of the primes of `Dn` divides `n * ∏ Up`: exactness of the trial division. -/
theorem dn_dvd (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    (∏ r ∈ Dn, r) ∣ n * ∏ r ∈ Up, r := by
  classical
  have hD : (∏ r ∈ Dn, r) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr ↦ (hDn r hr).ne_zero
  have hU : (∏ r ∈ Up, r) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr ↦ (hUp r hr).ne_zero
  have hNU : n * ∏ r ∈ Up, r ≠ 0 := Nat.mul_ne_zero hn.ne' hU
  rw [← Nat.factorization_le_iff_dvd hD hNU, Finsupp.le_def]
  intro p
  rw [Nat.factorization_mul hn.ne' hU, Finsupp.add_apply,
    factorization_prod_primes hDn, factorization_prod_primes hUp]
  by_cases hp : p ∈ Dn
  · have := hpos p hp
    simp only [if_pos hp]
    split <;> omega
  · simp [hp]

/-- The trial number is positive. -/
theorem trial_pos (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    0 < trial n Up Dn := by
  have hD : 0 < ∏ r ∈ Dn, r :=
    Finset.prod_pos fun r hr ↦ (hDn r hr).pos
  have hU : 0 < ∏ r ∈ Up, r :=
    Finset.prod_pos fun r hr ↦ (hUp r hr).pos
  exact Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hn hU) (dn_dvd hn hUp hDn hpos)) hD

/-- The trial division is exact. -/
theorem trial_mul (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    trial n Up Dn * ∏ r ∈ Dn, r = n * ∏ r ∈ Up, r :=
  Nat.div_mul_cancel (dn_dvd hn hUp hDn hpos)

/-- The prime valuations of a trial number: `+1` on `Up`, `-1` on `Dn`, unchanged elsewhere.
For a non-prime `r` every term vanishes, so the right-hand side is `0`. -/
theorem factorization_trial (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) (r : ℕ) :
    (trial n Up Dn).factorization r =
      n.factorization r + (if r ∈ Up then 1 else 0) - (if r ∈ Dn then 1 else 0) := by
  classical
  have hU : (∏ r ∈ Up, r) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr ↦ (hUp r hr).ne_zero
  rw [trial, Nat.factorization_div (dn_dvd hn hUp hDn hpos), Finsupp.tsub_apply,
    Nat.factorization_mul hn.ne' hU, Finsupp.add_apply, factorization_prod_primes hUp,
    factorization_prod_primes hDn]

/-- `tau m = ∏ (vₚ m + 1)` over any finite set of primes containing the prime factors of `m`. -/
theorem tau_eq_prod_of_subset {m : ℕ} (hm : m ≠ 0) {S : Finset ℕ}
    (hS : m.primeFactors ⊆ S) :
    tau m = ∏ r ∈ S, (m.factorization r + 1) := by
  rw [tau, Nat.card_divisors hm]
  refine Finset.prod_subset hS fun r _ hr ↦ ?_
  rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hr
  simp [hr]

/-- The divisor-count identity for a trial number, cross-multiplied so that it lives in `ℕ`. -/
theorem tau_trial_mul (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hdisj : Disjoint Up Dn) (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    tau (trial n Up Dn) * (∏ r ∈ Dn, (n.factorization r + 1)) *
        (∏ r ∈ Up, (n.factorization r + 1)) =
      tau n * (∏ r ∈ Dn, n.factorization r) * (∏ r ∈ Up, (n.factorization r + 2)) := by
  classical
  have hfac := factorization_trial hn hUp hDn hpos
  have hDnsub : Dn ⊆ n.primeFactors := fun r hr ↦ by
    have := hpos r hr
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  set S : Finset ℕ := n.primeFactors ∪ Up with hSdef
  have hUDS : Up ∪ Dn ⊆ S :=
    Finset.union_subset Finset.subset_union_right (hDnsub.trans Finset.subset_union_left)
  have htrialS : (trial n Up Dn).primeFactors ⊆ S := by
    intro r hr
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hfac r] at hr
    by_cases hrU : r ∈ Up
    · exact Finset.mem_union_right _ hrU
    · refine Finset.mem_union_left _ ?_
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      by_cases hrD : r ∈ Dn <;> simp only [hrU, hrD, if_true, if_false] at hr <;> omega
  have hsplit : ∀ f : ℕ → ℕ, (∏ r ∈ S, f r) =
      (∏ r ∈ S \ (Up ∪ Dn), f r) * ((∏ r ∈ Up, f r) * ∏ r ∈ Dn, f r) := by
    intro f
    rw [← Finset.prod_union hdisj, Finset.prod_sdiff hUDS]
  have h1 : tau n = (∏ r ∈ S \ (Up ∪ Dn), (n.factorization r + 1)) *
      ((∏ r ∈ Up, (n.factorization r + 1)) * ∏ r ∈ Dn, (n.factorization r + 1)) := by
    rw [tau_eq_prod_of_subset hn.ne' (Finset.subset_union_left (s₂ := Up)), hsplit]
  have h2 : tau (trial n Up Dn) = (∏ r ∈ S \ (Up ∪ Dn), (n.factorization r + 1)) *
      ((∏ r ∈ Up, (n.factorization r + 2)) * ∏ r ∈ Dn, n.factorization r) := by
    rw [tau_eq_prod_of_subset (trial_pos hn hUp hDn hpos).ne' htrialS, hsplit]
    refine congrArg₂ _ (Finset.prod_congr rfl fun r hr ↦ ?_) (congrArg₂ _
      (Finset.prod_congr rfl fun r hr ↦ ?_) (Finset.prod_congr rfl fun r hr ↦ ?_))
    · have hr' := Finset.mem_sdiff.mp hr
      have hrU : r ∉ Up := fun h ↦ hr'.2 (Finset.mem_union_left _ h)
      have hrD : r ∉ Dn := fun h ↦ hr'.2 (Finset.mem_union_right _ h)
      rw [hfac r]
      simp [hrU, hrD]
    · have hrD : r ∉ Dn := Finset.disjoint_left.mp hdisj hr
      rw [hfac r]
      simp [hr, hrD]
    · have hrU : r ∉ Up := Finset.disjoint_right.mp hdisj hr
      have := hpos r hr
      rw [hfac r]
      simp only [hrU, hr, if_true, if_false]
      omega
  rw [h1, h2]
  ring

/-- The divisor-count identity in the real-valued form used by the size estimate (digest §6.1). -/
theorem tau_trial_eq (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hdisj : Disjoint Up Dn) (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    (tau (trial n Up Dn) : ℝ) =
      tau n * (∏ r ∈ Up, ((n.factorization r + 2 : ℝ) / (n.factorization r + 1))) *
        (∏ r ∈ Dn, ((n.factorization r : ℝ) / (n.factorization r + 1))) := by
  have key := tau_trial_mul hn hUp hDn hdisj hpos
  have hcast : (tau (trial n Up Dn) : ℝ) * (∏ r ∈ Dn, ((n.factorization r : ℝ) + 1)) *
      (∏ r ∈ Up, ((n.factorization r : ℝ) + 1)) =
      (tau n : ℝ) * (∏ r ∈ Dn, (n.factorization r : ℝ)) *
        ∏ r ∈ Up, ((n.factorization r : ℝ) + 2) := by
    exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℝ)) key
  have hD : (∏ r ∈ Dn, ((n.factorization r : ℝ) + 1)) ≠ 0 := by positivity
  have hU : (∏ r ∈ Up, ((n.factorization r : ℝ) + 1)) ≠ 0 := by positivity
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  field_simp
  linear_combination hcast

/-- The logarithm of a trial number. -/
theorem log_trial (hn : 0 < n) (hUp : ∀ r ∈ Up, r.Prime) (hDn : ∀ r ∈ Dn, r.Prime)
    (hpos : ∀ r ∈ Dn, 1 ≤ n.factorization r) :
    Real.log (trial n Up Dn) =
      Real.log n + (∑ r ∈ Up, Real.log r) - ∑ r ∈ Dn, Real.log r := by
  have htp : 0 < trial n Up Dn := trial_pos hn hUp hDn hpos
  have hcast : ((trial n Up Dn : ℕ) : ℝ) * (∏ r ∈ Dn, (r : ℝ)) =
      (n : ℝ) * ∏ r ∈ Up, (r : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.cast_mul, ← Nat.cast_mul,
      trial_mul hn hUp hDn hpos]
  have hDne : (∏ r ∈ Dn, (r : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r hr ↦ Nat.cast_ne_zero.mpr (hDn r hr).ne_zero
  have hUne : (∏ r ∈ Up, (r : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r hr ↦ Nat.cast_ne_zero.mpr (hUp r hr).ne_zero
  have h1 := congrArg Real.log hcast
  rw [Real.log_mul (Nat.cast_ne_zero.mpr htp.ne') hDne,
    Real.log_mul (Nat.cast_ne_zero.mpr hn.ne') hUne,
    Real.log_prod fun r hr ↦ Nat.cast_ne_zero.mpr (hDn r hr).ne_zero,
    Real.log_prod fun r hr ↦ Nat.cast_ne_zero.mpr (hUp r hr).ne_zero] at h1
  linarith

end Erdos381Lower
