import Mathlib

/-!
# Erdős Problem #307: solutions have `P`, `Q` disjoint with `∑_{P ∪ Q} 1/p ≥ 2`

Barbeau and Erdős asked whether there are finite sets of primes `P`, `Q` with
`1 = (∑_{p ∈ P} 1/p)(∑_{q ∈ Q} 1/q)` (OPEN; not addressed here).  The problem page records: "It
is easy to see that, if `P` and `Q` are sets of primes, then `P` and `Q` are disjoint, and
`∑_{p ∈ P ∪ Q} 1/p ≥ 2`, whence `|P ∪ Q| ≥ 60`."  This file proves the first two claims — for
any solution, `P` and `Q` are disjoint and the reciprocal sum over `P ∪ Q` is at least `2` — with
the hypotheses in the exact form of the formal-conjectures statements for #307
(`hP`, `hQ`, `heq`); the numerical consequence `|P ∪ Q| ≥ 60` (whose page-stated derivation
needs the sizes of the reciprocal sums of the first primes, and which formal-conjectures records
via Bonfioli's machine-checked barriers) is not claimed, nor is the main question or Cambie's
coprime variants.

Proof.  Write `∑_{p ∈ P} 1/p = a/N` with `N = ∏_{p ∈ P} p` and `a = ∑_{p ∈ P} N/p`; each `p ∈ P`
divides every term of `a` except `N/p`, so `p ∤ a`.  Likewise `∑_{q ∈ Q} 1/q = b/M`.  The equation
gives `a·b = N·M`.  If some prime `p` lay in both `P` and `Q`, then `p² ∣ N·M = a·b` while `p ∤ a`
and `p ∤ b`, a contradiction; so `P` and `Q` are disjoint.  Then `∑_{P ∪ Q} 1/p = S + T` with
`S·T = 1`, `S, T > 0`, so `S + T ≥ 2` by AM–GM.
-/

namespace Erdos307

open scoped Finset

/-- If `p` is a member of `P` then dividing the product `∏ r ∈ P, r` by `p` removes exactly the
factor `p`. -/
private lemma prod_div_erase {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) (hp0 : 0 < p) :
    (∏ r ∈ P, r) / p = ∏ r ∈ P.erase p, r := by
  conv_lhs => rw [← Finset.mul_prod_erase P (fun r => r) hp]
  exact Nat.mul_div_cancel_left _ hp0

/-- For a finite set `P` of primes and `p ∈ P`, the numerator `∑ q ∈ P, (∏ r ∈ P, r) / q` is not
divisible by `p`: every summand except the one for `q = p` still contains the factor `p`, while
`(∏ r ∈ P, r) / p` is a product of primes different from `p`. -/
private lemma not_dvd_sum {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) {p : ℕ}
    (hp : p ∈ P) : ¬ p ∣ ∑ q ∈ P, (∏ r ∈ P, r) / q := by
  intro hdvd
  have hpp : p.Prime := hprime p hp
  have hrest : p ∣ ∑ q ∈ P.erase p, (∏ r ∈ P, r) / q := by
    refine Finset.dvd_sum fun q hq => ?_
    have hqP : q ∈ P := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    rw [prod_div_erase hqP (hprime q hqP).pos]
    exact Finset.dvd_prod_of_mem (fun r => r) (Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩)
  rw [← Finset.add_sum_erase P (fun q => (∏ r ∈ P, r) / q) hp] at hdvd
  have hdp : p ∣ (∏ r ∈ P, r) / p := by simpa using Nat.dvd_sub hdvd hrest
  rw [prod_div_erase hp hpp.pos] at hdp
  obtain ⟨r, hr, hdr⟩ := (hpp.prime.dvd_finsetProd_iff (fun r => r)).mp hdp
  exact Finset.ne_of_mem_erase hr
    ((Nat.prime_dvd_prime_iff_eq hpp (hprime r (Finset.mem_of_mem_erase hr))).mp hdr).symm

/-- The reciprocal sum of a finite set `P` of primes as a single fraction: with
`N = ∏ r ∈ P, r` the common denominator, `∑_{p ∈ P} 1/p = (∑_{q ∈ P} N / q) / N`, where the
inner divisions are exact in `ℕ`. -/
lemma sum_inv_primes_eq_div {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (p : ℚ)⁻¹
      = ((∑ q ∈ P, (∏ r ∈ P, r) / q : ℕ) : ℚ) / ((∏ r ∈ P, r : ℕ) : ℚ) := by
  have hN0 : 0 < ∏ r ∈ P, r := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hNQ : ((∏ r ∈ P, r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := hprime p hp
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.pos.ne'
  have hdd : p ∣ ∏ r ∈ P, r := Finset.dvd_prod_of_mem (fun r => r) hp
  have hmul : (((∏ r ∈ P, r) / p : ℕ) : ℚ) * (p : ℚ) = ((∏ r ∈ P, r : ℕ) : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdd]
  rw [inv_eq_one_div, div_eq_div_iff hpQ hNQ, one_mul, hmul]

/-- **Erdős #307, the page's easy remark**: for any solution `1 = (∑_{p ∈ P} 1/p)(∑_{q ∈ Q} 1/q)`
with `P`, `Q` finite sets of primes, `P` and `Q` are disjoint and `∑_{p ∈ P ∪ Q} 1/p ≥ 2`. -/
theorem erdos_307_disjoint_and_two_le {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    Disjoint P Q ∧ 2 ≤ ∑ p ∈ P ∪ Q, (p : ℚ)⁻¹ := by
  set N : ℕ := ∏ r ∈ P, r with hNdef
  set M : ℕ := ∏ r ∈ Q, r with hMdef
  set a : ℕ := ∑ q ∈ P, N / q with hadef
  set b : ℕ := ∑ q ∈ Q, M / q with hbdef
  have hN0 : 0 < N := Finset.prod_pos fun p hp => (hP p hp).pos
  have hM0 : 0 < M := Finset.prod_pos fun q hq => (hQ q hq).pos
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  have hMQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hSa : ∑ p ∈ P, (p : ℚ)⁻¹ = (a : ℚ) / (N : ℚ) := sum_inv_primes_eq_div hP
  have hTb : ∑ q ∈ Q, (q : ℚ)⁻¹ = (b : ℚ) / (M : ℚ) := sum_inv_primes_eq_div hQ
  -- Clearing denominators: `a * b = N * M` in `ℕ`.
  have habQ : (a : ℚ) * (b : ℚ) = (N : ℚ) * (M : ℚ) := by
    rw [hSa, hTb] at heq
    field_simp at heq
    linarith
  have hab : a * b = N * M := by exact_mod_cast habQ
  -- Disjointness.
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p hpP hpQ
    have hpp : p.Prime := hP p hpP
    have hpN : p ∣ N := Finset.dvd_prod_of_mem (fun r => r) hpP
    have hpM : p ∣ M := Finset.dvd_prod_of_mem (fun r => r) hpQ
    have hsq : p * p ∣ a * b := hab ▸ mul_dvd_mul hpN hpM
    have hpab : p ∣ a * b := dvd_trans (Dvd.intro p rfl) hsq
    rcases (Nat.Prime.dvd_mul hpp).mp hpab with h | h
    · exact not_dvd_sum hP hpP h
    · exact not_dvd_sum hQ hpQ h
  -- AM–GM on the two reciprocal sums.
  refine ⟨hdisj, ?_⟩
  have hSnn : (0 : ℚ) ≤ ∑ p ∈ P, (p : ℚ)⁻¹ :=
    Finset.sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  have hTnn : (0 : ℚ) ≤ ∑ q ∈ Q, (q : ℚ)⁻¹ :=
    Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)
  rw [Finset.sum_union hdisj]
  nlinarith [sq_nonneg ((∑ p ∈ P, (p : ℚ)⁻¹) - (∑ q ∈ Q, (q : ℚ)⁻¹)),
    sq_nonneg ((∑ p ∈ P, (p : ℚ)⁻¹) + (∑ q ∈ Q, (q : ℚ)⁻¹))]

end Erdos307

open Erdos307

/-- The same as a closed statement (no binders), used as the graded root. -/
theorem erdos_307_easy_closed :
    ¬ ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) ∧
      ¬ (Disjoint P Q ∧ 2 ≤ ∑ p ∈ P ∪ Q, (p : ℚ)⁻¹) := by
  rintro ⟨P, Q, hP, hQ, heq, h⟩
  exact h (erdos_307_disjoint_and_two_le hP hQ heq)
