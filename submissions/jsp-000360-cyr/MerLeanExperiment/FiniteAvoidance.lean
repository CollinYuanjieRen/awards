import MerLeanExperiment.IntervalSieve

namespace Erdos441

/-- The finite set of primes at most `Z`. -/
def sievePrimes (Z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Z).filter Nat.Prime

/-- A prime index in the finite sieve up to `Z`. -/
abbrev SievePrime (Z : ℕ) := ↥(sievePrimes Z)

/-- A sufficiently long integer interval contains a point avoiding all the
prescribed residue sets at primes up to `Z`. -/
theorem exists_interval_avoiding
    (M Z : ℕ) (hM : 3 ≤ M) (a b : ℤ) (hab : a ≤ b)
    (R : (p : SievePrime Z) → Finset (ZMod p.val))
    (hsmall : ∀ p, p.val ≤ M → R p = ∅)
    (hcard : ∀ p, 2 * (R p).card ≤ M)
    (hlength : (((2 * M) ^ Z : ℕ) : ℤ) < b - a) :
    ∃ k ∈ Finset.Ioc a b, ∀ p, (k : ZMod p.val) ∉ R p := by
  classical
  have hprime (p : SievePrime Z) : p.val.Prime :=
    (Finset.mem_filter.mp p.property).2
  have hm (p : SievePrime Z) : 0 < p.val := (hprime p).pos
  have hc : Pairwise (fun p q : SievePrime Z => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hprime p) (hprime q)).2
      (fun h => hpq (Subtype.ext h))
  have hsieve := interval_sieve_discrepancy a b hab (fun p : SievePrime Z => p.val)
    hm hc R
  let W : ℚ := ∏ p : SievePrime Z,
    (1 - ((R p).card : ℚ) / p.val)
  let E : ℚ := ∏ p : SievePrime Z, (1 + ((R p).card : ℚ))
  let n := Fintype.card (SievePrime Z)
  have hn : n ≤ Z := by
    dsimp [n]
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have htwo_card_le (p : SievePrime Z) : 2 * (R p).card ≤ p.val := by
    by_cases hpM : p.val ≤ M
    · rw [hsmall p hpM]
      simp
    · exact (hcard p).trans (Nat.le_of_lt (lt_of_not_ge hpM))
  have hfactor (p : SievePrime Z) :
      (1 / 2 : ℚ) ≤ 1 - ((R p).card : ℚ) / p.val := by
    have hpQ : (0 : ℚ) < p.val := by exact_mod_cast hm p
    have htwoQ : (2 : ℚ) * (R p).card ≤ p.val := by
      exact_mod_cast htwo_card_le p
    have hfrac : ((R p).card : ℚ) / p.val ≤ 1 / 2 := by
      rw [div_le_iff₀ hpQ]
      nlinarith
    linarith
  have hWn : (1 / 2 : ℚ) ^ n ≤ W := by
    have hprod := Finset.prod_le_prod
      (s := (Finset.univ : Finset (SievePrime Z)))
      (f := fun _ => (1 / 2 : ℚ))
      (g := fun p => 1 - ((R p).card : ℚ) / p.val)
      (by intro p hp; norm_num)
      (by intro p hp; exact hfactor p)
    simpa [W, n] using hprod
  have hWZ : (1 / 2 : ℚ) ^ Z ≤ W :=
    (pow_le_pow_of_le_one (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num) hn).trans hWn
  have herrfactor (p : SievePrime Z) :
      (1 + ((R p).card : ℚ)) ≤ M := by
    have hpCard := hcard p
    exact_mod_cast (show 1 + (R p).card ≤ M by omega)
  have hEn : E ≤ (M : ℚ) ^ n := by
    have hprod := Finset.prod_le_prod
      (s := (Finset.univ : Finset (SievePrime Z)))
      (f := fun p => (1 + ((R p).card : ℚ)))
      (g := fun _ => (M : ℚ))
      (by intro p hp; positivity)
      (by intro p hp; exact herrfactor p)
    simpa [E, n] using hprod
  have hEZ : E ≤ (M : ℚ) ^ Z :=
    hEn.trans (pow_le_pow_right₀ (a := (M : ℚ)) (by exact_mod_cast hM.trans' (by decide)) hn)
  have hlengthQ : (((2 * M) ^ Z : ℕ) : ℚ) < ((b - a : ℤ) : ℚ) := by
    exact_mod_cast hlength
  have hhalf_pos : (0 : ℚ) < (1 / 2 : ℚ) ^ Z := pow_pos (by norm_num) Z
  have hidentity :
      (((2 * M) ^ Z : ℕ) : ℚ) * (1 / 2 : ℚ) ^ Z = (M : ℚ) ^ Z := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  have hL0 : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hstrict : E < ((b - a : ℤ) : ℚ) * W := by
    calc
      E ≤ (M : ℚ) ^ Z := hEZ
      _ = (((2 * M) ^ Z : ℕ) : ℚ) * (1 / 2 : ℚ) ^ Z := hidentity.symm
      _ < ((b - a : ℤ) : ℚ) * (1 / 2 : ℚ) ^ Z :=
        mul_lt_mul_of_pos_right hlengthQ hhalf_pos
      _ ≤ ((b - a : ℤ) : ℚ) * W := mul_le_mul_of_nonneg_left hWZ hL0
  let good := {k ∈ Finset.Ioc a b |
    ∀ p : SievePrime Z, (k : ZMod p.val) ∉ R p}
  have hgood_pos : 0 < good.card := by
    by_contra hnot
    have hzero : good.card = 0 := Nat.eq_zero_of_not_pos hnot
    have hsieve' :
        |(good.card : ℚ) - ((b - a : ℤ) : ℚ) * W| ≤ E := by
      simpa [good, W, E] using hsieve
    rw [hzero, Nat.cast_zero, zero_sub, abs_neg] at hsieve'
    exact (not_lt_of_ge ((le_abs_self _).trans hsieve')) hstrict
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hgood_pos
  have hk' := Finset.mem_filter.mp hk
  exact ⟨k, hk'.1, hk'.2⟩

end Erdos441
