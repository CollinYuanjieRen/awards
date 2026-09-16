import Mathlib

/-!
# Erdős problem #276: Graham's theorem

**Graham's theorem (1964).** There is a Lucas sequence `a (n + 2) = a (n + 1) + a n` all of whose
terms are composite, such that no integer `≥ 2` divides every term.

We use Vsemirnov's initial pair (2004), `a 0 = 106276436867`, `a 1 = 35256392432`, which is the
smallest known such pair.  The proof is a covering argument: `cert` lists 34 triples `(p, per, r)`
such that

* `vsemirnov` is periodic modulo `p` with period `per` (checked on the initial pair);
* `p ∣ vsemirnov r`;
* and every residue class modulo `1440` meets some `n ≡ r [MOD per]`, where `1440` is the lcm of
  all the periods.

Consequently every term has one of the 17 covering primes `2, …, 2521` as a divisor, and since every
term is at least `35256392432 > 2521`, that divisor is proper.  Consecutive terms are coprime
(the initial pair is), so no fixed integer `≥ 2` divides all terms.

The only open part of Erdős #276 — whether *every* such sequence must arise from a covering system
— is **not** claimed here.
-/

namespace Erdos276

/-! ### Definitions -/

/-- A Lucas sequence: `a (n + 2) = a (n + 1) + a n` for all `n`. -/
def IsLucasSequence (a : ℕ → ℕ) : Prop := ∀ n, a (n + 2) = a (n + 1) + a n

/-- Pair iteration `(a n, a (n + 1))` for the Lucas sequence with initial terms `x, y`.
Iterating on pairs keeps kernel evaluation linear in `n`. -/
def lucasPair (x y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (x, y)
  | n + 1 => ((lucasPair x y n).2, (lucasPair x y n).1 + (lucasPair x y n).2)

/-- The Lucas sequence with initial terms `x, y`, i.e. `lucas x y 0 = x`, `lucas x y 1 = y`
and `lucas x y (n + 2) = lucas x y (n + 1) + lucas x y n`. -/
def lucas (x y : ℕ) (n : ℕ) : ℕ := (lucasPair x y n).1

/-- `lucas x y` really is a Lucas sequence. -/
theorem isLucasSequence_lucas (x y : ℕ) : IsLucasSequence (lucas x y) := by
  intro n
  have h : lucas x y (n + 2) = lucas x y n + lucas x y (n + 1) := rfl
  rw [h, Nat.add_comm]

/-- Vsemirnov's initial pair (2004): the smallest known initial pair for which every term of the
resulting Lucas sequence is composite. -/
def vsemirnov : ℕ → ℕ := lucas 106276436867 35256392432

/-- Vsemirnov's sequence is a Lucas sequence. -/
theorem vsemirnov_isLucasSequence : IsLucasSequence vsemirnov :=
  isLucasSequence_lucas _ _
/-!
### Generic facts about Lucas sequences

Three families of lemmas, all stated for an arbitrary `a : ℕ → ℕ` with `IsLucasSequence a`:

* a lower bound `min (a 0) (a 1) ≤ a n`;
* periodicity modulo `p`: if the pair `(a 0, a 1)` repeats modulo `p` after `per` steps, then the
  whole sequence is periodic modulo `p` with period `per`;
* consecutive terms keep the gcd of the initial pair.
-/

/-- Auxiliary two-step form of `lucas_min_le`: the bound holds simultaneously at `n` and `n + 1`. -/
theorem lucas_min_le_aux {a : ℕ → ℕ} (ha : IsLucasSequence a) (n : ℕ) :
    min (a 0) (a 1) ≤ a n ∧ min (a 0) (a 1) ≤ a (n + 1) := by
  induction n with
  | zero => exact ⟨min_le_left _ _, min_le_right _ _⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    show min (a 0) (a 1) ≤ a (k + 2)
    rw [ha k]
    exact le_trans ih.2 (Nat.le_add_right _ _)

/-- Every term of a Lucas sequence is at least the smaller of its two initial terms. -/
theorem lucas_min_le {a : ℕ → ℕ} (ha : IsLucasSequence a) (n : ℕ) : min (a 0) (a 1) ≤ a n :=
  (lucas_min_le_aux ha n).1

/-- Auxiliary pair form of periodicity: if the initial pair repeats modulo `p` after `per` steps,
then every consecutive pair does. -/
theorem mod_add_period_aux {a : ℕ → ℕ} (ha : IsLucasSequence a) {p per : ℕ}
    (h0 : a per % p = a 0 % p) (h1 : a (per + 1) % p = a 1 % p) (n : ℕ) :
    a (n + per) % p = a n % p ∧ a (n + per + 1) % p = a (n + 1) % p := by
  induction n with
  | zero => exact ⟨by simpa using h0, by simpa using h1⟩
  | succ k ih =>
    obtain ⟨e0, e1⟩ := ih
    refine ⟨by rw [show k + 1 + per = k + per + 1 by omega]; exact e1, ?_⟩
    have hl : a (k + 1 + per + 1) = a (k + per + 1) + a (k + per) := by
      rw [show k + 1 + per + 1 = k + per + 2 by omega]
      exact ha (k + per)
    have hr : a (k + 1 + 1) = a (k + 1) + a k := by
      rw [show k + 1 + 1 = k + 2 by omega]
      exact ha k
    rw [hl, hr, Nat.add_mod, Nat.add_mod (a (k + 1)) (a k), e0, e1]

/-- Periodicity modulo `p`, iterated: shifting the index by any multiple of `per` does not change
the residue. -/
theorem mod_add_mul_period {a : ℕ → ℕ} (ha : IsLucasSequence a) {p per : ℕ}
    (h0 : a per % p = a 0 % p) (h1 : a (per + 1) % p = a 1 % p) (q : ℕ) :
    ∀ n, a (n + per * q) % p = a n % p := by
  induction q with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    rw [Nat.mul_succ, ← Nat.add_assoc, (mod_add_period_aux ha h0 h1 (n + per * m)).1]
    exact ih n

/-- Periodicity modulo `p`, reduced form: the residue of `a n` only depends on `n % per`. -/
theorem mod_eq_mod_mod {a : ℕ → ℕ} (ha : IsLucasSequence a) {p per : ℕ}
    (h0 : a per % p = a 0 % p) (h1 : a (per + 1) % p = a 1 % p) (n : ℕ) :
    a n % p = a (n % per) % p := by
  conv_lhs => rw [← Nat.mod_add_div n per]
  exact mod_add_mul_period ha h0 h1 (n / per) (n % per)

/-- The gcd of two consecutive terms is invariant under one step of the recursion. -/
theorem gcd_succ_succ {a : ℕ → ℕ} (ha : IsLucasSequence a) (n : ℕ) :
    Nat.gcd (a (n + 1)) (a (n + 2)) = Nat.gcd (a n) (a (n + 1)) := by
  rw [ha n, Nat.add_comm (a (n + 1)) (a n), Nat.gcd_add_self_right, Nat.gcd_comm]

/-- Consecutive terms of a Lucas sequence always have the same gcd as the initial pair. -/
theorem gcd_eq_gcd_zero_one {a : ℕ → ℕ} (ha : IsLucasSequence a) (n : ℕ) :
    Nat.gcd (a n) (a (n + 1)) = Nat.gcd (a 0) (a 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show Nat.gcd (a (k + 1)) (a (k + 2)) = Nat.gcd (a 0) (a 1)
    rw [gcd_succ_succ ha k]
    exact ih


/-! ### The covering certificate -/

/-- The covering certificate: triples `(p, per, r)` meaning "`vsemirnov` has period `per`
modulo `p`, and `p ∣ vsemirnov n` whenever `n ≡ r [MOD per]`". -/
def cert : List (ℕ × ℕ × ℕ) :=
  [(2,3,1), (3,8,3), (3,8,7), (5,20,4), (5,20,9), (5,20,14), (5,20,19), (7,16,5), (7,16,13), (11,10,6),
   (17,36,2), (17,36,11), (17,36,20), (17,36,29), (19,18,14), (23,48,17), (23,48,41), (31,30,0),
   (41,40,18), (41,40,38), (47,32,9), (47,32,25), (61,60,12), (61,60,27), (61,60,42), (61,60,57),
   (107,72,8), (107,72,44), (181,90,80), (541,90,62), (1103,96,33), (1103,96,81), (2521,120,48), (2521,120,108)]

set_option maxRecDepth 10000 in
/-- Every triple of the certificate is valid: `p` is a nontrivial modulus smaller than every term
of the sequence, `per` is a positive period of `vsemirnov` modulo `p` dividing `1440`, and
`p ∣ vsemirnov r`.  Checked by kernel evaluation. -/
theorem cert_ok : ∀ t ∈ cert,
    1 < t.1 ∧ 0 < t.2.1 ∧ t.1 < 35256392432 ∧ 1440 % t.2.1 = 0 ∧
      vsemirnov t.2.1 % t.1 = vsemirnov 0 % t.1 ∧
      vsemirnov (t.2.1 + 1) % t.1 = vsemirnov 1 % t.1 ∧
      vsemirnov t.2.2 % t.1 = 0 := by
  decide

set_option maxRecDepth 10000 in
/-- The certificate is a covering system: every residue modulo `1440` is matched by some triple.
Checked by kernel evaluation. -/
theorem cert_cover : ∀ n < 1440, ∃ t ∈ cert, n % t.2.1 = t.2.2 := by
  decide

/-- The first term of Vsemirnov's sequence. -/
theorem vsemirnov_zero : vsemirnov 0 = 106276436867 := rfl

/-- The second term of Vsemirnov's sequence. -/
theorem vsemirnov_one : vsemirnov 1 = 35256392432 := rfl

/-- Vsemirnov's initial pair is coprime. -/
theorem vsemirnov_gcd_zero_one : Nat.gcd (vsemirnov 0) (vsemirnov 1) = 1 := by
  rw [vsemirnov_zero, vsemirnov_one]
  norm_num

/-- Every term of Vsemirnov's sequence is at least `35256392432`, hence larger than every
covering prime. -/
theorem vsemirnov_ge (k : ℕ) : 35256392432 ≤ vsemirnov k := by
  have h := lucas_min_le vsemirnov_isLucasSequence k
  rw [vsemirnov_zero, vsemirnov_one] at h
  omega

/-- Every term of Vsemirnov's sequence has a divisor strictly between `1` and the term itself. -/
theorem vsemirnov_exists_proper_factor : ∀ k, ∃ p, 1 < p ∧ p < vsemirnov k ∧ p ∣ vsemirnov k := by
  intro k
  obtain ⟨t, ht, hmod⟩ := cert_cover (k % 1440) (Nat.mod_lt _ (by norm_num))
  obtain ⟨hp1, -, hplt, h1440, hper0, hper1, hr0⟩ := cert_ok t ht
  refine ⟨t.1, hp1, lt_of_lt_of_le hplt (vsemirnov_ge k), ?_⟩
  have hk : k % t.2.1 = t.2.2 := by
    rw [← hmod, Nat.mod_mod_of_dvd k (Nat.dvd_of_mod_eq_zero h1440)]
  have hv := mod_eq_mod_mod vsemirnov_isLucasSequence hper0 hper1 k
  rw [hk, hr0] at hv
  exact Nat.dvd_of_mod_eq_zero hv

/-- No term of Vsemirnov's sequence is prime. -/
theorem vsemirnov_not_prime : ∀ k, ¬ (vsemirnov k).Prime := by
  intro k hk
  obtain ⟨p, hp1, hp2, hp3⟩ := vsemirnov_exists_proper_factor k
  rcases hk.eq_one_or_self_of_dvd p hp3 with h | h <;> omega

/-- Every term of Vsemirnov's sequence exceeds `1`; together with `vsemirnov_not_prime` this says
that every term is composite. -/
theorem vsemirnov_one_lt : ∀ k, 1 < vsemirnov k := by
  intro k
  have := vsemirnov_ge k
  omega

/-- Consecutive terms of Vsemirnov's sequence are coprime. -/
theorem vsemirnov_coprime_succ : ∀ k, Nat.Coprime (vsemirnov k) (vsemirnov (k + 1)) := by
  intro k
  exact (gcd_eq_gcd_zero_one vsemirnov_isLucasSequence k).trans vsemirnov_gcd_zero_one

/-- No integer `≥ 2` divides every term of Vsemirnov's sequence. -/
theorem vsemirnov_no_common_divisor : ∀ d, 2 ≤ d → ∃ k, ¬ d ∣ vsemirnov k := by
  intro d hd
  by_cases h0 : d ∣ vsemirnov 0
  · refine ⟨1, fun h1 => ?_⟩
    have hg : d ∣ Nat.gcd (vsemirnov 0) (vsemirnov 1) := Nat.dvd_gcd h0 h1
    rw [vsemirnov_gcd_zero_one] at hg
    have := Nat.le_of_dvd Nat.one_pos hg
    omega
  · exact ⟨0, h0⟩

/-- Graham's theorem: a Lucas sequence of composite numbers with no common divisor of all terms. -/
theorem exists_composite_lucasSequence :
    ∃ a : ℕ → ℕ, IsLucasSequence a ∧ (∀ k, 1 < a k ∧ ¬ (a k).Prime) ∧ (∀ d, 2 ≤ d → ∃ k, ¬ d ∣ a k) :=
  ⟨vsemirnov, vsemirnov_isLucasSequence,
    fun k => ⟨vsemirnov_one_lt k, vsemirnov_not_prime k⟩, vsemirnov_no_common_divisor⟩

end Erdos276
