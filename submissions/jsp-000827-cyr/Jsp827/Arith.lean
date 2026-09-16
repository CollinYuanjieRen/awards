import Mathlib

/-!
# Arithmetic of smooth multi-indices

For a list of primes `p : Fin d → ℕ` and an exponent vector `e`, `gval p e = ∏ p i ^ e i`.
Facts needed for the Marstrand counterexample (discrete log-coordinate version):

* if the primes `p i` include every prime `≤ 2^J` and every exponent `e i ≥ J`, then every
  `n` with `1 ≤ n ≤ 2^J` divides `gval p e`, and `n = gval p a` for the exponent vector
  `a = fun i => (Nat.factorization n) (p i)` with `a ≤ e` componentwise;
* `gval p` is injective (unique factorization);
* the `Nat.log 2` sandwich: if `2^{j-1} < n ≤ 2^j`, `n ∣ g` and `L = Nat.log 2 g` then
  `Nat.log 2 (g / n) ∈ {L - j, L - j + 1}` (for `1 ≤ j ≤ L`).
-/

namespace Erdos994

/-- The smooth number with exponent vector `e`. -/
def gval {d : ℕ} (p : Fin d → ℕ) (e : Fin d → ℕ) : ℕ := ∏ i, p i ^ e i

lemma gval_pos {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, 0 < p i) (e : Fin d → ℕ) : 0 < gval p e :=
  Finset.prod_pos fun i _ ↦ pow_pos (hp i) (e i)

lemma gval_add {d : ℕ} (p : Fin d → ℕ) (a b : Fin d → ℕ) :
    gval p (a + b) = gval p a * gval p b := by
  simp [gval, pow_add, Finset.prod_mul_distrib]

/-- The exponent vector of `n` with respect to the primes `p`. -/
def expVec {d : ℕ} (p : Fin d → ℕ) (n : ℕ) : Fin d → ℕ := fun i => n.factorization (p i)

/-- The multiplicity of a prime `q` in `gval p e`, as a sum over the indices `i` with
`p i = q`. -/
private lemma factorization_gval {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (e : Fin d → ℕ) (q : ℕ) :
    (gval p e).factorization q = ∑ i, if p i = q then e i else 0 := by
  rw [gval, Nat.factorization_prod fun i _ ↦ pow_ne_zero (e i) (hp i).ne_zero]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization,
    Finsupp.single_apply]
  by_cases h : p i = q <;> simp [h]

/-- The multiplicity of `p j` in `gval p e` is `e j`. -/
private lemma factorization_gval_self {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : Fin d → ℕ) (j : Fin d) :
    (gval p e).factorization (p j) = e j := by
  rw [factorization_gval hp e (p j)]
  simp [hinj.eq_iff]

/-- A prime outside the range of `p` does not divide `gval p e`. -/
private lemma factorization_gval_of_notMem {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (e : Fin d → ℕ) {q : ℕ} (hq : ∀ i, p i ≠ q) : (gval p e).factorization q = 0 := by
  rw [factorization_gval hp e q]
  exact Finset.sum_eq_zero fun i _ ↦ by simp [hq i]

/-- If every prime factor of `n` is among the `p i` (which are distinct primes), then
`n = gval p (expVec p n)`. -/
lemma gval_expVec {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {n : ℕ} (hn : 0 < n) (hcover : ∀ q, q.Prime → q ∣ n → ∃ i, p i = q) :
    gval p (expVec p n) = n := by
  have hg : gval p (expVec p n) ≠ 0 := (gval_pos (fun i ↦ (hp i).pos) _).ne'
  refine Nat.eq_of_factorization_eq hg hn.ne' fun q ↦ ?_
  by_cases hq : ∃ i, p i = q
  · obtain ⟨i, rfl⟩ := hq
    exact factorization_gval_self hp hinj _ i
  · simp only [not_exists] at hq
    rw [factorization_gval_of_notMem hp _ hq]
    rcases Nat.eq_zero_or_pos (n.factorization q) with h | h
    · exact h.symm
    have hqp : q.Prime := by
      by_contra hqp
      simp [Nat.factorization_eq_zero_of_not_prime n hqp] at h
    have hqd : q ∣ n := by
      by_contra hqd
      simp [Nat.factorization_eq_zero_of_not_dvd hqd] at h
    obtain ⟨i, hi⟩ := hcover q hqp hqd
    exact absurd hi (hq i)

/-- Every `n ≤ 2^J` is `p`-smooth with exponents `≤ J` when the `p i` cover all primes
`≤ 2^J`. -/
lemma expVec_le_of_le_pow {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    {J n : ℕ} (hn : n ≤ 2 ^ J) (i : Fin d) : expVec p n i ≤ J := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [expVec]
  have hdvd : p i ^ n.factorization (p i) ∣ n := Nat.ordProj_dvd n (p i)
  have h1 : (2 : ℕ) ^ n.factorization (p i) ≤ p i ^ n.factorization (p i) :=
    Nat.pow_le_pow_left (hp i).two_le _
  have h2 : p i ^ n.factorization (p i) ≤ n := Nat.le_of_dvd hn0 hdvd
  have h3 : (2 : ℕ) ^ n.factorization (p i) ≤ 2 ^ J := le_trans h1 (le_trans h2 hn)
  exact (Nat.pow_le_pow_iff_right (le_refl 2)).mp h3

lemma gval_injective {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : Function.Injective (gval p) := by
  intro a b hab
  funext i
  rw [← factorization_gval_self hp hinj a i, ← factorization_gval_self hp hinj b i, hab]

/-- Divisibility of `gval` corresponds to componentwise order of exponents. -/
lemma gval_dvd_gval_iff {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {a e : Fin d → ℕ} :
    gval p a ∣ gval p e ↔ a ≤ e := by
  have hpa : gval p a ≠ 0 := (gval_pos (fun i ↦ (hp i).pos) a).ne'
  have hpe : gval p e ≠ 0 := (gval_pos (fun i ↦ (hp i).pos) e).ne'
  constructor
  · intro h i
    have := ((Nat.factorization_le_iff_dvd hpa hpe).mpr h) (p i)
    rwa [factorization_gval_self hp hinj a i, factorization_gval_self hp hinj e i] at this
  · intro h
    refine ⟨gval p (e - a), ?_⟩
    rw [← gval_add]
    congr 1
    funext i
    have : a i ≤ e i := h i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega

/-- The `Nat.log 2` sandwich for the quotient by a dyadic-range divisor. -/
lemma log_div_mem {g n j : ℕ} (hg : 0 < g) (hn : n ∣ g) (hj : 1 ≤ j)
    (hlo : 2 ^ (j - 1) < n) (hhi : n ≤ 2 ^ j) (hjL : j ≤ Nat.log 2 g) :
    Nat.log 2 (g / n) = Nat.log 2 g - j ∨ Nat.log 2 (g / n) = Nat.log 2 g - j + 1 := by
  set L := Nat.log 2 g with hL
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlo
  have hgn : n * (g / n) = g := Nat.mul_div_cancel' hn
  have hm0 : 0 < g / n := Nat.div_pos (Nat.le_of_dvd hg hn) hn0
  have hlow : 2 ^ L ≤ g := Nat.pow_log_le_self 2 hg.ne'
  have hhigh : g < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) g
  have key1 : 2 ^ (L - j) ≤ g / n := by
    have h2 : (2 : ℕ) ^ j * 2 ^ (L - j) = 2 ^ L := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : n * 2 ^ (L - j) ≤ n * (g / n) := by
      rw [hgn]
      calc n * 2 ^ (L - j) ≤ 2 ^ j * 2 ^ (L - j) := Nat.mul_le_mul_right _ hhi
        _ = 2 ^ L := h2
        _ ≤ g := hlow
    exact Nat.le_of_mul_le_mul_left h3 hn0
  have key2 : g / n < 2 ^ (L - j + 2) := by
    have h2 : (2 : ℕ) ^ (j - 1) * 2 ^ (L - j + 2) = 2 ^ (L + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : 2 ^ (j - 1) * (g / n) < 2 ^ (j - 1) * 2 ^ (L - j + 2) := by
      rw [h2]
      calc 2 ^ (j - 1) * (g / n) < n * (g / n) := mul_lt_mul_of_pos_right hlo hm0
        _ = g := hgn
        _ < 2 ^ (L + 1) := hhigh
    exact Nat.lt_of_mul_lt_mul_left h3
  have hle1 : L - j ≤ Nat.log 2 (g / n) := Nat.le_log_of_pow_le (by norm_num) key1
  have hle2 : Nat.log 2 (g / n) < L - j + 2 := Nat.log_lt_of_lt_pow hm0.ne' key2
  omega

end Erdos994
