import Mathlib

/-!
# Erdős problem #931 — the two explicit examples stated on the problem page

Erdős problem #931 asks: *let `k₁ ≥ k₂ ≥ 3`; are there only finitely many `n₂ ≥ n₁ + k₁` such that
`∏_{1 ≤ i ≤ k₁} (n₁ + i)` and `∏_{1 ≤ j ≤ k₂} (n₂ + j)` have the same prime factors?*

That finiteness question is **open** and nothing here claims it.  This file formalises only the two
explicit examples recorded on the problem page:

* Tijdeman's example `19 · 20 · 21 · 22` and `54 · 55 · 56 · 57`
  (`n₁ = 18`, `k₁ = 4`, `n₂ = 53`, `k₂ = 4`), both with prime factors `{2, 3, 5, 7, 11, 19}`;
* AlphaProof's example `10! = 2⁸·3⁴·5²·7` and `14 · 15 · 16 = 2⁵·3·5·7`
  (`n₁ = 0`, `k₁ = 10`, `n₂ = 13`, `k₂ = 3`), both with prime factors `{2, 3, 5, 7}`.

The latter refutes, as literally stated, Erdős's guess that the same prime factors should force
`n₂ > 2(n₁ + k₁)`: here `n₂ = 13 ≤ 20 = 2(n₁ + k₁)`.
-/

namespace Erdos931

/-- `∏_{1 ≤ i ≤ k} (n + i)`, the product of the `k` consecutive integers `n+1, …, n+k` -/
def consProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- the two blocks `n₁+1..n₁+k₁` and `n₂+1..n₂+k₂` have products with the same set of prime
factors -/
def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  (consProd n₁ k₁).primeFactors = (consProd n₂ k₂).primeFactors

/-! ### Private arithmetic helpers -/

/-- peeling a prime power off the front of an explicit factorisation -/
private lemma primeFactors_pow_mul {p a k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (ha : a ≠ 0) :
    (p ^ k * a).primeFactors = insert p a.primeFactors := by
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.pos.ne') ha, Nat.primeFactors_pow _ hk,
    hp.primeFactors, Finset.singleton_union]

/-- peeling a single prime off the front of an explicit factorisation -/
private lemma primeFactors_prime_mul {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    (p * a).primeFactors = insert p a.primeFactors := by
  rw [Nat.primeFactors_mul hp.pos.ne' ha, hp.primeFactors, Finset.singleton_union]

/-- `19 · 20 · 21 · 22 = 2³ · 3 · 5 · 7 · 11 · 19` -/
private lemma primeFactors_175560 : (175560 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19} := by
  have h : (175560 : ℕ) = 2 ^ 3 * (3 * (5 * (7 * (11 * 19)))) := by norm_num
  rw [h, primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]

/-- `54 · 55 · 56 · 57 = 2⁴ · 3⁴ · 5 · 7 · 11 · 19` -/
private lemma primeFactors_9480240 : (9480240 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19} := by
  have h : (9480240 : ℕ) = 2 ^ 4 * (3 ^ 4 * (5 * (7 * (11 * 19)))) := by norm_num
  rw [h, primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]

/-- `10! = 2⁸ · 3⁴ · 5² · 7` -/
private lemma primeFactors_3628800 : (3628800 : ℕ).primeFactors = {2, 3, 5, 7} := by
  have h : (3628800 : ℕ) = 2 ^ 8 * (3 ^ 4 * (5 ^ 2 * 7)) := by norm_num
  rw [h, primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]

/-- `14 · 15 · 16 = 2⁵ · 3 · 5 · 7` -/
private lemma primeFactors_3360 : (3360 : ℕ).primeFactors = {2, 3, 5, 7} := by
  have h : (3360 : ℕ) = 2 ^ 5 * (3 * (5 * 7)) := by norm_num
  rw [h, primeFactors_pow_mul (by norm_num) (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    primeFactors_prime_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]

private lemma consProd_18_4_eq : consProd 18 4 = 175560 := by decide
private lemma consProd_53_4_eq : consProd 53 4 = 9480240 := by decide
private lemma consProd_0_10_eq : consProd 0 10 = 3628800 := by decide
private lemma consProd_13_3_eq : consProd 13 3 = 3360 := by decide

/-! ### Tijdeman's example -/

theorem consProd_tijdeman₁ : consProd 18 4 = 19 * 20 * 21 * 22 := by
  rw [consProd_18_4_eq]

theorem consProd_tijdeman₂ : consProd 53 4 = 54 * 55 * 56 * 57 := by
  rw [consProd_53_4_eq]

theorem tijdeman_primeFactors :
    (consProd 18 4).primeFactors = {2, 3, 5, 7, 11, 19} ∧
      (consProd 53 4).primeFactors = {2, 3, 5, 7, 11, 19} :=
  ⟨by rw [consProd_18_4_eq]; exact primeFactors_175560,
   by rw [consProd_53_4_eq]; exact primeFactors_9480240⟩

/-- Tijdeman's example, in the page's parameters: k₁ = k₂ = 4 ≥ 3 and n₂ = 53 ≥ n₁ + k₁ = 22 -/
theorem tijdeman : SamePrimeFactors 18 4 53 4 ∧ 3 ≤ 4 ∧ 18 + 4 ≤ 53 :=
  ⟨tijdeman_primeFactors.1.trans tijdeman_primeFactors.2.symm, by norm_num, by norm_num⟩

/-! ### AlphaProof's example -/

theorem consProd_alphaproof₁ : consProd 0 10 = Nat.factorial 10 := by
  decide

theorem consProd_alphaproof₂ : consProd 13 3 = 14 * 15 * 16 := by
  rw [consProd_13_3_eq]

theorem alphaproof_primeFactors :
    (consProd 0 10).primeFactors = {2, 3, 5, 7} ∧ (consProd 13 3).primeFactors = {2, 3, 5, 7} :=
  ⟨by rw [consProd_0_10_eq]; exact primeFactors_3628800,
   by rw [consProd_13_3_eq]; exact primeFactors_3360⟩

/-- AlphaProof's example: k₁ = 10 ≥ k₂ = 3 ≥ 3, n₂ = 13 ≥ n₁ + k₁ = 10, same prime factors, yet
n₂ ≤ 2(n₁ + k₁) -/
theorem alphaproof :
    SamePrimeFactors 0 10 13 3 ∧ 3 ≤ 3 ∧ 3 ≤ 10 ∧ 0 + 10 ≤ 13 ∧ 13 ≤ 2 * (0 + 10) :=
  ⟨alphaproof_primeFactors.1.trans alphaproof_primeFactors.2.symm, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Erdős's guess "same prime factors ⇒ n₂ > 2(n₁ + k₁)" is false as literally stated -/
theorem erdos_guess_false :
    ¬ ∀ n₁ k₁ n₂ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ → n₁ + k₁ ≤ n₂ → SamePrimeFactors n₁ k₁ n₂ k₂ →
      2 * (n₁ + k₁) < n₂ := by
  intro h
  have := h 0 10 13 3 (by norm_num) (by norm_num) (by norm_num) alphaproof.1
  omega

end Erdos931

/-! ### Kernel dependency audit -/

#print axioms Erdos931.consProd_tijdeman₁
#print axioms Erdos931.consProd_tijdeman₂
#print axioms Erdos931.tijdeman_primeFactors
#print axioms Erdos931.tijdeman
#print axioms Erdos931.consProd_alphaproof₁
#print axioms Erdos931.consProd_alphaproof₂
#print axioms Erdos931.alphaproof_primeFactors
#print axioms Erdos931.alphaproof
#print axioms Erdos931.erdos_guess_false
