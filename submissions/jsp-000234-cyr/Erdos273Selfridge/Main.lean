import Mathlib

/-!
# Erdős Problem #273: a covering system with moduli `p − 1`, `p ≥ 3` prime (Selfridge)

Erdős asked whether there is a covering system of the integers all of whose moduli are of the
form `p − 1` for primes `p ≥ 5` (OPEN).  The problem page records that Selfridge found an example
using divisors of `360` if `p = 3` is allowed.  This file certifies such a system, in the exact
shape of the formal-conjectures statement `Erdos273.erdos_273.variants.three`
(`answer(True) ↔ ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
c.moduli i = Ideal.span {↑(p − 1)}`, tagged "research solved" with `sorry`): the twelve congruence
classes `(modulus, residue)` = `(2,0), (4,1), (6,3), (10,7), (12,11), (18,1), (30,1), (36,7),
(40,23), (60,19), (72,67), (180,175)`, whose moduli `p − 1` come from the primes
`3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181`, are pairwise distinct and cover every residue
modulo `360`.  The question for `p ≥ 5` is not addressed.

The structures `CoveringSystem` and `StrictCoveringSystem` are copied verbatim from
`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`.
-/

open scoped Pointwise

/-- A covering system of a commutative semiring `R` is a finite collection of congruence relations
such that every element satisfies at least one of the relations (formal-conjectures definition). -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/-- A covering system is strict if all the congruence relations are taken modulo a different
ideal (formal-conjectures definition). -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

/-- The twelve moduli `p − 1` of Selfridge's system. -/
def selfridgeModulus : Fin 12 → ℕ := ![2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180]

/-- The corresponding residues. -/
def selfridgeResidue : Fin 12 → ℕ := ![0, 1, 3, 7, 11, 1, 1, 7, 23, 19, 67, 175]

/-- The primes `p` with `p − 1 = selfridgeModulus i`. -/
def selfridgePrime : Fin 12 → ℕ := ![3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181]

section Selfridge

set_option maxRecDepth 10000

/-- Every modulus divides `360`, so the whole system only depends on `n % 360`. -/
private theorem selfridgeModulus_dvd (i : Fin 12) : selfridgeModulus i ∣ 360 := by
  revert i
  decide

/-- Every modulus is nonzero. -/
private theorem selfridgeModulus_ne_zero (i : Fin 12) : selfridgeModulus i ≠ 0 := by
  revert i
  decide

/-- No modulus equals `1`. -/
private theorem selfridgeModulus_ne_one (i : Fin 12) : selfridgeModulus i ≠ 1 := by
  revert i
  decide

/-- The twelve moduli are pairwise distinct. -/
private theorem selfridgeModulus_injective : Function.Injective selfridgeModulus := by
  have h : ∀ i j : Fin 12, selfridgeModulus i = selfridgeModulus j → i = j := by decide
  exact fun i j hij => h i j hij

/-- The exhaustive check that the twelve classes cover every residue modulo `360`. -/
private theorem selfridge_covers_lt_360 (m : ℕ) (hm : m < 360) :
    ∃ i, m % selfridgeModulus i = selfridgeResidue i := by
  revert m
  decide

end Selfridge

/-- Every natural number lies in one of the twelve classes. -/
theorem selfridge_covers (n : ℕ) : ∃ i, n % selfridgeModulus i = selfridgeResidue i := by
  obtain ⟨i, hi⟩ := selfridge_covers_lt_360 (n % 360) (Nat.mod_lt _ (by norm_num))
  refine ⟨i, ?_⟩
  rwa [Nat.mod_mod_of_dvd n (selfridgeModulus_dvd i)] at hi

/-- The twelve congruence classes, as subsets of `ℕ`, cover `ℕ`. -/
private theorem selfridge_unionCovers :
    ⋃ i, ({selfridgeResidue i} : Set ℕ) +
        ((Ideal.span {selfridgeModulus i} : Ideal ℕ) : Set ℕ) = @Set.univ ℕ := by
  refine Set.eq_univ_of_forall fun n => ?_
  obtain ⟨i, hi⟩ := selfridge_covers n
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hn : selfridgeResidue i + selfridgeModulus i * (n / selfridgeModulus i) = n := by
    have h := Nat.mod_add_div n (selfridgeModulus i)
    rwa [hi] at h
  rw [← hn]
  exact Set.add_mem_add rfl
    (Ideal.mem_span_singleton.mpr ⟨n / selfridgeModulus i, rfl⟩)

/-- Selfridge's covering system as a `StrictCoveringSystem ℕ`. -/
noncomputable def selfridgeSystem : StrictCoveringSystem ℕ where
  ι := Fin 12
  residue := selfridgeResidue
  moduli i := Ideal.span {selfridgeModulus i}
  unionCovers := selfridge_unionCovers
  ne_bot i := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact selfridgeModulus_ne_zero i
  ne_top i := by
    rw [Ne, Ideal.span_singleton_eq_top, Nat.isUnit_iff]
    exact selfridgeModulus_ne_one i
  injective_moduli := by
    intro i j hij
    have h : Ideal.span {selfridgeModulus i} = Ideal.span {selfridgeModulus j} := hij
    have hij' : selfridgeModulus j ∈ Ideal.span {selfridgeModulus i} := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    have hji' : selfridgeModulus i ∈ Ideal.span {selfridgeModulus j} := by
      rw [← h]; exact Ideal.mem_span_singleton_self _
    exact selfridgeModulus_injective
      (Nat.dvd_antisymm (Ideal.mem_span_singleton.mp hij') (Ideal.mem_span_singleton.mp hji'))

/-- Each `selfridgePrime i` is prime. -/
private theorem selfridgePrime_prime (i : Fin 12) : (selfridgePrime i).Prime := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have h19 : Nat.Prime 19 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h41 : Nat.Prime 41 := by norm_num
  have h61 : Nat.Prime 61 := by norm_num
  have h73 : Nat.Prime 73 := by norm_num
  have h181 : Nat.Prime 181 := by norm_num
  fin_cases i
  · exact h3
  · exact h5
  · exact h7
  · exact h11
  · exact h13
  · exact h19
  · exact h31
  · exact h37
  · exact h41
  · exact h61
  · exact h73
  · exact h181

/-- Each `selfridgePrime i` is at least `3`. -/
private theorem selfridgePrime_ge_three (i : Fin 12) : 3 ≤ selfridgePrime i := by
  revert i
  decide

/-- Each `selfridgePrime i` is one more than the corresponding modulus. -/
private theorem selfridgePrime_sub_one (i : Fin 12) :
    selfridgePrime i - 1 = selfridgeModulus i := by
  revert i
  decide

/-- The moduli of `selfridgeSystem` are the ideals `(p − 1)` for primes `p ≥ 3`. -/
theorem selfridgeSystem_moduli :
    ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧ selfridgeSystem.moduli i = Ideal.span {(↑(p - 1) : ℕ)} := by
  intro i
  refine ⟨selfridgePrime i, selfridgePrime_prime i, selfridgePrime_ge_three i, ?_⟩
  show Ideal.span {selfridgeModulus i} = Ideal.span {(↑(selfridgePrime i - 1) : ℕ)}
  rw [selfridgePrime_sub_one i]

/-- **Erdős #273 with `p = 3` allowed (Selfridge).**  There is a strict covering system of `ℕ`
all of whose moduli are `p − 1` for primes `p ≥ 3`; exactly the `answer(True)` content of the
formal-conjectures statement `erdos_273.variants.three`.  The case `p ≥ 5` is open and not
claimed. -/
theorem erdos_273_three :
    ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧ c.moduli i = Ideal.span {↑(p - 1)} :=
  ⟨selfridgeSystem, selfridgeSystem_moduli⟩
