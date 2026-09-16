import Mathlib

/-!
# Erdős Problem #879: the elementary upper bound `G(n) < H(n)` (Erdős–van Lint)

Call `S ⊆ {1, …, n}` admissible if its elements are pairwise coprime, let `G(n)` be the largest
sum of an admissible set, and let `H(n) = ∑_{p ≤ n} p + n · π(√n)`.  Erdős asked whether
`G(n) > H(n) − n^{1+o(1)}` (OPEN) and about the structure of the extremal sets (OPEN).  Erdős and
van Lint proved `H(n) − n^{3/2−o(1)} < G(n) < H(n)` and `(H(n) − G(n))/n → ∞`.  This file proves
the elementary half `G(n) < H(n)` for all `n ≥ 4`.

Convention.  The problem page writes `H(n) = ∑_{p<n} p + n π(n^{1/2})`; with a strict `p < n` the
inequality `G(n) < H(n)` fails for every prime `n ≥ 5` (the primes up to `n` already form an
admissible set of sum `∑_{p≤n} p`), while the Erdős–van Lint asymptotics are unaffected by the
difference `n` between the two conventions.  We therefore use `∑_{p ≤ n} p` (see
`ref/convention-check.md`); nothing beyond this elementary bound is claimed.

Proof.  In an admissible `S`, distinct elements `> 1` have distinct least prime factors.  An
element `a ≤ n` whose least prime factor exceeds `√n` is itself prime, so these elements sum to at
most `∑_{√n < p ≤ n} p`; the elements with least prime factor `≤ √n` number at most `π(√n)` and are
each `≤ n`.  With the element `1`, `G(n) ≤ 1 + ∑_{√n<p≤n} p + n π(√n) = H(n) + 1 − ∑_{p≤√n} p < H(n)`
since `2 ≤ √n` for `n ≥ 4`.
-/

open Finset

/-- A finite set of naturals is admissible if its elements are pairwise coprime. -/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

instance (S : Finset ℕ) : Decidable (IsAdmissible S) := by
  unfold IsAdmissible; infer_instance

/-- `G n` is the largest sum of an admissible subset of `{1, …, n}`. -/
def G (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter IsAdmissible).sup fun S ↦ ∑ a ∈ S, a

/-- `H n = ∑_{p ≤ n} p + n · π(⌊√n⌋)`, with `π` Mathlib's `Nat.primeCounting`. -/
def H (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, p + n * Nat.primeCounting (Nat.sqrt n)

/-- In an admissible set, distinct elements other than `1` have distinct least prime factors. -/
lemma minFac_injOn_erase_one {S : Finset ℕ} (hadm : IsAdmissible S) :
    Set.InjOn Nat.minFac ((S.erase 1 : Finset ℕ) : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_erase] at ha hb
  obtain ⟨ha1, haS⟩ := ha
  obtain ⟨hb1, hbS⟩ := hb
  by_contra hne
  have hco : Nat.Coprime a b := hadm a haS b hbS hne
  have hpa : Nat.minFac a ∣ a := Nat.minFac_dvd a
  have hpb : Nat.minFac a ∣ b := by rw [hab]; exact Nat.minFac_dvd b
  have hd : Nat.minFac a ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [Nat.Coprime] at hco
  rw [hco] at hd
  exact (Nat.minFac_prime ha1).one_lt.ne' (Nat.dvd_one.mp hd)

/-- An element of `{1, …, n}` whose least prime factor exceeds `√n` is prime. -/
lemma prime_of_sqrt_lt_minFac {n a : ℕ} (ha1 : 1 ≤ a) (han : a ≤ n)
    (h : Nat.sqrt n < Nat.minFac a) : Nat.Prime a := by
  by_contra hp
  have h2 : Nat.minFac a ^ 2 ≤ a := Nat.minFac_sq_le_self ha1 hp
  have h3 : Nat.minFac a ≤ Nat.sqrt a := Nat.le_sqrt'.mpr h2
  have h4 : Nat.sqrt a ≤ Nat.sqrt n := Nat.sqrt_le_sqrt han
  omega

/-- Sanity values: `G 4 = 8 = 4 + 3 + 1`, `H 4 = 2 + 3 + 4 · 1 = 9`. -/
theorem G_H_eval : G 4 = 8 ∧ H 4 = 9 := by
  refine ⟨by decide, ?_⟩
  have hs : Nat.sqrt 4 = 2 := Nat.sqrt_eq' 2
  show ∑ p ∈ (Finset.Icc 1 4).filter Nat.Prime, p + 4 * Nat.primeCounting (Nat.sqrt 4) = 9
  rw [hs]
  decide

/-- **Erdős–van Lint, elementary upper bound.**  Every admissible `S ⊆ {1, …, n}` with `n ≥ 4` has
`∑ S < H n`. -/
theorem sum_lt_H_of_isAdmissible (n : ℕ) (hn : 4 ≤ n) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n)
    (hadm : IsAdmissible S) : ∑ a ∈ S, a < H n := by
  set r := Nat.sqrt n with hr
  set S' := S.erase 1 with hS'
  have hmem : ∀ a ∈ S', 1 ≤ a ∧ a ≤ n ∧ a ≠ 1 := by
    intro a ha
    rw [hS', Finset.mem_erase] at ha
    have h := Finset.mem_Icc.mp (hS ha.2)
    exact ⟨h.1, h.2, ha.1⟩
  have hr2 : 2 ≤ r := by rw [hr]; exact Nat.le_sqrt.mpr (by omega)
  set Pn := (Finset.Icc 1 n).filter Nat.Prime with hPn
  -- Split `S.erase 1` according to whether the least prime factor exceeds `√n`.
  have hsplit : ∑ a ∈ S'.filter (fun a => r < Nat.minFac a), a
      + ∑ a ∈ S'.filter (fun a => ¬ r < Nat.minFac a), a = ∑ a ∈ S', a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hpsplit : ∑ p ∈ Pn.filter (fun p => r < p), p
      + ∑ p ∈ Pn.filter (fun p => ¬ r < p), p = ∑ p ∈ Pn, p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  -- Elements with large least prime factor are primes in `(√n, n]`.
  have hbig : ∑ a ∈ S'.filter (fun a => r < Nat.minFac a), a
      ≤ ∑ p ∈ Pn.filter (fun p => r < p), p := by
    apply Finset.sum_le_sum_of_subset
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haS', hlt⟩ := ha
    obtain ⟨h1, h2, h3⟩ := hmem a haS'
    have hp : Nat.Prime a := prime_of_sqrt_lt_minFac h1 h2 hlt
    refine ⟨?_, ?_⟩
    · rw [hPn, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hp⟩
    · rwa [hp.minFac_eq] at hlt
  -- Elements with small least prime factor are at most `π(√n)` many, each at most `n`.
  have hcard : (S'.filter (fun a => ¬ r < Nat.minFac a)).card ≤ Nat.primeCounting r := by
    have hcnt : Nat.primeCounting r = ((Finset.range (r + 1)).filter Nat.Prime).card := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [hcnt]
    apply Finset.card_le_card_of_injOn Nat.minFac
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      obtain ⟨haS', hle⟩ := ha
      obtain ⟨h1, h2, h3⟩ := hmem a haS'
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.minFac_prime h3⟩
    · exact (minFac_injOn_erase_one hadm).mono
        (by rw [hS']; exact_mod_cast Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hsmall : ∑ a ∈ S'.filter (fun a => ¬ r < Nat.minFac a), a ≤ n * Nat.primeCounting r := by
    calc ∑ a ∈ S'.filter (fun a => ¬ r < Nat.minFac a), a
        ≤ (S'.filter (fun a => ¬ r < Nat.minFac a)).card • n :=
          Finset.sum_le_card_nsmul _ _ _ (fun a ha => (hmem a (Finset.mem_of_mem_filter a ha)).2.1)
      _ = (S'.filter (fun a => ¬ r < Nat.minFac a)).card * n := smul_eq_mul _ _
      _ ≤ Nat.primeCounting r * n := Nat.mul_le_mul_right _ hcard
      _ = n * Nat.primeCounting r := Nat.mul_comm _ _
  -- The element `1` contributes at most `1`.
  have hone : ∑ a ∈ S, a ≤ ∑ a ∈ S', a + 1 := by
    by_cases h1 : (1 : ℕ) ∈ S
    · have he := Finset.sum_erase_add S (fun a => a) h1
      rw [hS']
      omega
    · rw [hS', Finset.erase_eq_of_notMem h1]
      omega
  -- The prime `2` is one of the primes at most `√n`, since `n ≥ 4`.
  have h2le : 2 ≤ ∑ p ∈ Pn.filter (fun p => ¬ r < p), p := by
    have h2mem : (2 : ℕ) ∈ Pn.filter (fun p => ¬ r < p) := by
      rw [Finset.mem_filter, hPn, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨by norm_num, by omega⟩, Nat.prime_two⟩, by omega⟩
    exact Finset.single_le_sum (f := fun p => p) (fun i _ => Nat.zero_le i) h2mem
  have hH : H n = ∑ p ∈ Pn, p + n * Nat.primeCounting r := by rw [hPn, hr]; rfl
  obtain ⟨N, hN⟩ : ∃ N, N = n * Nat.primeCounting r := ⟨_, rfl⟩
  rw [← hN] at hsmall hH
  omega

/-- **Erdős #879, the elementary upper bound.**  `G(n) < H(n)` for every `n ≥ 4`. -/
theorem erdos_879_upper_bound (n : ℕ) (hn : 4 ≤ n) : G n < H n := by
  have hpos : (⊥ : ℕ) < H n := by
    have h := sum_lt_H_of_isAdmissible n hn ∅ (Finset.empty_subset _) (by simp [IsAdmissible])
    simpa using h
  show ((Finset.Icc 1 n).powerset.filter IsAdmissible).sup (fun S ↦ ∑ a ∈ S, a) < H n
  rw [Finset.sup_lt_iff hpos]
  intro S hSmem
  rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
  exact sum_lt_H_of_isAdmissible n hn S hSmem.1 hSmem.2

/-- The same bound as a closed statement: there is no `n ≥ 4` with `H n ≤ G n`.  The lower bound
`H(n) − n^{3/2−o(1)} < G(n)`, the question `G(n) > H(n) − n^{1+o(1)}` and the structure of the
extremal sets are not addressed. -/
theorem erdos_879_upper_bound_closed : ¬ ∃ n : ℕ, 4 ≤ n ∧ H n ≤ G n := by
  rintro ⟨n, hn, h⟩
  exact absurd (erdos_879_upper_bound n hn) (not_lt.mpr h)
