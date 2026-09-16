import Mathlib
import ErdosProblems.Erdos387.CongruenceCounting

/-!
# Local sieve residues with one fixed congruence

Fixing the shift modulo one squarefree factor leaves an independent local
choice at each prime of the complementary factor. All residues below are
canonical natural representatives; the result does not restrict the integer
whose residue will later be tested.
-/

namespace Erdos387Proof.ConstrainedSieveResidues

open Erdos387
open scoped BigOperators

/-- Explicit membership in the local assignment image. The local criterion
itself does not require the primes to exceed `k`. -/
theorem mem_localAssignmentResidues_iff {g k a : ℕ} (hg : Squarefree g) :
    a ∈ localAssignmentResidues g k ↔
      a < g ∧ ∀ p ∈ g.primeFactors, a % p < k := by
  classical
  constructor
  · intro ha
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨localAssignmentResidue_lt hg A, ?_⟩
    intro p hp
    let p' : ↑g.primeFactors := ⟨p, hp⟩
    calc
      localAssignmentResidue g k A % p = (A p' : ℕ) % p :=
        localAssignmentResidue_mod g k A p'
      _ ≤ (A p' : ℕ) := Nat.mod_le _ _
      _ < k := (A p').isLt
  · rintro ⟨ha, hlocal⟩
    let A : (p : ↑g.primeFactors) → Fin k :=
      fun p => ⟨a % (p : ℕ), hlocal p p.property⟩
    have hm : a ≡ localAssignmentResidue g k A [MOD g] := by
      have hmrad : a ≡ localAssignmentResidue g k A
          [MOD ∏ p ∈ g.primeFactors, p] := by
        apply (modEq_prod_primeFactors_iff g a (localAssignmentResidue g k A)).mpr
        intro p hp
        let p' : ↑g.primeFactors := ⟨p, hp⟩
        have hA : a ≡ (A p' : ℕ) [MOD p] := (Nat.mod_modEq a p).symm
        exact hA.trans (localAssignmentResidue_mod g k A p').symm
      simpa only [Nat.prod_primeFactors_of_squarefree hg] using hmrad
    have heq := Nat.mod_eq_of_modEq hm (localAssignmentResidue_lt hg A)
    rw [Nat.mod_eq_of_lt ha] at heq
    exact Finset.mem_image.mpr ⟨A, Finset.mem_univ _, heq.symm⟩

private theorem modEq_of_dvd {a b p m : ℕ} (hp : p ∣ m)
    (h : a ≡ b [MOD m]) : a ≡ b [MOD p] := by
  change a % m = b % m at h
  have := congrArg (fun n => n % p) h
  change a % p = b % p
  simpa only [Nat.mod_mod_of_dvd _ hp] using this

/-- Projection of an allowed residue to a squarefree divisor is allowed. -/
theorem mod_mem_localAssignmentResidues {g v k a : ℕ}
    (hg : Squarefree g) (hv : v ∣ g)
    (ha : a ∈ localAssignmentResidues g k) :
    a % v ∈ localAssignmentResidues v k := by
  have hvf : Squarefree v := hg.squarefree_of_dvd hv
  have hlocal := (mem_localAssignmentResidues_iff hg).mp ha
  apply (mem_localAssignmentResidues_iff hvf).mpr
  refine ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hvf.ne_zero), ?_⟩
  intro p hp
  have hpg : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr
    ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.dvd_of_mem_primeFactors hp).trans hv,
      hg.ne_zero⟩
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_primeFactors hp)]
  exact hlocal.2 p hpg

/-- Adjoining the fixed shift on the first factor preserves all local sieve
conditions on the product. -/
theorem simultaneousResidue_mem_localAssignmentResidues
    {u v k i a : ℕ} (huv : Squarefree (u * v))
    (hcop : Nat.Coprime u v) (hi : i < k)
    (ha : a ∈ localAssignmentResidues v k) :
    simultaneousResidue hcop i a ∈ localAssignmentResidues (u * v) k := by
  have hu : Squarefree u := huv.of_mul_left
  have hv : Squarefree v := huv.of_mul_right
  have halocal := (mem_localAssignmentResidues_iff hv).mp ha
  apply (mem_localAssignmentResidues_iff huv).mpr
  refine ⟨simultaneousResidue_lt hcop (Nat.pos_of_ne_zero hu.ne_zero)
    (Nat.pos_of_ne_zero hv.ne_zero) i a, ?_⟩
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hpu | hpv
  · have hm := modEq_of_dvd hpu (simultaneousResidue_mod_left hcop i a)
    exact (show simultaneousResidue hcop i a % p = i % p from hm).trans_lt
      ((Nat.mod_le i p).trans_lt hi)
  · have hpv' : p ∈ v.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hprime, hpv, hv.ne_zero⟩
    have hm := modEq_of_dvd hpv (simultaneousResidue_mod_right hcop i a)
    exact (show simultaneousResidue hcop i a % p = a % p from hm).trans_lt
      (halocal.2 p hpv')

/-- The constrained local residue set is exactly a CRT image of the
unconstrained local residue set on the complementary modulus. -/
theorem filter_modEq_eq_image {u v k i : ℕ} (huv : Squarefree (u * v))
    (hcop : Nat.Coprime u v) (hi : i < k) :
    ((localAssignmentResidues (u * v) k).filter (fun r => r ≡ i [MOD u])) =
      (localAssignmentResidues v k).image (simultaneousResidue hcop i) := by
  classical
  have hu : Squarefree u := huv.of_mul_left
  have hv : Squarefree v := huv.of_mul_right
  ext r
  constructor
  · intro hr
    obtain ⟨hr, hri⟩ := Finset.mem_filter.mp hr
    have hrlt := ((mem_localAssignmentResidues_iff huv).mp hr).1
    have hrv := mod_mem_localAssignmentResidues huv (dvd_mul_left v u) hr
    refine Finset.mem_image.mpr ⟨r % v, hrv, ?_⟩
    have hm : r ≡ simultaneousResidue hcop i (r % v) [MOD u * v] :=
      Nat.chineseRemainder_modEq_unique hcop hri (Nat.mod_modEq r v).symm
    have heq := Nat.mod_eq_of_modEq hm
      (simultaneousResidue_lt hcop (Nat.pos_of_ne_zero hu.ne_zero)
        (Nat.pos_of_ne_zero hv.ne_zero) i (r % v))
    rwa [Nat.mod_eq_of_lt hrlt, eq_comm] at heq
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_filter.mpr
      ⟨simultaneousResidue_mem_localAssignmentResidues huv hcop hi ha,
        simultaneousResidue_mod_left hcop i a⟩

/-- CRT with the first coordinate fixed is injective on canonical local
residues on the second factor. -/
theorem simultaneousResidue_injOn_localAssignmentResidues
    {u v k i : ℕ} (hv : Squarefree v) (hcop : Nat.Coprime u v) :
    Set.InjOn (simultaneousResidue hcop i)
      (↑(localAssignmentResidues v k) : Set ℕ) := by
  intro a ha b hb heq
  have hal := ((mem_localAssignmentResidues_iff hv).mp ha).1
  have hbl := ((mem_localAssignmentResidues_iff hv).mp hb).1
  have hma := Nat.mod_eq_of_modEq (simultaneousResidue_mod_right hcop i a) hal
  have hmb := Nat.mod_eq_of_modEq (simultaneousResidue_mod_right hcop i b) hbl
  rw [heq] at hma
  exact hma.symm.trans hmb

/-- Exact constrained sieve multiplicity. Only the complementary prime
factors need to exceed `k` for this counting statement. -/
theorem card_filter_modEq {u v k i : ℕ} (huv : Squarefree (u * v))
    (hcop : Nat.Coprime u v) (hi : i < k)
    (hlarge : ∀ p ∈ v.primeFactors, k < p) :
    ((localAssignmentResidues (u * v) k).filter (fun r => r ≡ i [MOD u])).card =
      k ^ v.primeFactors.card := by
  rw [filter_modEq_eq_image huv hcop hi,
    Finset.card_image_of_injOn
      (simultaneousResidue_injOn_localAssignmentResidues huv.of_mul_right hcop),
    card_localAssignmentResidues hlarge]

/-- Product-form interface with coprimality derived from squarefreeness. -/
theorem card_filter_modEq_of_eq_mul {g u v k i : ℕ}
    (hg : Squarefree g) (hguv : g = u * v) (hi : i < k)
    (hlarge : ∀ p ∈ v.primeFactors, k < p) :
    ((localAssignmentResidues g k).filter (fun r => r ≡ i [MOD u])).card =
      k ^ v.primeFactors.card := by
  subst g
  exact card_filter_modEq hg (Nat.coprime_of_squarefree_mul hg) hi hlarge

end Erdos387Proof.ConstrainedSieveResidues
