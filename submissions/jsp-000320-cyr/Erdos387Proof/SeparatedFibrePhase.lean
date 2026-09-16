import Erdos387Proof.SeparatedRetainedResidue
import Erdos387Proof.SeparatedBuchstabDecomposition

/-! Exact removal of the last arithmetic masks on a fixed separated fibre.
The only removed filter is the unit filter already present in seq. Roughness
and the original sharp product window remain explicit. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedFibrePhase
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open SeparatedCertificateEnlargement SeparatedPrimeFibre
open SeparatedBuchstabDecomposition MaskedReciprocalPhase SeparatedRetainedResidue
open scoped BigOperators

variable {B K X z y medium second gap g : ℕ} {S : BPZSection6Input B K}
variable {i : Fin S.k}

/-- For a rough variable, adding the actual small-prime sieve product to
the fixed modulus adds no new unit restriction. -/
theorem unit_iff_base_coprime (a : SplitCertificate S X) (q : ℕ)
    (hzy : z ≤ y) (hg : g≠0) (hsupport : ∀ p∈g.primeFactors,p < z)
    (hrough : IsZRough y q)
    [NeZero (refinementModulus S*a.1.val.otherValue i*g*a.2.1)] :
    IsUnit (q : ZMod (refinementModulus S*a.1.val.otherValue i*g*a.2.1)) ↔
      q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1) := by
  rw [ZMod.isUnit_iff_coprime]
  have hqg := (ConvenientPhaseData.coprime_of_support_rough hg hsupport
    (fun p hp hpz =>  hrough p hp (hpz.trans_le hzy))).symm
  have horder : refinementModulus S*a.1.val.otherValue i*g*a.2.1 =
      (refinementModulus S*a.1.val.otherValue i*a.2.1)*g := by ring
  rw [horder]
  constructor
  · intro h
    exact h.of_dvd_right (dvd_mul_right _ _)
  · intro h
    exact h.mul_right hqg

/-- Exact equality with the full dyadic rough phase, preserving any scalar
weight on the varying coordinate and the sharp original product window. -/
theorem sum_domain_eq_whole_rough (a : SplitCertificate S X)
    (ha : a∈certificates S X z y medium second gap i) (hB : 0 < B)
    (hzy : z ≤ y) (hg : g≠0) (hsupport : ∀ p∈g.primeFactors,p < z)
    (c : ℤ) (w : ℕ→ℂ) :
    let N := refinementModulus S*a.1.val.otherValue i*g*a.2.1
    letI : NeZero N := ⟨Nat.ne_of_gt (Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (refinementModulus_pos S) (a.1.val.otherValue_pos i))
        (Nat.pos_of_ne_zero hg)) (by have hb := split_bounds ha; omega))⟩
    (∑ q∈domain (y:=y) (medium:=medium) (i:=i) a,
      w q*seq N c 0 [] (q : ℤ)) =
    ∑ q∈Finset.Ioc (blockUpper a.2.2/2) (blockUpper a.2.2),
      if lower a i < q ∧ q ≤ upper a i medium then
        w q*(roughIndicator y q*seq N c 0 [] (q : ℤ)) else 0 := by
  classical
  have hb := split_bounds ha
  let : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  let : NeZero (a.1.val.otherValue i) := ⟨(a.1.val.otherValue_pos i).ne'⟩
  let : NeZero g := ⟨hg⟩
  let : NeZero a.2.1 := ⟨by omega⟩
  dsimp only
  have hdom : domain (y:=y) (medium:=medium) (i:=i) a =
      (Finset.Ioc (blockUpper a.2.2/2) (blockUpper a.2.2)).filter (fun q => 
        IsZRough y q ∧ q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1) ∧
          lower a i < q ∧ q ≤ upper a i medium) := by
    ext q
    rw [mem_domain_iff_sharp a ha hB,Finset.mem_filter]
  rw [hdom,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hcut : lower a i < q ∧ q ≤ upper a i medium
  · by_cases hr : IsZRough y q
    · have hu := unit_iff_base_coprime (i:=i) a q hzy hg hsupport hr
      by_cases hc : q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1)
      · rw [if_pos ⟨hr,hc,hcut⟩,if_pos hcut]
        simp only [roughIndicator,if_pos hr,one_mul]
      · have hnunit := mt hu.mp hc
        have hzero : seq (refinementModulus S*a.1.val.otherValue i*g*a.2.1)
            c 0 [] (q : ℤ)=0 := by
          simp only [seq,good,zero_add,Int.cast_natCast,if_neg hnunit]
        simp only [hc,and_false,false_and,if_false,hcut,and_self,if_true,
          roughIndicator,hr,hzero,mul_zero]
    · simp only [hr,false_and,if_false,roughIndicator,hcut,and_self,if_true,zero_mul,mul_zero]
  · have hn : ¬(IsZRough y q ∧
        q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1) ∧
          lower a i < q ∧ q ≤ upper a i medium) := fun h =>  hcut h.2.2
    simp only [if_neg hn,if_neg hcut]

theorem certificate_mem_of_mem_fibre {a t : SplitCertificate S X}
    (ht : t∈fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a) :
    t∈certificates S X z y medium second gap i := by
  classical
  exact (Finset.mem_filter.mp ht).1

theorem actualTerm_eq_fixed (a t : SplitCertificate S X)
    (ha : a∈certificates S X z y medium second gap i)
    (ht : t∈certificates S X z y medium second gap i) (hkey : SameAnchorKey i t a)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors,max (2*S.k) 3 ≤ p ∧ p < z)
    (b : ℕ) (hb : b < g) (h : ℤ) :
    let hd := sieve_data ha hg hsupport
    let N := refinementModulus S*a.1.val.otherValue i*g*a.2.1
    letI : NeZero N := ⟨Nat.ne_of_gt (Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (refinementModulus_pos S) (a.1.val.otherValue_pos i))
        (Nat.pos_of_ne_zero hg.ne_zero)) (by have hb := split_bounds ha; omega))⟩
    actualTerm ht hg hsupport b h =
      FourierVariation.tentWeight X h (-i.val) (N*t.2.2 : ℕ)⁻¹ *
        seq N ((-h)*((retainedResidue a i g b hd.1 hd.2.1 : ℤ)-i.val)) 0 [] (t.2.2 : ℤ) := by
  have hD := otherValue_eq_of_key hkey
  have hdA := sieve_data ha hg hsupport
  have hdT := sieve_data ht hg hsupport
  have hgamma := retainedResidue_eq_of_key a t hkey b hdA.1 hdT.1 hdA.2.1 hdT.2.1
  have hh := certificate_fourierSummand_eq_single ht hg hsupport b hb h
  simpa only [actualTerm,hgamma,hD,hkey.2.1] using hh

/-- The actual original certificate Fourier sum on one fixed key equals the
whole-interval weighted rough phase. Every original mask is either explicit
or exactly the unit mask in seq; the fixed residue still includes r. -/
theorem sum_actualTerm_eq_whole_rough (a : SplitCertificate S X)
    (ha : a∈certificates S X z y medium second gap i) (hB : 0 < B) (hzy : z ≤ y)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors,max (2*S.k) 3 ≤ p ∧ p < z)
    (b : ℕ) (hb : b < g) (h : ℤ) :
    let hd := sieve_data ha hg hsupport
    let N := refinementModulus S*a.1.val.otherValue i*g*a.2.1
    letI : NeZero N := ⟨Nat.ne_of_gt (Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (refinementModulus_pos S) (a.1.val.otherValue_pos i))
        (Nat.pos_of_ne_zero hg.ne_zero)) (by have hb := split_bounds ha; omega))⟩
    (∑ t∈(fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a).attach,
      actualTerm (certificate_mem_of_mem_fibre t.property) hg hsupport b h) =
    ∑ q∈Finset.Ioc (blockUpper a.2.2/2) (blockUpper a.2.2),
      if lower a i < q ∧ q ≤ upper a i medium then
        FourierVariation.tentWeight X h (-i.val) (N*q : ℕ)⁻¹ *
          (roughIndicator y q*seq N ((-h)*
            ((retainedResidue a i g b hd.1 hd.2.1 : ℤ)-i.val)) 0 [] (q : ℤ)) else 0 := by
  classical
  have hba := split_bounds ha
  let : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  let : NeZero (a.1.val.otherValue i) := ⟨(a.1.val.otherValue_pos i).ne'⟩
  let : NeZero g := ⟨hg.ne_zero⟩
  let : NeZero a.2.1 := ⟨by omega⟩
  dsimp only
  let N := refinementModulus S*a.1.val.otherValue i*g*a.2.1
  let hd := sieve_data ha hg hsupport
  let c := (-h)*((retainedResidue a i g b hd.1 hd.2.1 : ℤ)-i.val)
  let w : ℕ→ℂ := fun q =>  FourierVariation.tentWeight X h (-i.val) (N*q : ℕ)⁻¹
  have hsum :
      (∑ t∈(fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a).attach,
        actualTerm (certificate_mem_of_mem_fibre t.property) hg hsupport b h) =
      ∑ t∈(fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a).attach,
        w t.val.2.2*seq N c 0 [] (t.val.2.2 : ℤ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact actualTerm_eq_fixed a t.val ha (Finset.mem_filter.mp t.property).1
      (Finset.mem_filter.mp t.property).2 hg hsupport b hb h
  apply hsum.trans
  apply (Finset.sum_attach
    (fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a)
      (fun t : SplitCertificate S X => w t.2.2*seq N c 0 [] (t.2.2 : ℤ))).trans
  apply (sum_fibre_eq_domain a ha hzy (fun q => w q*seq N c 0 [] (q : ℤ))).trans
  exact sum_domain_eq_whole_rough a ha hB hzy hg.ne_zero
    (fun p hp => (hsupport p hp).2) c w

end Erdos387Proof.SeparatedFibrePhase
