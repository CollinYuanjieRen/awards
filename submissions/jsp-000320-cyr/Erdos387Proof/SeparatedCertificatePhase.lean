import Erdos387Proof.SeparatedConductorBound
import Erdos387Proof.SquarefreeTuple
import ErdosProblems.Erdos387.DivisorTupleCRT
import ErdosProblems.Erdos387.SubpowerScale

/-!
# Arithmetic phase data from actual separated squarefree certificates

The certificate's small factors are only bounded in size; no smoothness
hypothesis is added. Squarefreeness of the original divisor supplies the
coprimalities needed by the conductor reduction.
-/

namespace Erdos387Proof.SeparatedCertificatePhase

open scoped BigOperators
open Erdos387 Erdos387.CoverBPZ SeparatedConductorBound

def smallProduct {k : ℕ} (f : Fin k → ℕ) : ℕ := ∏ i, f i

def remainingProduct {k : ℕ} (q : Fin k → ℕ) (i : Fin k) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

def remainingPrimes {k : ℕ} (q : Fin k → ℕ) (i : Fin k) : Finset ℕ :=
  ((Finset.univ.erase i).filter fun j => q j ≠ 1).image q

/-- Duplicated nonunit q-coordinates are excluded by coprimality of the
original tuple, not by a smoothness assertion about the f-coordinates. -/
theorem remainingPrimes_data {k : ℕ} (q : Fin k → ℕ) (i : Fin k)
    (hshape : ∀ j, q j = 1 ∨ (q j).Prime)
    (hpair : ∀ a b, a ≠ b → Nat.Coprime (q a) (q b)) :
    (∀ p ∈ remainingPrimes q i, p.Prime) ∧
      (remainingPrimes q i).card ≤ k-1 ∧
      (∏ p ∈ remainingPrimes q i, p) = remainingProduct q i := by
  classical
  have hinj : Set.InjOn q ((Finset.univ.erase i).filter fun j => q j ≠ 1) := by
    intro a ha b hb hab
    by_contra hne
    have hc := hpair a b hne
    rw [hab] at hc
    have hq : q b = 1 := by simpa using hc
    exact (Finset.mem_filter.mp hb).2 hq
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    exact (hshape j).resolve_left (Finset.mem_filter.mp hj).2
  · exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans
      (by simp)
  · unfold remainingPrimes remainingProduct
    rw [Finset.prod_image hinj]
    exact Finset.prod_filter_ne_one _

theorem tuple_small_remaining_factorization {n k : ℕ} {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (f q : Fin k → ℕ) (i : Fin k)
    (hfactor : ∀ j, E.factor j = f j*q j) :
    E.value = smallProduct f * (q i*remainingProduct q i) := by
  unfold CoverDivisorTuple.value smallProduct remainingProduct
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-- The sieve support lies below z while every prime in the represented
divisor lies at least z. This also controls f_i at the removed coordinate. -/
theorem sieve_coprime_value
    {B K X z n g : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ)-S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (hz : 2*S.k ≤ z) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    Nat.Coprime g E.value := by
  obtain ⟨_,hvalueSq,_⟩ := coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨_,hrough⟩ := coverDivisorTuple_rough_data S hnSq hn hprog E hz
  by_contra hcop
  obtain ⟨p,hp,hpg,hpE⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpgMem : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpg,hgSq.ne_zero⟩
  have hpEMem : p ∈ E.value.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpE,hvalueSq.ne_zero⟩
  exact (not_lt_of_ge (hrough p hpEMem)) (hgSupport p hpgMem)

/-- The entire small-factor product, including the removed coordinate,
is bounded using only the individual certificate size bounds. -/
theorem smallProduct_le {k y : ℕ} (f : Fin k → ℕ)
    (hf : ∀ i, f i ≤ y^3) : smallProduct f ≤ y^(3*k) := by
  calc
    smallProduct f ≤ ∏ _i : Fin k, y^3 := Finset.prod_le_prod
      (by intro i _; exact Nat.zero_le _) (by intro i _; exact hf i)
    _ = y^(3*k) := by simp [← pow_mul]

/-- The exact small-modulus condition needed by the proved phase bound.
The only additional scale inputs are g≤t and the fixed modulus M≤t. -/
theorem small_modulus_le {t k g M : ℕ} (f : Fin k → ℕ)
    (hg : g ≤ t) (hM : M ≤ t)
    (hf : ∀ i, f i ≤ (Erdos387.BPZScale.y t k)^3) :
    g*smallProduct f*M ≤ t^(3*k*Erdos387.BPZScale.yExp k+2) := by
  have hf' := smallProduct_le f hf
  calc
    g*smallProduct f*M ≤ t*((Erdos387.BPZScale.y t k)^(3*k))*t :=
      Nat.mul_le_mul (Nat.mul_le_mul hg hf') hM
    _ = t^(3*k*Erdos387.BPZScale.yExp k+2) := by
      unfold Erdos387.BPZScale.y
      rw [← pow_mul, ← pow_succ', ← pow_succ]
      congr 1
      ring

/-- All prime-product and small-modulus coprimalities are inherited from
the original squarefree divisor and its roughness. -/
theorem separated_tuple_products
    {B K X z n g : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ)-S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (f q : Fin S.k → ℕ) (i : Fin S.k)
    (hfactor : ∀ j, E.factor j = f j*q j)
    (hshape : ∀ j, q j = 1 ∨ (q j).Prime)
    (hz : 2*S.k ≤ z) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    (∀ p ∈ remainingPrimes q i, p.Prime) ∧
      (remainingPrimes q i).card ≤ S.k-1 ∧
      (∏ p ∈ remainingPrimes q i, p) = remainingProduct q i ∧
      Squarefree (remainingProduct q i) ∧
      0 < g*smallProduct f*refinementModulus S ∧
      Nat.Coprime (g*smallProduct f*refinementModulus S) (remainingProduct q i) := by
  obtain ⟨hfactorSq,hvalueSq,_⟩ := coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨hM,_⟩ := coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hg := sieve_coprime_value S hnSq hn hprog E hz hgSq hgSupport
  have hpair : ∀ a b, a ≠ b → Nat.Coprime (q a) (q b) := by
    intro a b hab
    have hE : Nat.Coprime (E.factor a) (E.factor b) :=
      Nat.Coprime.of_dvd_right (E.divides b)
        (Nat.Coprime.of_dvd_left (E.divides a)
          (S.coverQuotients_pairwise_coprime hn hprog a a.isLt b b.isLt
            (fun h => hab (Fin.ext h))))
    rw [hfactor a, hfactor b] at hE
    exact (hE.of_dvd_left (dvd_mul_left (q a) (f a))).of_dvd_right
      (dvd_mul_left (q b) (f b))
  obtain ⟨hP,hcard,hprod⟩ := remainingPrimes_data q i hshape hpair
  have hvalue := tuple_small_remaining_factorization E f q i hfactor
  have hsq : Squarefree (smallProduct f*(q i*remainingProduct q i)) := by
    rwa [← hvalue]
  obtain ⟨hF,hFsq,hqsq⟩ := Nat.squarefree_mul_iff.mp hsq
  have hwD : remainingProduct q i ∣ E.value := by
    rw [hvalue]
    exact (dvd_mul_left (remainingProduct q i) (q i)).trans
      (dvd_mul_left (q i*remainingProduct q i) (smallProduct f))
  have hFw : Nat.Coprime (smallProduct f) (remainingProduct q i) :=
    hF.of_dvd_right (dvd_mul_left (remainingProduct q i) (q i))
  have hMw := hM.of_dvd_right hwD
  have hgw := hg.of_dvd_right hwD
  have hposF : 0 < smallProduct f := Nat.pos_of_ne_zero hFsq.ne_zero
  have hMpos := refinementModulus_pos S
  exact ⟨hP,hcard,hprod,Squarefree.squarefree_of_dvd
    (dvd_mul_left (remainingProduct q i) (q i)) hqsq,
    Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hgSq.ne_zero) hposF) hMpos,
    (hgw.mul_left hFw).mul_left hMw⟩

/-- Construct the entire conductor chain from a squarefree separated tuple.
The terminal prime is the actual largest remaining q-coordinate. -/
theorem separated_tuple_phase_data
    {B K X z n g second gap : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ)-S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (f q : Fin S.k → ℕ) (i₀ j₀ : Fin S.k)
    (hfactor : ∀ j, E.factor j = f j*q j)
    (hshape : ∀ j, q j = 1 ∨ (q j).Prime)
    (hij : i₀ ≠ j₀) (hsecond : 1 ≤ second) (hj : second < q j₀)
    (hgap : ∀ j, j ≠ i₀ → gap*q j ≤ q i₀)
    (hz : 2*S.k ≤ z) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    let s₀ := g*smallProduct f*refinementModulus S
    ∃ (j : Fin S.k) (ss : List ℕ), j ≠ i₀ ∧ (q j).Prime ∧ second < q j ∧
      gap*q j ≤ q i₀ ∧ S.k ≤ q j ∧
      (s₀::ss).length ≤ S.k ∧ ss.prod*q j = remainingProduct q i₀ ∧
      Squarefree (ss.prod*q j) ∧ ConductorStripping.CoprimeChain (q j) (s₀::ss) ∧
      ∀ v ∈ ss, v ≤ q j := by
  dsimp only
  obtain ⟨hP,hcard,hprod,_,hs₀,hcop⟩ :=
    separated_tuple_products S hnSq hn hprog E f q i₀ hfactor hshape hz hgSq hgSupport
  obtain ⟨j,hji,hpj,hsecondj,hgapj,hmax⟩ :=
    exists_maximal_remaining_prime S.k second gap q i₀ j₀ hij hsecond hj hshape hgap
  have hjP : q j ∈ remainingPrimes q i₀ := by
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨?_, hpj.ne_one⟩, rfl⟩
    exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
  have hmaxP : ∀ v ∈ remainingPrimes q i₀, v ≤ q j := by
    intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    exact hmax l (Finset.mem_erase.mp (Finset.mem_filter.mp hl).1).1
  obtain ⟨ss,hlen,hssprod,hsq,hchain,hssmax⟩ :=
    prime_set_stripping_data (remainingPrimes q i₀) (q j)
      (g*smallProduct f*refinementModulus S) hjP hP hmaxP hs₀ (by rwa [hprod])
  have hpdiv : q j ∣ E.value := by
    have hqj : q j ∣ E.factor j := by rw [hfactor j]; exact dvd_mul_left _ _
    exact hqj.trans (Finset.dvd_prod_of_mem E.factor (Finset.mem_univ j))
  obtain ⟨_,hvalueSq,_⟩ := coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨_,hrough⟩ := coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hzp : z ≤ q j := hrough (q j)
    (Nat.mem_primeFactors.mpr ⟨hpj,hpdiv,hvalueSq.ne_zero⟩)
  refine ⟨j,ss,hji,hpj,hsecondj,hgapj,by omega,?_,hssprod.trans hprod,hsq,hchain,hssmax⟩
  rw [hlen]
  exact hcard.trans (Nat.sub_le _ _)

/-- CRT residues of the original tuple give nonzero index-difference
coefficients at the selected terminal prime. -/
theorem cover_crt_coefficient_ne_zero
    {n k : ℕ} {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) (i j : Fin k) (hji : j ≠ i)
    (p : ℕ) [NeZero p] (hkp : k ≤ p) (hpdvd : p ∣ E.factor j) :
    (((E.crtResidue : ℤ)-(i.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
  apply difference_ne_zero_mod p i.val j.val (i.isLt.trans_le hkp)
    (j.isLt.trans_le hkp) (fun h => hji (Fin.ext h.symm)) (E.crtResidue : ℤ)
  simpa only [Int.cast_natCast] using
    (ZMod.natCast_eq_natCast_iff E.crtResidue j.val p).mpr
      ((E.crtResidue_mod_factor j).of_dvd hpdvd)

/-- Any subsequently combined CRT residue with the same original tuple
congruences has the same nonzero index-difference coefficient. -/
theorem combined_crt_coefficient_ne_zero
    {n k : ℕ} {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) (i j : Fin k) (hji : j ≠ i)
    (p b : ℕ) [NeZero p] (hkp : k ≤ p) (hpdvd : p ∣ E.factor j)
    (hb : Nat.ModEq E.value b E.crtResidue) :
    (((b : ℤ)-(i.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
  have hpd : p ∣ E.value := hpdvd.trans
    (Finset.dvd_prod_of_mem E.factor (Finset.mem_univ j))
  have heq : (b : ZMod p) = (E.crtResidue : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff b E.crtResidue p).mpr (hb.of_dvd hpd)
  simpa only [Int.cast_sub, Int.cast_natCast, heq] using
    cover_crt_coefficient_ne_zero E i j hji p hkp hpdvd

/-- Arithmetic output extracted from the actual original error certificate.
This record contains no estimate for a phase or for an error count. -/
structure CertificatePhaseData {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium second gap g : ℕ) where
  hn : S.k < n
  hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ)-S.α
  E : CoverDivisorTuple (S.toCoverFactorization hn hprog)
  f : Fin S.k → ℕ
  q : Fin S.k → ℕ
  i₀ : Fin S.k
  j : Fin S.k
  ss : List ℕ
  near : n < B*E.value
  upper : E.value ≤ n
  factor : ∀ i, E.factor i = f i*q i
  small : ∀ i, f i ≤ y^3
  shape : ∀ i, q i = 1 ∨ (q i).Prime ∧ y < q i
  medium_bound : ∀ i, E.factor i ≤ medium
  largest : ∀ i, q i ≤ q i₀
  value_squarefree : Squarefree E.value
  terminal_ne : j ≠ i₀
  terminal_prime : (q j).Prime
  terminal_large : second < q j
  terminal_gap : gap*q j ≤ q i₀
  index_bound : S.k ≤ q j
  depth : (g*smallProduct f*refinementModulus S::ss).length ≤ S.k
  remaining : ss.prod*q j = remainingProduct q i₀
  remaining_squarefree : Squarefree (ss.prod*q j)
  chain : ConductorStripping.CoprimeChain (q j)
    (g*smallProduct f*refinementModulus S::ss)
  remaining_max : ∀ v ∈ ss, v ≤ q j

/-- Extracting phase-ready arithmetic data preserves the original tuple,
near-divisor window, factor decomposition and all stated size ranges. -/
theorem exists_certificatePhaseData
    {B K X z n y medium second gap g : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (herr : HasSeparatedAlmostPrimeError S n y medium second gap)
    (hsecond : 1 ≤ second) (hz : 2*S.k ≤ z) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    Nonempty (CertificatePhaseData S n y medium second gap g) := by
  obtain ⟨hn,hprog,d,E,f,q,i₀,j₀,hnear,hupper,hvalue,hfactor,hsmall,
    hshape,hmedium,hlargest,hij,hsecondj,hgap⟩ := herr
  obtain ⟨j,ss,hji,hpj,hsecondp,hgapj,hkp,hlen,hprod,hsq,hchain,hmax⟩ :=
    separated_tuple_phase_data S hnSq hn hprog E f q i₀ j₀ hfactor
      (fun i => (hshape i).imp_right And.left) hij hsecond hsecondj hgap hz hgSq hgSupport
  have hvalueSq := (coverDivisorTuple_squarefree_data S hnSq hn hprog E).2.1
  exact ⟨{ hn := hn, hprog := hprog, E := E, f := f, q := q, i₀ := i₀, j := j, ss := ss
           near := by rwa [hvalue]
           upper := by rwa [hvalue]
           factor := hfactor, small := hsmall, shape := hshape
           medium_bound := hmedium, largest := hlargest, value_squarefree := hvalueSq
           terminal_ne := hji, terminal_prime := hpj, terminal_large := hsecondp
           terminal_gap := hgapj, index_bound := hkp, depth := hlen
           remaining := hprod, remaining_squarefree := hsq, chain := hchain
           remaining_max := hmax }⟩

namespace CertificatePhaseData

/-- The actual conductor after removing the largest prime coordinate. -/
noncomputable def modulus {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) : ℕ :=
  g*smallProduct C.f*refinementModulus S*remainingProduct C.q C.i₀

theorem modulus_eq {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) :
    C.modulus = (g*smallProduct C.f*refinementModulus S::C.ss).prod*C.q C.j := by
  simp only [modulus, List.prod_cons, Nat.mul_assoc, C.remaining]

/-- Multiplying back the removed largest prime recovers the original
full CRT modulus g*M*E.value exactly. -/
theorem modulus_mul_removed
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) :
    C.modulus*C.q C.i₀ = g*C.E.value*refinementModulus S := by
  rw [tuple_small_remaining_factorization C.E C.f C.q C.i₀ C.factor]
  unfold modulus
  ring

theorem modulus_pos {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) : 0 < C.modulus := by
  rw [C.modulus_eq]
  exact Nat.mul_pos C.chain.prod_pos C.terminal_prime.pos

/-- Canonical CRT data attached to the same original divisor tuple. -/
noncomputable def crtTuple {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) :
    CoprimeCoverDivisorTuple (S.toCoverFactorization C.hn C.hprog) where
  toCoverDivisorTuple := C.E
  positive i := Nat.pos_of_ne_zero (Squarefree.squarefree_of_dvd
    (Finset.dvd_prod_of_mem C.E.factor (Finset.mem_univ i)) C.value_squarefree).ne_zero
  pairwise a b hab := Nat.Coprime.of_dvd_right (C.E.divides b)
    (Nat.Coprime.of_dvd_left (C.E.divides a)
      (S.coverQuotients_pairwise_coprime C.hn C.hprog a a.isLt b b.isLt
        (fun h => hab (Fin.ext h))))

theorem crt_coefficient_ne_zero
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) :
    (((C.crtTuple.crtResidue : ℤ)-(C.i₀.val : ℤ) : ℤ) : ZMod (C.q C.j)) ≠ 0 := by
  have : NeZero (C.q C.j) := ⟨C.terminal_prime.ne_zero⟩
  apply cover_crt_coefficient_ne_zero C.crtTuple C.i₀ C.j C.terminal_ne
    (C.q C.j) C.index_bound
  change C.q C.j ∣ C.E.factor C.j
  rw [C.factor]
  exact dvd_mul_left _ _

/-- Only the congruences retained after removing i₀ are needed for the
index-difference coefficient. No congruence at the removed prime is assumed. -/
theorem combined_coefficient_ne_zero
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) (b : ℕ)
    (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val) :
    (((b : ℤ)-(C.i₀.val : ℤ) : ℤ) : ZMod (C.q C.j)) ≠ 0 := by
  have : NeZero (C.q C.j) := ⟨C.terminal_prime.ne_zero⟩
  have hdvd : C.q C.j ∣ C.E.factor C.j := by rw [C.factor]; exact dvd_mul_left _ _
  apply difference_ne_zero_mod (C.q C.j) C.i₀.val C.j.val
    (C.i₀.isLt.trans_le C.index_bound) (C.j.isLt.trans_le C.index_bound)
    (fun h => C.terminal_ne (Fin.ext h.symm)) (b : ℤ)
  simpa only [Int.cast_natCast] using
    (ZMod.natCast_eq_natCast_iff b C.j.val (C.q C.j)).mpr
      ((hb C.j C.terminal_ne).of_dvd hdvd)

instance modulusNeZero {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) : NeZero C.modulus :=
  ⟨Nat.ne_of_gt C.modulus_pos⟩

/-- The proved numerical phase saving applied to an actual extracted
certificate. Its scale hypotheses contain no analytic bound. -/
theorem norm_dyadic_phase_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q u : ℕ) (hQ : C.q C.i₀ ≤ Q) (hu : 0 < u) (huQ : u ≤ Q)
    (huY : u ≤ (BPZScale.y t S.k)^2)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a A : ℤ) (hc : (c : ZMod (C.q C.j)) ≠ 0) :
    ‖PeriodicStripping.intervalSum A (Q/u-Q/(2*u))
      (fun v => χ v*MaskedReciprocalPhase.seq C.modulus c a [] v)‖ ≤
        4*((Q/u-Q/(2*u) : ℕ) : ℝ)/(t : ℝ) := by
  have : NeZero (C.q C.j) := ⟨C.terminal_prime.ne_zero⟩
  have : Fact (C.q C.j).Prime := ⟨C.terminal_prime⟩
  exact norm_bpz_dyadic_char_seq_le (C.q C.j) t S.k Q u
    (g*smallProduct C.f*refinementModulus S) C.ss S.hk3 ht C.depth
    C.chain.1 C.chain.2.1 C.remaining_squarefree C.remaining_max
    (small_modulus_le C.f hg hM C.small) C.terminal_large.le hu huQ huY
    (C.terminal_gap.trans hQ) C.modulus C.modulus_eq χ hχ c a A hc

/-- The actual retained CRT classes give the nonzero nonfrequency factor.
A frequency divisible by the terminal prime is left with the trivial bound. -/
theorem norm_dyadic_frequency_split
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q u : ℕ) (hQ : C.q C.i₀ ≤ Q) (hu : 0 < u) (huQ : u ≤ Q)
    (huY : u ≤ (BPZScale.y t S.k)^2)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h a A : ℤ) :
    ‖PeriodicStripping.intervalSum A (Q/u-Q/(2*u))
      (fun v => χ v*MaskedReciprocalPhase.seq C.modulus
        (h*((b : ℤ)-C.i₀.val)) a [] v)‖ ≤
      if (h : ZMod (C.q C.j)) = 0 then ((Q/u-Q/(2*u) : ℕ) : ℝ)
      else 4*((Q/u-Q/(2*u) : ℕ) : ℝ)/(t : ℝ) := by
  have : Fact (C.q C.j).Prime := ⟨C.terminal_prime⟩
  split_ifs with hh
  · apply PeriodicStripping.norm_intervalSum_le
    intro v
    rw [norm_mul,hχ,one_mul]
    exact MaskedReciprocalPhase.norm_seq_le _ _ _ _ _
  · apply C.norm_dyadic_phase_le ht hg hM Q u hQ hu huQ huY χ hχ
    simpa only [Int.cast_mul] using mul_ne_zero hh (C.combined_coefficient_ne_zero b hb)

theorem terminal_dvd_modulus
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) : C.q C.j ∣ C.modulus := by
  rw [C.modulus_eq]
  exact dvd_mul_left _ _

/-- Original-conductor coprimality supplies the terminal-prime unit
condition before applying any inverse-phase nonvanishing assertion. -/
theorem unit_mod_terminal
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g)
    (r : ℕ) (hr : Nat.Coprime r C.modulus) : IsUnit (r : ZMod (C.q C.j)) :=
  (ZMod.isUnit_iff_coprime r (C.q C.j)).mpr (hr.of_dvd_right C.terminal_dvd_modulus)

/-- Type-I reciprocal multipliers are units; inverting one does not create
an exceptional coefficient. -/
theorem typeI_coefficient_ne_zero
    {B K n y medium second gap g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g) (b : ℕ)
    (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (r : ℕ) (hr : Nat.Coprime r C.modulus) :
    (h : ZMod (C.q C.j))*((b : ZMod (C.q C.j))-C.i₀.val)*
      (r : ZMod (C.q C.j))⁻¹ ≠ 0 := by
  have : Fact (C.q C.j).Prime := ⟨C.terminal_prime⟩
  have hb' : ((b : ZMod (C.q C.j))-C.i₀.val) ≠ 0 := by
    simpa only [Int.cast_sub, Int.cast_natCast] using C.combined_coefficient_ne_zero b hb
  exact mul_ne_zero (mul_ne_zero hh hb') (inv_ne_zero (C.unit_mod_terminal r hr).ne_zero)

/-- The concrete second-prime threshold dominates the entire Type-II
multiplier range y². -/
theorem small_multiplier_lt_terminal
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 1 ≤ t) (u : ℕ) (hu : u ≤ (BPZScale.y t S.k)^2) : u < C.q C.j := by
  have hexp : 2*BPZScale.yExp S.k ≤ BPZScale.secondExp S.k := by
    have hh := (bpz_exponent_margins S.k S.hk3).2.2
    have hk := S.hk3
    nlinarith
  apply (hu.trans _).trans_lt C.terminal_large
  unfold BPZScale.y BPZScale.secondMin
  rw [← pow_mul]
  exact Nat.pow_le_pow_right ht (by simpa [Nat.mul_comm] using hexp)

/-- Type-II distinct multipliers give a nonzero difference modulo the
terminal prime. The subtraction here is in ZMod, never truncated Nat
subtraction, and the two multipliers need only satisfy their original y² bounds. -/
theorem typeII_coefficient_ne_zero
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 1 ≤ t) (b : ℕ)
    (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (u₁ u₂ : ℕ) (hu₁ : u₁ ≤ (BPZScale.y t S.k)^2)
    (hu₂ : u₂ ≤ (BPZScale.y t S.k)^2) (hne : u₁ ≠ u₂)
    (hu : Nat.Coprime (u₁*u₂) C.modulus) :
    (h : ZMod (C.q C.j))*((b : ZMod (C.q C.j))-C.i₀.val)*
      ((u₁*u₂ : ℕ) : ZMod (C.q C.j))⁻¹*
        ((u₂ : ZMod (C.q C.j))-(u₁ : ZMod (C.q C.j))) ≠ 0 := by
  have : Fact (C.q C.j).Prime := ⟨C.terminal_prime⟩
  have : NeZero (C.q C.j) := ⟨C.terminal_prime.ne_zero⟩
  apply mul_ne_zero (C.typeI_coefficient_ne_zero b hb h hh _ hu)
  have hd := difference_ne_zero_mod (C.q C.j) u₁ u₂
    (C.small_multiplier_lt_terminal ht u₁ hu₁)
    (C.small_multiplier_lt_terminal ht u₂ hu₂) hne (u₂ : ℤ) (by simp)
  simpa only [Int.cast_sub, Int.cast_natCast] using hd

end CertificatePhaseData

/-- An actual finite squarefree Brun-support product supplies the sieve
hypotheses required during certificate extraction. -/
theorem brun_support_data (T : Finset ℕ) (z : ℕ)
    (hprime : ∀ p ∈ T, p.Prime) (hT : ∀ p ∈ T, p < z) :
    Squarefree (∏ p ∈ T, p) ∧
      ∀ p ∈ (∏ v ∈ T, v).primeFactors, p < z := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      change IsRelPrime p q
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
    · intro p hp
      exact (hprime p hp).squarefree
  · simpa only [Nat.primeFactors_prod hprime] using hT

/-- At the linear Brun truncation depth 2N, the sieve support is at most
one copy of the subpower base once N≥2*xExp(k). -/
theorem brun_support_le_base (N k : ℕ) (T : Finset ℕ)
    (hN : 2*BPZScale.xExp k ≤ N) (hcard : T.card ≤ 2*N)
    (hT : ∀ p ∈ T, p < SubpowerScale.z N k) :
    (∏ p ∈ T, p) ≤ SubpowerScale.base N k := by
  have hz : 1 ≤ SubpowerScale.z N k := Nat.one_le_pow _ _ (by omega)
  have hexp : SubpowerScale.roughPower N k*(2*N) ≤ SubpowerScale.scalePower N k := by
    calc
      SubpowerScale.roughPower N k*(2*N) = (2*BPZScale.xExp k)*N^(2*k+4) := by
        unfold SubpowerScale.roughPower
        rw [show 2*k+4 = (2*k+3)+1 by omega, pow_succ]
        ring
      _ ≤ N*N^(2*k+4) := Nat.mul_le_mul_right _ hN
      _ = SubpowerScale.scalePower N k := by
        unfold SubpowerScale.scalePower
        rw [show 2*k+5 = (2*k+4)+1 by omega, pow_succ]
        ring
  calc
    (∏ p ∈ T, p) ≤ ∏ _p ∈ T, SubpowerScale.z N k :=
      Finset.prod_le_prod (by intro p _; omega) (by intro p hp; exact (hT p hp).le)
    _ = (SubpowerScale.z N k)^T.card := by simp
    _ ≤ (SubpowerScale.z N k)^(2*N) := Nat.pow_le_pow_right hz hcard
    _ ≤ SubpowerScale.base N k := by
      unfold SubpowerScale.z SubpowerScale.base
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) hexp

/-- An explicit threshold controls all fixed small-scale constants. -/
theorem le_subpower_base (N k : ℕ) (hN : 1 ≤ N) : N ≤ SubpowerScale.base N k := by
  calc
    N ≤ 2^N := (Nat.lt_two_pow_self (n := N)).le
    _ ≤ 2^(N^(2*k+5)) := Nat.pow_le_pow_right (by omega)
      (le_self_pow hN (by omega))

/-- These are concrete finite thresholds for the phase consumer's extra
scale conditions, rather than an assumed eventual phase-saving theorem. -/
theorem subpower_phase_scale_conditions
    {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) (T : Finset ℕ)
    (hN : max (2*BPZScale.xExp S.k)
      (max (refinementModulus S) (6*2^S.k)) ≤ N)
    (hcard : T.card ≤ 2*N) (hT : ∀ p ∈ T, p < SubpowerScale.z N S.k) :
    (∏ p ∈ T, p) ≤ SubpowerScale.base N S.k ∧
      refinementModulus S ≤ SubpowerScale.base N S.k ∧
      6*2^S.k ≤ SubpowerScale.base N S.k := by
  have hh := le_max_left (2*BPZScale.xExp S.k)
    (max (refinementModulus S) (6*2^S.k))
  have hM : refinementModulus S ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have ht : 6*2^S.k ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (refinementModulus_pos S).trans_le hM
  have hbase := le_subpower_base N S.k hN1
  exact ⟨brun_support_le_base N S.k T (hh.trans hN) hcard hT,
    hM.trans hbase, ht.trans hbase⟩

end Erdos387Proof.SeparatedCertificatePhase
