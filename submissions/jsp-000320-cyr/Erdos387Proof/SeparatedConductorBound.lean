import Erdos387Proof.ConductorStripping
import Mathlib.Data.Nat.Squarefree
import ErdosProblems.Erdos387.ParameterScale

/-!
# Numerical conductor reduction for separated factors

This is the numerical consumer of the finite conductor iteration used in
BNPZ arXiv:2605.21221v2, §10.  In particular the terminal remainder is bounded
explicitly; a prime larger than the original interval cannot silently be used.
The scale inequalities here are arithmetic obligations for the separated
certificate, not additional assumptions on the original Erdős problem.
-/

namespace Erdos387Proof.SeparatedConductorBound

open scoped BigOperators ComplexConjugate
open PeriodicStripping MaskedReciprocalPhase ConductorStripping

/-- Squarefreeness of the whole factorization supplies every coprimality
needed during stripping, including coprimality with the terminal prime. -/
theorem coprimeChain_of_squarefree (p : ℕ) (ss : List ℕ)
    (hsq : Squarefree (ss.prod*p)) : CoprimeChain p ss := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    have h : Squarefree (s*(ss.prod*p)) := by
      simpa only [List.prod_cons, Nat.mul_assoc] using hsq
    obtain ⟨hcop, hs, ht⟩ := Nat.squarefree_mul_iff.mp h
    exact ⟨Nat.pos_of_ne_zero hs.ne_zero, hcop, ih ht⟩

/-- A uniform quantitative bound for the explicit finite recursive envelope.
The terminal bound is the concrete prime envelope, not an analytic premise. -/
theorem iteratedBound_le_four_mul
    (L K p : ℕ) (ss : List ℕ) (j : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbase : iteratedBound L K p [] (j+ss.length) ≤ (L : ℝ)*δ^(2^ss.length))
    (hK : 1/(K : ℝ) ≤ δ^(2^ss.length))
    (hboundary : ∀ s ∈ ss,
      (s : ℝ)^2*((K : ℝ)-1)^2 ≤ (L : ℝ)^2*δ^(2^ss.length)) :
    iteratedBound L K p ss j ≤ 4*(L : ℝ)*δ := by
  induction ss generalizing j δ with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, pow_zero, pow_one] at hbase
    nlinarith [mul_nonneg (Nat.cast_nonneg L) hδ]
  | cons s ss ih =>
    have hexp : (δ^2)^(2^ss.length) = δ^(2^(s::ss).length) := by
      rw [← pow_mul, List.length_cons, pow_succ]
      congr 1
      omega
    have hd2 : δ^2 ≤ 1 := by nlinarith
    have hbase' : iteratedBound L K p [] ((j+1)+ss.length) ≤
        (L : ℝ)*(δ^2)^(2^ss.length) := by
      simpa only [hexp, List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hbase
    have hi := ih (j+1) (δ^2) (sq_nonneg δ) hd2 hbase'
      (by simpa only [hexp] using hK)
      (by intro v hv; simpa only [hexp] using hboundary v (List.mem_cons_of_mem s hv))
    have hpow : δ^(2^(s::ss).length) ≤ δ^2 := by
      apply pow_le_pow_of_le_one hδ hδ1
      simp only [List.length_cons, pow_succ]
      have : 1 ≤ 2^ss.length := Nat.one_le_pow _ _ (by omega)
      omega
    have hk' := mul_le_mul_of_nonneg_left (hK.trans hpow)
      (show 0 ≤ 2*(L : ℝ)^2 by positivity)
    simp only [mul_one_div] at hk'
    have hb := (hboundary s (List.mem_cons_self)).trans
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg (L : ℝ)))
    have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*(L : ℝ) by positivity)
    change Real.sqrt _ ≤ _
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hnon : 0 ≤ (L : ℝ)^2*δ^2 := by positivity
      nlinarith

/-- A convenient coarse version of the sharp prime envelope. -/
theorem primeBound_le (p j : ℕ) (hp : 1 ≤ p) :
    primeBound p j ≤ 3*(2^j : ℕ)*Real.sqrt (p : ℝ) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 1 ≤ Real.sqrt (p : ℝ) := by
    simpa using Real.sqrt_le_sqrt hp'
  have hc : ((2*2^j-1 : ℕ) : ℝ) ≤ 2*(2^j : ℕ) := by
    exact_mod_cast Nat.sub_le (2*2^j) 1
  unfold primeBound
  have hmul := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (p : ℝ))
  have hmul' := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ (2^j : ℕ) by positivity)
  nlinarith

/-- A terminal interval estimate with the complete-period remainder visible.
The conditions rule out the invalid use of complete-period cancellation on
an interval much shorter than the terminal prime. -/
theorem terminalBound_le (L K p j : ℕ) (hp : 0 < p) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hprime : 6*(2^j : ℕ) ≤ ρ*Real.sqrt (p : ℝ))
    (hinterval : 2*(p : ℝ) ≤ (L : ℝ)*ρ) :
    iteratedBound L K p [] j ≤ (L : ℝ)*ρ := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hs0 := Real.sqrt_nonneg (p : ℝ)
  have hs2 := Real.sq_sqrt (le_of_lt hp')
  have hpb := primeBound_le p j hp
  have hprod := mul_le_mul_of_nonneg_right hprime hs0
  have hpb' : 2*primeBound p j ≤ ρ*(p : ℝ) := by nlinarith
  have hq : ((L/p : ℕ) : ℝ)*(p : ℝ) ≤ L := by
    exact_mod_cast Nat.div_mul_le_self L p
  have hq' := mul_le_mul_of_nonneg_right hq hρ
  have hprod' := mul_le_mul_of_nonneg_left hpb'
    (show (0 : ℝ) ≤ (L/p : ℕ) by positivity)
  have hr : ((L%p : ℕ) : ℝ) ≤ p := by exact_mod_cast (Nat.mod_lt L hp).le
  simp only [iteratedBound]
  nlinarith

/-- Explicit integral scale conditions imply a saving of a factor t in the
proved conductor envelope.  Every assumption is an arithmetic inequality;
no cancellation statement is assumed. -/
theorem iteratedBound_le_div_scale (L K p t : ℕ) (ss : List ℕ) (j : ℕ)
    (ht : 1 ≤ t) (hp : 0 < p)
    (hK : t^(2^ss.length) ≤ K)
    (hprime : (6*2^(j+ss.length)*t^(2^ss.length))^2 ≤ p)
    (hinterval : 2*p*t^(2^ss.length) ≤ L)
    (hboundary : ∀ s ∈ ss, s*K*t^(2^ss.length) ≤ L) :
    iteratedBound L K p ss j ≤ 4*(L : ℝ)/(t : ℝ) := by
  let R : ℝ := (t : ℝ)^(2^ss.length)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hR1 : 1 ≤ R := one_le_pow₀ ht'
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hρ : 0 ≤ 1/R := by positivity
  have hρ1 : 1/R ≤ 1 := (div_le_one hR).mpr hR1
  have heq : (1/(t : ℝ))^(2^ss.length) = 1/R := by
    simp only [one_div, inv_pow, R]
  have hK' : R ≤ (K : ℝ) := by dsimp [R]; exact_mod_cast hK
  have hsqrt : 6*(2^(j+ss.length) : ℕ)*R ≤ Real.sqrt (p : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    dsimp [R]
    exact_mod_cast hprime
  have hprime' : 6*(2^(j+ss.length) : ℕ) ≤ (1/R)*Real.sqrt (p : ℝ) := by
    apply (le_div_iff₀ hR).mpr at hsqrt
    simpa [one_div, div_eq_mul_inv, mul_comm] using hsqrt
  have hinterval' : 2*(p : ℝ) ≤ (L : ℝ)*(1/R) := by
    rw [mul_one_div]
    apply (le_div_iff₀ hR).mpr
    dsimp [R]
    exact_mod_cast hinterval
  have hbase := terminalBound_le L K p (j+ss.length) hp (1/R) hρ hprime' hinterval'
  have hbound (s : ℕ) (hs : s ∈ ss) :
      (s : ℝ)^2*((K : ℝ)-1)^2 ≤ (L : ℝ)^2*(1/R) := by
    have hsk : (s : ℝ)*((K : ℝ)-1) ≤ (L : ℝ)*(1/R) := by
      rw [mul_one_div]
      apply (le_div_iff₀ hR).mpr
      have h := hboundary s hs
      have hh : (s : ℝ)*(K : ℝ)*R ≤ L := by dsimp [R]; exact_mod_cast h
      have hh' : 0 ≤ (s : ℝ)*R := by positivity
      nlinarith
    have hsk0 : 0 ≤ (s : ℝ)*((K : ℝ)-1) := by
      have : (1 : ℝ) ≤ K := hR1.trans hK'
      positivity
    have hsq := pow_le_pow_left₀ hsk0 hsk 2
    have hρsq : (1/R)^2 ≤ 1/R := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hρsq (sq_nonneg (L : ℝ))
    nlinarith
  have hh := iteratedBound_le_four_mul L K p ss j (1/(t : ℝ))
    (by positivity) ((div_le_one (lt_of_lt_of_le zero_lt_one ht')).mpr ht')
    (by simpa only [heq] using hbase)
    (by rw [heq]; exact one_div_le_one_div_of_le hR hK')
    (by intro s hs; simpa only [heq] using hbound s hs)
  simpa only [mul_one_div] using hh

/-- The dyadic interval obtained after dividing by u retains at least Q/(4u)
terms. This bound includes both integer-rounding errors. -/
theorem dyadic_length_lower (Q u : ℕ) (hu : 0 < u) (huQ : u ≤ Q) :
    Q ≤ 4*u*(Q/u-Q/(2*u)) := by
  have hT : 1 ≤ Q/u := (Nat.le_div_iff_mul_le hu).mpr (by simpa using huQ)
  have hdiv : Q/(2*u) = (Q/u)/2 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm u 2]
  have hrem := Nat.mod_lt Q hu
  have hdecomp := Nat.mod_add_div Q u
  have hhalf := Nat.mod_add_div (Q/u) 2
  have hrem2 := Nat.mod_lt (Q/u) (by omega : 0 < 2)
  rw [hdiv]
  have h₁ : Q < u*(Q/u+1) := by nlinarith
  have h₂ : Q/u+1 ≤ 2*(Q/u) := by omega
  have h₃ : Q/u ≤ 2*(Q/u-(Q/u)/2) := by omega
  nlinarith [Nat.mul_le_mul_left u h₂, Nat.mul_le_mul_left (2*u) h₃]

/-- An initial unit additive character costs no extra terminal depth.  It
vanishes from the first correlation norm, after which the actual unweighted
conductor iteration applies.  The removed list must contain a first factor. -/
theorem norm_interval_char_seq_le_iterated
    (p : ℕ) [NeZero p] [Fact p.Prime] (L K : ℕ) (hK : 0 < K) (hKp : K ≤ p)
    (s : ℕ) (ss : List ℕ) (hchain : CoprimeChain p (s::ss))
    (q : ℕ) [NeZero q] (hq : q = (s::ss).prod*p)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ)
    (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^(hs.length+(s::ss).length) < p) :
    ‖intervalSum A L (fun n => χ n*seq q c a hs n)‖ ≤
      iteratedBound L K p (s::ss) hs.length := by
  obtain ⟨hspos,hcop,hchain⟩ := hchain
  let t := ss.prod*p
  have htpos : 0 < t := Nat.mul_pos hchain.prod_pos (Nat.pos_of_ne_zero (NeZero.ne p))
  have : NeZero s := ⟨Nat.ne_of_gt hspos⟩
  have : NeZero t := ⟨Nat.ne_of_gt htpos⟩
  have hqt : q = s*t := by simpa [List.prod_cons, Nat.mul_assoc, t] using hq
  clear hq
  subst q
  have hpt : p ∣ t := by dsimp [t]; exact dvd_mul_left p ss.prod
  have hsp : Nat.Coprime s p := hcop.of_dvd_right hpt
  have hc' := twist_ne_zero s t p hcop hpt c hc
  let B := iteratedBound L K p ss (hs.length+1)
  have hB0 : 0 ≤ B := iteratedBound_nonneg L K p ss (hs.length+1)
  have hnext (j : ℕ) (hj : j < K) (i : ℕ) (hi : i < j) :
      ‖intervalSum A L (seq t (c*Nat.gcdA s t) a
        (((j*s : ℕ),(i*s : ℕ))::hs))‖ ≤ B := by
    have hd : ∀ uv ∈ (((j*s : ℕ),(i*s : ℕ))::hs : List (ℤ × ℤ)),
        (uv.1 : ZMod p) ≠ (uv.2 : ZMod p) := by
      intro uv huv
      rcases List.mem_cons.mp huv with rfl | huv
      · simpa using paired_shift_ne p s K j i hsp hKp hj hi
      · exact hdistinct uv huv
    have hsm : 2^((((j*s : ℕ),(i*s : ℕ))::hs : List (ℤ × ℤ)).length+ss.length) < p := by
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsmall
    exact norm_interval_seq_le_iterated p L K hK hKp ss hchain t rfl
      (c*Nat.gcdA s t) a (((j*s : ℕ),(i*s : ℕ))::hs) A hc' hd hsm
  have h := norm_interval_char_seq_sq_le s t hcop χ hχ c a hs A L K hK
  have hm := nextCorrelationMass_le t (c*Nat.gcdA s t) a hs A L K s B hnext
  have hcount : (((K*(K-1)/2 : ℕ) : ℝ)) ≤ (K : ℝ)^2/2 := by
    have hh : 2*(K*(K-1)/2) ≤ K*K := by
      have h₁ := Nat.div_mul_le_self (K*(K-1)) 2
      have h₂ := Nat.mul_le_mul_left K (Nat.sub_le K 1)
      omega
    have hh' : (2 : ℝ)*((K*(K-1)/2 : ℕ) : ℝ) ≤ (K : ℝ)*(K : ℝ) := by
      exact_mod_cast hh
    nlinarith
  have hmass := hm.trans (mul_le_mul_of_nonneg_right hcount hB0)
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hterm : (4*(L : ℝ)/(K : ℝ)^2)*nextCorrelationMass t (c*Nat.gcdA s t) a hs A L K s
      ≤ 2*L*B := by
    have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4*(L : ℝ)/(K : ℝ)^2 by positivity)
    convert hh using 1
    all_goals try field_simp [ne_of_gt hk]
    all_goals first | rfl | ring
  have hr : 0 ≤ 2*(L : ℝ)^2/K + 2*L*B + 2*(s : ℝ)^2*((K : ℝ)-1)^2 := by
    positivity
  change ‖intervalSum A L (fun n => χ n*seq (s*t) c a hs n)‖ ≤ Real.sqrt _
  have he := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (2*(L : ℝ)^2/K + 2*L*B + 2*(s : ℝ)^2*((K : ℝ)-1)^2)
  nlinarith [norm_nonneg (intervalSum A L (fun n => χ n*seq (s*t) c a hs n))]

/-- The averaging length is a fixed integer power of the scale. Its comparison
with the terminal prime and the pole-support size follow from the same
explicit lower bound on p. -/
theorem scale_averaging_data (p t r j : ℕ) (ht : 1 ≤ t)
    (hprime : (6*2^(j+r)*t^(2^r))^2 ≤ p) :
    0 < (t^(2^r))^2 ∧ (t^(2^r))^2 ≤ p ∧
      2^(j+r) < p ∧ t^(2^r) ≤ (t^(2^r))^2 := by
  have hR : 1 ≤ t^(2^r) := Nat.one_le_pow _ _ ht
  have hD : 1 ≤ 2^(j+r) := Nat.one_le_pow _ _ (by omega)
  have hDR : t^(2^r) ≤ 6*2^(j+r)*t^(2^r) := by nlinarith
  have hDD : 2^(j+r) < 6*2^(j+r)*t^(2^r) := by nlinarith
  have hbig : 1 ≤ 6*2^(j+r)*t^(2^r) := by omega
  have hs : (t^(2^r))^2 ≤ (6*2^(j+r)*t^(2^r))^2 :=
    Nat.pow_le_pow_left hDR 2
  refine ⟨by positivity, hs.trans hprime, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Explicit scale saving for the actual zero-extended reciprocal phase.
All new shifts, coefficient twists and prime cancellation hypotheses are
proved by the finite iteration. -/
theorem norm_interval_seq_le_div_scale
    (p : ℕ) [NeZero p] [Fact p.Prime] (L t : ℕ) (ht : 1 ≤ t)
    (ss : List ℕ) (hchain : CoprimeChain p ss)
    (q : ℕ) [NeZero q] (hq : q = ss.prod*p)
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ)
    (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hprime : (6*2^(hs.length+ss.length)*t^(2^ss.length))^2 ≤ p)
    (hinterval : 2*p*t^(2^ss.length) ≤ L)
    (hboundary : ∀ s ∈ ss, s*(t^(2^ss.length))^2*t^(2^ss.length) ≤ L) :
    ‖intervalSum A L (seq q c a hs)‖ ≤ 4*(L : ℝ)/(t : ℝ) := by
  obtain ⟨hK,hKp,hsmall,hR⟩ := scale_averaging_data p t ss.length hs.length ht hprime
  exact (norm_interval_seq_le_iterated p L ((t^(2^ss.length))^2) hK hKp
    ss hchain q hq c a hs A hc hdistinct hsmall).trans
    (iteratedBound_le_div_scale L _ p t ss hs.length ht
      (Nat.pos_of_ne_zero (NeZero.ne p)) hR hprime hinterval hboundary)

/-- The same scale saving permits the linear additive character present in
BNPZ's completed interval sums. A first conductor factor removes it exactly. -/
theorem norm_interval_char_seq_le_div_scale
    (p : ℕ) [NeZero p] [Fact p.Prime] (L t : ℕ) (ht : 1 ≤ t)
    (s : ℕ) (ss : List ℕ) (hchain : CoprimeChain p (s::ss))
    (q : ℕ) [NeZero q] (hq : q = (s::ss).prod*p)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ)
    (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hprime : (6*2^(hs.length+(s::ss).length)*t^(2^(s::ss).length))^2 ≤ p)
    (hinterval : 2*p*t^(2^(s::ss).length) ≤ L)
    (hboundary : ∀ v ∈ s::ss,
      v*(t^(2^(s::ss).length))^2*t^(2^(s::ss).length) ≤ L) :
    ‖intervalSum A L (fun n => χ n*seq q c a hs n)‖ ≤ 4*(L : ℝ)/(t : ℝ) := by
  obtain ⟨hK,hKp,hsmall,hR⟩ :=
    scale_averaging_data p t (s::ss).length hs.length ht hprime
  exact (norm_interval_char_seq_le_iterated p L ((t^(2^(s::ss).length))^2)
    hK hKp s ss hchain q hq χ hχ c a hs A hc hdistinct hsmall).trans
    (iteratedBound_le_div_scale L _ p t (s::ss) hs.length ht
      (Nat.pos_of_ne_zero (NeZero.ne p)) hR hprime hinterval hboundary)

/-- Frequencies divisible by the terminal prime are explicitly put in the
trivial-bound branch. They are not passed to a nonzero-coefficient theorem. -/
theorem norm_interval_char_seq_frequency_split
    (p : ℕ) [NeZero p] [Fact p.Prime] (L t : ℕ) (ht : 1 ≤ t)
    (s : ℕ) (ss : List ℕ) (hchain : CoprimeChain p (s::ss))
    (q : ℕ) [NeZero q] (hq : q = (s::ss).prod*p)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (h b a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ)
    (hb : (b : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hprime : (6*2^(hs.length+(s::ss).length)*t^(2^(s::ss).length))^2 ≤ p)
    (hinterval : 2*p*t^(2^(s::ss).length) ≤ L)
    (hboundary : ∀ v ∈ s::ss,
      v*(t^(2^(s::ss).length))^2*t^(2^(s::ss).length) ≤ L) :
    ‖intervalSum A L (fun n => χ n*seq q (h*b) a hs n)‖ ≤
      if (h : ZMod p) = 0 then (L : ℝ) else 4*(L : ℝ)/(t : ℝ) := by
  split_ifs with hh
  · apply norm_intervalSum_le
    intro n
    rw [norm_mul, hχ, one_mul]
    exact norm_seq_le q (h*b) a hs n
  · apply norm_interval_char_seq_le_div_scale p L t ht s ss hchain q hq χ hχ
      (h*b) a hs A _ hdistinct hprime hinterval hboundary
    simpa only [Int.cast_mul] using mul_ne_zero hh hb

/-- Separation from the original interval scale controls both the terminal
period remainder and all finite shift boundaries, with integer floors. -/
theorem separated_interval_conditions (Q u gap p R : ℕ)
    (hu : 0 < u) (huQ : u ≤ Q) (hR : 1 ≤ R)
    (hgap : 8*u*R^3 ≤ gap) (hsep : gap*p ≤ Q) :
    2*p*R ≤ Q/u-Q/(2*u) ∧
      ∀ s ≤ p, s*R^2*R ≤ Q/u-Q/(2*u) := by
  let L := Q/u-Q/(2*u)
  have hL : Q ≤ 4*u*L := dyadic_length_lower Q u hu huQ
  have hh := Nat.mul_le_mul_right p hgap
  have hmain : 2*p*R^3 ≤ L := by
    have h : 4*u*(2*p*R^3) ≤ 4*u*L := by nlinarith
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hpow : R ≤ R^3 := le_self_pow hR (by omega)
  constructor
  · exact (Nat.mul_le_mul_left (2*p) hpow).trans hmain
  · intro s hsp
    have hh := Nat.mul_le_mul_right (R^3) hsp
    nlinarith

/-- The fixed integral BNPZ exponents are much larger than the conductor
iteration depth. This is a concrete comparison, not an asymptotic premise. -/
theorem bpz_exponent_margins (k : ℕ) (hk : 3 ≤ k) :
    2*(2^k+1) ≤ Erdos387.BPZScale.secondExp k ∧
    2*Erdos387.BPZScale.yExp k+3*2^k+1 ≤ Erdos387.BPZScale.gapExp k ∧
    3*k*Erdos387.BPZScale.yExp k+2 ≤ Erdos387.BPZScale.secondExp k := by
  have hA : 1 ≤ 3^k := Nat.one_le_pow _ _ (by omega)
  have h23 : 2^k ≤ 3^k := Nat.pow_le_pow_left (by omega) k
  have h99 : 1 ≤ k^99 := Nat.one_le_pow _ _ (by omega)
  have h96 : 3 ≤ k^96 := hk.trans (le_self_pow (by omega) (by omega))
  have h98 : 9 ≤ k^98 := calc
    9 ≤ k^2 := by nlinarith
    _ ≤ k^98 := Nat.pow_le_pow_right (by omega) (by omega)
  have h99' : 9*k ≤ k^99 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right k h98
  dsimp [Erdos387.BPZScale.secondExp, Erdos387.BPZScale.yExp,
    Erdos387.BPZScale.gapExp]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- For the actual BNPZ scale, the prime and separation inequalities needed
by conductor iteration follow from the second-prime and gap thresholds. -/
theorem bpz_scale_conditions (t k r p u : ℕ) (hk : 3 ≤ k)
    (ht : 6*2^k ≤ t) (hr : r ≤ k)
    (hp : Erdos387.BPZScale.secondMin t k ≤ p)
    (hu : u ≤ (Erdos387.BPZScale.y t k)^2) :
    (6*2^r*t^(2^r))^2 ≤ p ∧
      8*u*(t^(2^r))^3 ≤ Erdos387.BPZScale.gap t k := by
  obtain ⟨hsecond,hgap,_⟩ := bpz_exponent_margins k hk
  have htwo : 1 ≤ 2^k := Nat.one_le_pow _ _ (by omega)
  have ht1 : 1 ≤ t := by omega
  have h8 : 8 ≤ t := by
    have hh : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by omega) hk
    norm_num at hh
    omega
  have hrpow : 2^r ≤ 2^k := Nat.pow_le_pow_right (by omega) hr
  have hR : t^(2^r) ≤ t^(2^k) := Nat.pow_le_pow_right ht1 hrpow
  have hcoef : 6*2^r ≤ t := (Nat.mul_le_mul_left 6 hrpow).trans ht
  constructor
  · calc
      (6*2^r*t^(2^r))^2 ≤ (t*t^(2^k))^2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hcoef hR) 2
      _ = t^(2*(2^k+1)) := by rw [← pow_succ', ← pow_mul]; congr 1; omega
      _ ≤ t^Erdos387.BPZScale.secondExp k := Nat.pow_le_pow_right ht1 hsecond
      _ ≤ p := hp
  · calc
      8*u*(t^(2^r))^3 ≤ t*(t^Erdos387.BPZScale.yExp k)^2*(t^(2^k))^3 :=
        Nat.mul_le_mul (Nat.mul_le_mul h8 hu) (Nat.pow_le_pow_left hR 3)
      _ = t^(2*Erdos387.BPZScale.yExp k+3*2^k+1) := by
        simp only [← pow_mul, ← pow_succ', ← pow_add]
        congr 1
        omega
      _ ≤ t^Erdos387.BPZScale.gapExp k := Nat.pow_le_pow_right ht1 hgap

/-- Selecting the largest remaining prime from precisely the separated
certificate data.  No smoothness property of the small factors is used. -/
theorem exists_maximal_remaining_prime (k second gap : ℕ) (q : Fin k → ℕ)
    (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀) (hsecond : 1 ≤ second)
    (hj : second < q j₀)
    (hq : ∀ i, q i = 1 ∨ (q i).Prime)
    (hgap : ∀ j, j ≠ i₀ → gap*q j ≤ q i₀) :
    ∃ j : Fin k, j ≠ i₀ ∧ (q j).Prime ∧ second < q j ∧
      gap*q j ≤ q i₀ ∧ ∀ i, i ≠ i₀ → q i ≤ q j := by
  classical
  have hnon : (Finset.univ.erase i₀).Nonempty :=
    ⟨j₀, Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩⟩
  obtain ⟨j,hjmem,hmax⟩ := Finset.exists_max_image (Finset.univ.erase i₀) q hnon
  have hji := (Finset.mem_erase.mp hjmem).1
  have hmax' : ∀ i, i ≠ i₀ → q i ≤ q j := by
    intro i hi
    exact hmax i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hjlarge : second < q j := hj.trans_le (hmax' j₀ (Ne.symm hij))
  have hp : (q j).Prime := by
    rcases hq j with h | h
    · omega
    · exact h
  exact ⟨j,hji,hp,hjlarge,hgap j hji,hmax'⟩

/-- Turning the finite set of remaining distinct primes into the exact list
used by conductor iteration. Removing its largest prime and prepending the
small composite factor preserves the original number of prime factors as
an upper bound for the number of stripping steps. -/
theorem prime_set_stripping_data (P : Finset ℕ) (p s₀ : ℕ)
    (hp : p ∈ P) (hprime : ∀ v ∈ P, v.Prime)
    (hmax : ∀ v ∈ P, v ≤ p) (hs₀ : 0 < s₀)
    (hcop : Nat.Coprime s₀ (∏ v ∈ P, v)) :
    ∃ ss : List ℕ, (s₀::ss).length = P.card ∧
      ss.prod*p = ∏ v ∈ P, v ∧ Squarefree (ss.prod*p) ∧
      CoprimeChain p (s₀::ss) ∧ ∀ v ∈ ss, v ≤ p := by
  let ss := (P.erase p).toList
  have hprod : ss.prod*p = ∏ v ∈ P, v := by
    dsimp [ss]
    rw [Finset.prod_toList]
    exact Finset.prod_erase_mul P id hp
  have hsq : Squarefree (ss.prod*p) := by
    rw [hprod]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro v hv w hw hvw
      change IsRelPrime v w
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprime v hv) (hprime w hw)).mpr hvw
    · intro v hv
      exact (hprime v hv).squarefree
  refine ⟨ss, ?_, hprod, hsq, ?_, ?_⟩
  · simpa only [List.length_cons, ss, Finset.length_toList] using Finset.card_erase_add_one hp
  · exact ⟨hs₀, by simpa only [hprod] using hcop, coprimeChain_of_squarefree p ss hsq⟩
  · intro v hv
    exact hmax v (Finset.mem_of_mem_erase (Finset.mem_toList.mp hv))

/-- Distinct original indices below p give the required nonzero CRT
coefficient. The same elementary adapter applies to distinct Type-II
multipliers once their size is known to be below p. -/
theorem difference_ne_zero_mod (p i j : ℕ) [NeZero p]
    (hi : i < p) (hj : j < p) (hij : i ≠ j)
    (b : ℤ) (hb : (b : ZMod p) = (j : ZMod p)) :
    ((b-(i : ℤ) : ℤ) : ZMod p) ≠ 0 := by
  rw [Int.cast_sub, Int.cast_natCast, hb, sub_ne_zero]
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hi] at hv
  exact hij hv.symm

/-- The exact §10 dyadic interval, specialized to the already-defined BNPZ
integral scale. The small composite factor need not be squarefree: it only
needs to be coprime to the squarefree remaining product. -/
theorem norm_bpz_dyadic_char_seq_le
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (t k Q u s₀ : ℕ) (ss : List ℕ) (hk : 3 ≤ k) (ht : 6*2^k ≤ t)
    (hdepth : (s₀::ss).length ≤ k)
    (hs₀ : 0 < s₀) (hcop : Nat.Coprime s₀ (ss.prod*p))
    (hsq : Squarefree (ss.prod*p))
    (hmax : ∀ s ∈ ss, s ≤ p)
    (hsmallfactor : s₀ ≤ t^(3*k*Erdos387.BPZScale.yExp k+2))
    (hp : Erdos387.BPZScale.secondMin t k ≤ p)
    (hu : 0 < u) (huQ : u ≤ Q) (huY : u ≤ (Erdos387.BPZScale.y t k)^2)
    (hsep : Erdos387.BPZScale.gap t k*p ≤ Q)
    (q : ℕ) [NeZero q] (hq : q = (s₀::ss).prod*p)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a A : ℤ) (hc : (c : ZMod p) ≠ 0) :
    ‖intervalSum A (Q/u-Q/(2*u)) (fun n => χ n*seq q c a [] n)‖ ≤
      4*((Q/u-Q/(2*u) : ℕ) : ℝ)/(t : ℝ) := by
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^k := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨hprime,hgap⟩ := bpz_scale_conditions t k (s₀::ss).length p u hk ht hdepth hp huY
  have hR : 1 ≤ t^(2^(s₀::ss).length) := Nat.one_le_pow _ _ ht1
  obtain ⟨hinterval,hboundary⟩ := separated_interval_conditions Q u
    (Erdos387.BPZScale.gap t k) p (t^(2^(s₀::ss).length)) hu huQ hR hgap hsep
  have hs₀p : s₀ ≤ p := hsmallfactor.trans
    ((Nat.pow_le_pow_right ht1 (bpz_exponent_margins k hk).2.2).trans hp)
  have hchain : CoprimeChain p (s₀::ss) :=
    ⟨hs₀,hcop,coprimeChain_of_squarefree p ss hsq⟩
  apply norm_interval_char_seq_le_div_scale p _ t ht1 s₀ ss hchain q hq
    χ hχ c a [] A hc
  · simp
  · simpa only [List.length_nil, Nat.zero_add] using hprime
  · exact hinterval
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hboundary v hs₀p
    · exact hboundary v (hmax v hv)

end Erdos387Proof.SeparatedConductorBound
