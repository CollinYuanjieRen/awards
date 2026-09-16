import Erdos387Proof.PeriodicStripping
import Erdos387Proof.MaskedReciprocalPhase
import Erdos387Proof.TerminalPrimeCancellation
import Erdos387Proof.PeriodicCompletion

/-!
# Stripping a coprime factor from masked reciprocal phases

This is a finite, source-facing form of the conductor-reduction step in
BNPZ arXiv:2605.21221v2, Lemma 10.2. Original denominator masks are retained.
Only additive unit characters, not arbitrary varying weights, disappear
from the norms of the correlations.
-/

namespace Erdos387Proof.ConductorStripping

open scoped BigOperators ComplexConjugate
open PeriodicStripping MaskedReciprocalPhase

noncomputable def nextCorrelationMass (t : ℕ) [NeZero t] (c a : ℤ)
    (hs : List (ℤ × ℤ)) (A : ℤ) (L K s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
    ‖intervalSum A L (seq t c a (((j*s : ℕ),(i*s : ℕ))::hs))‖

theorem correlationMass_seq_eq (t : ℕ) [NeZero t] (c a : ℤ)
    (hs : List (ℤ × ℤ)) (A : ℤ) (L K s : ℕ) :
    correlationMass A L K s (seq t c a hs) =
      nextCorrelationMass t c a hs A L K s := by
  unfold correlationMass nextCorrelationMass intervalSum
  simp_rw [seq_cons]

/-- Exact one-step conductor reduction, with no terminal cancellation premise. -/
theorem norm_interval_seq_sq_le (s t : ℕ) [NeZero s] [NeZero t]
    (hcop : Nat.Coprime s t) (c a : ℤ) (hs : List (ℤ × ℤ))
    (A : ℤ) (L K : ℕ) (hK : 0 < K) :
    ‖intervalSum A L (seq (s*t) c a hs)‖^2 ≤
      2*(L : ℝ)^2/K + (4*L/(K : ℝ)^2) *
        nextCorrelationMass t (c*Nat.gcdA s t) a hs A L K s +
      2*(s : ℝ)^2*((K : ℝ)-1)^2 := by
  have h := interval_periodic_factor_sq_le A L K s hK
    (seq s (c*Nat.gcdB s t) a hs) (seq t (c*Nat.gcdA s t) a hs)
    (seq_periodic s _ a hs) (norm_seq_le s _ a hs) (norm_seq_le t _ a hs)
  have heq : intervalSum A L (seq (s*t) c a hs) =
      intervalSum A L (fun n => seq s (c*Nat.gcdB s t) a hs n *
        seq t (c*Nat.gcdA s t) a hs n) := by
    unfold intervalSum
    exact Finset.sum_congr rfl fun n _ => seq_mul s t hcop c a hs _
  rw [← heq, correlationMass_seq_eq] at h
  exact h

/-- A unit additive character contributes only a constant to each correlation. -/
theorem char_correlation (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (b : ℤ → ℂ) (u v n : ℤ) :
    (χ (n+u)*b (n+u)) * conj (χ (n+v)*b (n+v)) =
      (χ u * conj (χ v)) * (b (n+u) * conj (b (n+v))) := by
  have hn : χ n * conj (χ n) = 1 := by
    rw [Complex.mul_conj', hχ]
    norm_num
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  simp only [map_mul]
  calc
    _ = (χ n * conj (χ n)) * (χ u * conj (χ v)) *
        (b (n+u) * conj (b (n+v))) := by ring
    _ = _ := by rw [hn, one_mul]

theorem norm_interval_char_correlation_eq (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (b : ℤ → ℂ) (u v A : ℤ) (L : ℕ) :
    ‖intervalSum A L (fun n =>
      (χ (n+u)*b (n+u)) * conj (χ (n+v)*b (n+v)))‖ =
      ‖intervalSum A L (fun n => b (n+u) * conj (b (n+v)))‖ := by
  unfold intervalSum
  simp_rw [char_correlation χ hχ]
  rw [← Finset.mul_sum, norm_mul]
  simp [hχ]

theorem correlationMass_char_eq (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (b : ℤ → ℂ) (A : ℤ) (L K s : ℕ) :
    correlationMass A L K s (fun n => χ n*b n) = correlationMass A L K s b := by
  unfold correlationMass
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  exact norm_interval_char_correlation_eq χ hχ b _ _ A L

/-- The initial unit additive character disappears after this single step. -/
theorem norm_interval_char_seq_sq_le (s t : ℕ) [NeZero s] [NeZero t]
    (hcop : Nat.Coprime s t) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ) (L K : ℕ) (hK : 0 < K) :
    ‖intervalSum A L (fun n => χ n*seq (s*t) c a hs n)‖^2 ≤
      2*(L : ℝ)^2/K + (4*L/(K : ℝ)^2) *
        nextCorrelationMass t (c*Nat.gcdA s t) a hs A L K s +
      2*(s : ℝ)^2*((K : ℝ)-1)^2 := by
  have hb (n : ℤ) : ‖χ n*seq t (c*Nat.gcdA s t) a hs n‖ ≤ 1 := by
    rw [norm_mul, hχ, one_mul]
    exact norm_seq_le t _ a hs n
  have h := interval_periodic_factor_sq_le A L K s hK
    (seq s (c*Nat.gcdB s t) a hs)
    (fun n => χ n*seq t (c*Nat.gcdA s t) a hs n)
    (seq_periodic s _ a hs) (norm_seq_le s _ a hs) hb
  have heq : intervalSum A L (fun n => χ n*seq (s*t) c a hs n) =
      intervalSum A L (fun n => seq s (c*Nat.gcdB s t) a hs n *
        (χ n*seq t (c*Nat.gcdA s t) a hs n)) := by
    unfold intervalSum
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only
    rw [seq_mul s t hcop]
    ring
  rw [← heq, correlationMass_char_eq χ hχ, correlationMass_seq_eq] at h
  exact h

/-- A finite uniform bound on the next-stage sums bounds the correlation mass. -/
theorem nextCorrelationMass_le (t : ℕ) [NeZero t] (c a : ℤ)
    (hs : List (ℤ × ℤ)) (A : ℤ) (L K s : ℕ) (B : ℝ)
    (hB : ∀ j < K, ∀ i < j,
      ‖intervalSum A L (seq t c a (((j*s : ℕ),(i*s : ℕ))::hs))‖ ≤ B) :
    nextCorrelationMass t c a hs A L K s ≤
      ((K*(K-1)/2 : ℕ) : ℝ)*B := by
  unfold nextCorrelationMass
  calc
    _ ≤ ∑ j ∈ Finset.range K, ∑ _i ∈ Finset.range j, B := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact hB j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
    _ = ((K*(K-1)/2 : ℕ) : ℝ)*B := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_mul, ← Nat.cast_sum, Finset.sum_range_id]

/-- Squared recurrence, convenient for a finite conductor induction.
Its next-stage hypothesis concerns sums over the remaining conductor. -/
theorem norm_interval_seq_sq_le_of_next (s t : ℕ) [NeZero s] [NeZero t]
    (hcop : Nat.Coprime s t) (c a : ℤ) (hs : List (ℤ × ℤ))
    (A : ℤ) (L K : ℕ) (hK : 0 < K) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < K, ∀ i < j,
      ‖intervalSum A L (seq t (c*Nat.gcdA s t) a
        (((j*s : ℕ),(i*s : ℕ))::hs))‖ ≤ B) :
    ‖intervalSum A L (seq (s*t) c a hs)‖^2 ≤
      2*(L : ℝ)^2/K + 2*L*B + 2*(s : ℝ)^2*((K : ℝ)-1)^2 := by
  have h := norm_interval_seq_sq_le s t hcop c a hs A L K hK
  have hm := nextCorrelationMass_le t (c*Nat.gcdA s t) a hs A L K s B hB
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
  linarith


/-- The exact sharp complete-prime envelope from the terminal adapter. -/
noncomputable def primeBound (p j : ℕ) : ℝ :=
  ((2*2^j-1 : ℕ) : ℝ)*Real.sqrt (p : ℝ) + (2^j : ℕ)

/-- An explicit finite recursive bound, terminating at the proved prime sum. -/
noncomputable def iteratedBound (L K p : ℕ) : List ℕ → ℕ → ℝ
  | [], j => ((L/p : ℕ) : ℝ)*primeBound p j + (L%p : ℕ)
  | s::ss, j => Real.sqrt (2*(L : ℝ)^2/K + 2*L*iteratedBound L K p ss (j+1) +
      2*(s : ℝ)^2*((K : ℝ)-1)^2)

/-- At each stage the removed factor is positive and coprime to what remains. -/
def CoprimeChain (p : ℕ) : List ℕ → Prop
  | [] => True
  | s::ss => 0 < s ∧ Nat.Coprime s (ss.prod*p) ∧ CoprimeChain p ss

theorem CoprimeChain.prod_pos {p : ℕ} {ss : List ℕ} (h : CoprimeChain p ss) :
    0 < ss.prod := by
  induction ss with
  | nil => simp
  | cons s ss ih => exact Nat.mul_pos h.1 (ih h.2.2)

theorem iteratedBound_nonneg (L K p : ℕ) (ss : List ℕ) (j : ℕ) :
    0 ≤ iteratedBound L K p ss j := by
  cases ss with
  | nil => simp only [iteratedBound, primeBound]; positivity
  | cons s ss => exact Real.sqrt_nonneg _

/-- Converting a complete interval to the complete residue sum loses no term. -/
theorem intervalSum_zero_prime_eq (p : ℕ) [NeZero p] (f : ℤ → ℂ) :
    intervalSum 0 p f = ∑ x : ZMod p, f (x.val : ℤ) := by
  unfold intervalSum
  simp only [zero_add]
  symm
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_range.mpr x.val_lt
  · intro x hx y hy hxy
    exact ZMod.val_injective p hxy
  · intro n hn
    refine ⟨(n : ZMod p), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro x hx
    rfl

/-- The base of conductor iteration uses the actual proved prime cancellation. -/
theorem norm_interval_seq_prime_le (p : ℕ) [NeZero p] [Fact p.Prime]
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ) (L K : ℕ)
    (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^hs.length < p) :
    ‖intervalSum A L (seq p c a hs)‖ ≤ iteratedBound L K p [] hs.length := by
  apply PeriodicCompletion.norm_intervalSum_le_div_mul_add_mod
    A L p (seq p c a hs) (primeBound p hs.length)
    (Nat.pos_of_ne_zero (NeZero.ne p)) (seq_periodic p c a hs) (norm_seq_le p c a hs)
  rw [intervalSum_zero_prime_eq]
  exact TerminalPrimeCancellation.norm_sum_seq_le p c a hs hc hdistinct hsmall

/-- Each Bézout twist stays nonzero at every prime dividing the remaining modulus. -/
theorem twist_ne_zero (s t p : ℕ) [NeZero p] [Fact p.Prime]
    (hcop : Nat.Coprime s t) (hp : p ∣ t) (c : ℤ) (hc : (c : ZMod p) ≠ 0) :
    ((c*Nat.gcdA s t : ℤ) : ZMod p) ≠ 0 := by
  have ht : (t : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff t p).mpr hp
  have hb : (1 : ℤ) = (s : ℤ)*Nat.gcdA s t + (t : ℤ)*Nat.gcdB s t := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab s t
  have hz : (1 : ZMod p) = (s : ZMod p)*(Nat.gcdA s t : ZMod p) := by
    have := congrArg (fun n : ℤ => (n : ZMod p)) hb
    simpa [ht] using this
  have hg : (Nat.gcdA s t : ZMod p) ≠ 0 := by
    intro h
    simp [h] at hz
  rw [Int.cast_mul]
  exact mul_ne_zero hc hg

/-- Distinct averaging indices give distinct paired shifts at the final prime.
Only K≤p is needed; the raw product K*s may exceed p. -/
theorem paired_shift_ne (p s K j i : ℕ) [NeZero p] [Fact p.Prime]
    (hsp : Nat.Coprime s p) (hKp : K ≤ p) (hj : j < K) (hi : i < j) :
    ((j*s : ℕ) : ZMod p) ≠ ((i*s : ℕ) : ZMod p) := by
  have hs : (s : ZMod p) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime s p).mpr hsp).ne_zero
  intro he
  simp only [Nat.cast_mul] at he
  have hji : (j : ZMod p) = (i : ZMod p) := mul_right_cancel₀ hs he
  have hv := congrArg ZMod.val hji
  rw [ZMod.val_natCast_of_lt (hj.trans_le hKp),
    ZMod.val_natCast_of_lt ((hi.trans hj).trans_le hKp)] at hv
  omega

/-- Finite conductor iteration with every terminal hypothesis discharged.
The only bound at the end is the proved sharp complete-prime theorem. -/
theorem norm_interval_seq_le_iterated
    (p : ℕ) [NeZero p] [Fact p.Prime] (L K : ℕ) (hK : 0 < K) (hKp : K ≤ p)
    (ss : List ℕ) (hchain : CoprimeChain p ss)
    (q : ℕ) [NeZero q] (hq : q = ss.prod*p)
    (c a : ℤ) (hs : List (ℤ × ℤ)) (A : ℤ)
    (hc : (c : ZMod p) ≠ 0)
    (hdistinct : ∀ uv ∈ hs, (uv.1 : ZMod p) ≠ (uv.2 : ZMod p))
    (hsmall : 2^(hs.length+ss.length) < p) :
    ‖intervalSum A L (seq q c a hs)‖ ≤ iteratedBound L K p ss hs.length := by
  induction ss generalizing q c hs with
  | nil =>
    have hqp : q = p := by simpa using hq
    clear hq
    subst q
    exact norm_interval_seq_prime_le p c a hs A L K hc hdistinct (by simpa using hsmall)
  | cons s ss ih =>
    rcases hchain with ⟨hspos,hcop,hchain⟩
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
    have hnext (j : ℕ) (hj : j < K) (i : ℕ) (hi : i < j) :
        ‖intervalSum A L (seq t (c*Nat.gcdA s t) a
          (((j*s : ℕ),(i*s : ℕ))::hs))‖ ≤ iteratedBound L K p ss (hs.length+1) := by
      have hd : ∀ uv ∈ (((j*s : ℕ),(i*s : ℕ))::hs : List (ℤ × ℤ)),
          (uv.1 : ZMod p) ≠ (uv.2 : ZMod p) := by
        intro uv huv
        rcases List.mem_cons.mp huv with rfl | huv
        · simpa using paired_shift_ne p s K j i hsp hKp hj hi
        · exact hdistinct uv huv
      have hsm : 2^((((j*s : ℕ),(i*s : ℕ))::hs : List (ℤ × ℤ)).length+ss.length) < p := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsmall
      simpa only [List.length_cons] using
        ih hchain t rfl (c*Nat.gcdA s t) (((j*s : ℕ),(i*s : ℕ))::hs) hc' hd hsm
    have hsq := norm_interval_seq_sq_le_of_next s t hcop c a hs A L K hK
      (iteratedBound L K p ss (hs.length+1))
      (iteratedBound_nonneg L K p ss (hs.length+1)) hnext
    have hr : 0 ≤ 2*(L : ℝ)^2/K + 2*L*iteratedBound L K p ss (hs.length+1) +
        2*(s : ℝ)^2*((K : ℝ)-1)^2 := by
      have := iteratedBound_nonneg L K p ss (hs.length+1)
      positivity
    change ‖intervalSum A L (seq (s*t) c a hs)‖ ≤ Real.sqrt _
    have he := Real.sq_sqrt hr
    have hn := Real.sqrt_nonneg (2*(L : ℝ)^2/K +
      2*L*iteratedBound L K p ss (hs.length+1) + 2*(s : ℝ)^2*((K : ℝ)-1)^2)
    nlinarith [norm_nonneg (intervalSum A L (seq (s*t) c a hs))]

end Erdos387Proof.ConductorStripping
