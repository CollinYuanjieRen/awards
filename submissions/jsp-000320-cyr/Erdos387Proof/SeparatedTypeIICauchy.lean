import Erdos387Proof.SeparatedProductWindow

/-!
# Finite bounded-weight Type-II Cauchy expansion

BNPZ §10, the displayed Type-II correlation expansion. This file keeps
original conductor-unit masks and terminal-prime exceptional frequencies.
The finite algebra never discards an arbitrary two-variable weight.
-/

namespace Erdos387Proof.SeparatedTypeIICauchy

open scoped BigOperators ComplexConjugate
open SeparatedProductWindow SeparatedCertificatePhase
open MaskedReciprocalPhase PeriodicStripping SeparatedConductorBound

/-- Cauchy after removing ONLY a proved one-bounded single-variable weight. -/
theorem norm_sum_mul_sq_le_finset {α : Type*} (S : Finset α) (a b : α → ℂ)
    (ha : ∀ x ∈ S, ‖a x‖ ≤ 1) :
    ‖∑ x ∈ S, a x*b x‖^2 ≤ (S.card : ℝ)*∑ x ∈ S, ‖b x‖^2 := by
  have hn : ‖∑ x ∈ S, a x*b x‖ ≤ ∑ x ∈ S, ‖b x‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha x hx)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun x => ‖b x‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

/-- Exact complex square expansion, before taking any correlation norms. -/
theorem norm_sum_sq_eq_re_sum {α : Type*} (S : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ S, f x‖^2 = (∑ x ∈ S, ∑ z ∈ S, f x*conj (f z)).re := by
  have he : (∑ x ∈ S, f x)*conj (∑ z ∈ S, f z) =
      ∑ x ∈ S, ∑ z ∈ S, f x*conj (f z) := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [← he, Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem sum_norm_sum_sq_eq {α β : Type*} (U : Finset α) (V : Finset β) (f : α → β → ℂ) :
    (∑ m ∈ V, ‖∑ u ∈ U, f u m‖^2) =
      ∑ u ∈ U, ∑ v ∈ U, (∑ m ∈ V, f u m*conj (f v m)).re := by
  simp only [norm_sum_sq_eq_re_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]

/-- Separated u-weights factor out of the correlation. -/
theorem weighted_correlation_eq {β : Type*} (V : Finset β) (a b : ℂ) (f g : β → ℂ) :
    (∑ m ∈ V, (a*f m)*conj (b*g m)) =
      (a*conj b)*(∑ m ∈ V, f m*conj (g m)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_mul]
  ring

theorem weighted_correlation_re_le {β : Type*} (V : Finset β) (a b : ℂ) (f g : β → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    (∑ m ∈ V, (a*f m)*conj (b*g m)).re ≤ ‖∑ m ∈ V, f m*conj (g m)‖ := by
  rw [weighted_correlation_eq]
  apply (Complex.re_le_norm _).trans
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hab : ‖a‖*‖b‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  exact mul_le_of_le_one_left (norm_nonneg _) hab

/-- The diagonal is bounded before estimating off-diagonal correlations. -/
theorem diagonal_re_le_card {β : Type*} (V : Finset β) (f : β → ℂ)
    (hf : ∀ m ∈ V, ‖f m‖ ≤ 1) :
    (∑ m ∈ V, f m*conj (f m)).re ≤ V.card := by
  simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  calc
    _ ≤ ∑ _m ∈ V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have := hf m hm
      nlinarith [norm_nonneg (f m)]
    _ = _ := by simp

/-- The exact finite Type-II inequality. Only alpha and beta are discarded
by their proved one-variable norm bounds; F remains in every correlation. -/
theorem typeII_cauchy {α β : Type*} [DecidableEq α] (U : Finset α) (V : Finset β)
    (a : α → ℂ) (b : β → ℂ) (F : α → β → ℂ)
    (ha : ∀ u ∈ U, ‖a u‖ ≤ 1) (hb : ∀ m ∈ V, ‖b m‖ ≤ 1)
    (hF : ∀ u ∈ U, ∀ m ∈ V, ‖F u m‖ ≤ 1) :
    ‖∑ u ∈ U, ∑ m ∈ V, a u*b m*F u m‖^2 ≤
      (V.card : ℝ)*((U.card : ℝ)*V.card +
        ∑ u ∈ U, ∑ v ∈ U.erase u, ‖∑ m ∈ V, F u m*conj (F v m)‖) := by
  classical
  have he : (∑ u ∈ U, ∑ m ∈ V, a u*b m*F u m) =
      ∑ m ∈ V, b m*(∑ u ∈ U, a u*F u m) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [he]
  apply (norm_sum_mul_sq_le_finset V b (fun m => ∑ u ∈ U, a u*F u m) hb).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [sum_norm_sum_sq_eq U V]
  calc
    _ ≤ ∑ u ∈ U, ((V.card : ℝ) +
        ∑ v ∈ U.erase u, ‖∑ m ∈ V, F u m*conj (F v m)‖) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [← Finset.sum_erase_add _ _ hu, add_comm (V.card : ℝ)]
      apply add_le_add
      · apply Finset.sum_le_sum
        intro v hv
        exact weighted_correlation_re_le V (a u) (a v) (F u) (F v)
          (ha u hu) (ha v (Finset.mem_of_mem_erase hv))
      · apply diagonal_re_le_card V
        intro m hm
        rw [norm_mul]
        have hau := ha u hu
        have hfum := hF u hu m hm
        nlinarith [norm_nonneg (a u), norm_nonneg (F u m)]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Multiplicativity of the totalized inverse is used only on units. -/
theorem inv_mul_of_units (q : ℕ) (x z : ZMod q) (hx : IsUnit x) (hz : IsUnit z) :
    (x*z)⁻¹ = x⁻¹*z⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    (x*z)*(x⁻¹*z⁻¹) = (x*x⁻¹)*(z*z⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit x hx, ZMod.mul_inv_of_unit z hz, one_mul]

/-- The reciprocal difference formula, with both original unit hypotheses. -/
theorem inv_sub_inv_of_units (q : ℕ) (x z : ZMod q) (hx : IsUnit x) (hz : IsUnit z) :
    x⁻¹-z⁻¹ = (x*z)⁻¹*(z-x) := by
  calc
    x⁻¹-z⁻¹ = (x*z)⁻¹*(x*z)*(x⁻¹-z⁻¹) := by
      rw [ZMod.inv_mul_of_unit (x*z) (hx.mul hz), one_mul]
    _ = (x*z)⁻¹*(z*(x*x⁻¹)-x*(z*z⁻¹)) := by ring
    _ = _ := by rw [ZMod.mul_inv_of_unit x hx, ZMod.mul_inv_of_unit z hz]; ring

/-- Projection to a divisor modulus commutes with inverse on the unit locus. -/
theorem castHom_inv_of_unit (q p : ℕ) (hp : p ∣ q) (x : ZMod q) (hx : IsUnit x) :
    ZMod.castHom hp (ZMod p) (x⁻¹) = (ZMod.castHom hp (ZMod p) x)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

/-- Canonical integer lift of the actual Type-II reciprocal coefficient. -/
noncomputable def pairCoefficient (q : ℕ) (c : ℤ) (u v : ℕ) : ℤ :=
  (((c : ZMod q)*((u*v : ℕ) : ZMod q)⁻¹*((v : ZMod q)-(u : ZMod q))).val : ℤ)

theorem pairCoefficient_cast (q : ℕ) [NeZero q] (c : ℤ) (u v : ℕ) :
    (pairCoefficient q c u v : ZMod q) =
      (c : ZMod q)*((u*v : ℕ) : ZMod q)⁻¹*((v : ZMod q)-(u : ZMod q)) := by
  simp [pairCoefficient]

theorem pairCoefficient_cast_divisor (q p : ℕ) [NeZero q] (hp : p ∣ q)
    (c : ℤ) (u v : ℕ) (huv : Nat.Coprime (u*v) q) :
    (pairCoefficient q c u v : ZMod p) =
      (c : ZMod p)*((u*v : ℕ) : ZMod p)⁻¹*((v : ZMod p)-(u : ZMod p)) := by
  have hx : IsUnit ((u*v : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr huv
  have he := congrArg (ZMod.castHom hp (ZMod p)) (pairCoefficient_cast q c u v)
  simpa only [map_mul, map_sub, map_intCast, map_natCast,
    castHom_inv_of_unit q p hp _ hx] using he

/-- Exact zero-extended paired correlation. If m is not a unit, BOTH
original denominator masks vanish and the new mask also vanishes. -/
theorem seq_product_correlation (q : ℕ) [NeZero q] (c : ℤ) (u v : ℕ)
    (hu : Nat.Coprime u q) (hv : Nat.Coprime v q) (m : ℤ) :
    seq q c 0 [] ((u : ℤ)*m)*conj (seq q c 0 [] ((v : ℤ)*m)) =
      seq q (pairCoefficient q c u v) 0 [] m := by
  classical
  have hu' : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hu
  have hv' : IsUnit (v : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hv
  unfold seq
  simp only [good, zero_add, Int.cast_mul, Int.cast_natCast, IsUnit.mul_iff,
    hu', hv', true_and]
  by_cases hm : IsUnit (m : ZMod q)
  · simp only [hm, if_true, phase, zero_add, Int.cast_mul, Int.cast_natCast]
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    rw [inv_mul_of_units q _ _ hu' hm, inv_mul_of_units q _ _ hv' hm,
      pairCoefficient_cast]
    have hi := inv_sub_inv_of_units q (u : ZMod q) (v : ZMod q) hu' hv'
    push_cast
    calc
      _ = (c : ZMod q)*((u : ZMod q)⁻¹-(v : ZMod q)⁻¹)*(m : ZMod q)⁻¹ := by ring
      _ = _ := by rw [hi]; ring
  · simp [hm]

/-- A unit linear character remains a unit linear character after pairing. -/
theorem linear_seq_product_correlation (q : ℕ) [NeZero q] (c : ℤ) (u v : ℕ)
    (hu : Nat.Coprime u q) (hv : Nat.Coprime v q)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) (m : ℤ) :
    (χ ((u : ℤ)*m)*seq q c 0 [] ((u : ℤ)*m))*
      conj (χ ((v : ℤ)*m)*seq q c 0 [] ((v : ℤ)*m)) =
      (χ.mulShift ((u : ℤ)-(v : ℤ))) m*seq q (pairCoefficient q c u v) 0 [] m := by
  calc
    _ = (χ ((u : ℤ)*m)*conj (χ ((v : ℤ)*m)))*
        (seq q c 0 [] ((u : ℤ)*m)*conj (seq q c 0 [] ((v : ℤ)*m))) := by
      simp only [map_mul]
      ring
    _ = _ := by
      have hc : conj (χ ((v : ℤ)*m)) = χ (-((v : ℤ)*m)) := by
        rw [AddChar.map_neg_eq_inv]
        exact (RCLike.inv_eq_conj (hχ _)).symm
      rw [seq_product_correlation q c u v hu hv m, hc, ← AddChar.map_add_eq_mul]
      congr 1
      change χ _ = χ (((u : ℤ)-(v : ℤ))*m)
      congr 1
      ring

/-- A terminal-prime exceptional frequency is never passed to the
nonzero-coefficient cancellation theorem. -/
theorem certificate_pairCoefficient_ne_zero
    {B K n t medium g : ℕ} {S : Erdos387.CoverBPZ.BPZSection6Input B K}
    (C : CertificatePhaseData S n (Erdos387.BPZScale.y t S.k) medium
      (Erdos387.BPZScale.secondMin t S.k) (Erdos387.BPZScale.gap t S.k) g)
    (ht : 1 ≤ t) (b : ℕ)
    (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (u v : ℕ) (hu : u ≤ (Erdos387.BPZScale.y t S.k)^2)
    (hv : v ≤ (Erdos387.BPZScale.y t S.k)^2) (hne : u ≠ v)
    (huv : Nat.Coprime (u*v) C.modulus) :
    (pairCoefficient C.modulus (h*((b : ℤ)-C.i₀.val)) u v : ZMod (C.q C.j)) ≠ 0 := by
  rw [pairCoefficient_cast_divisor C.modulus (C.q C.j) C.terminal_dvd_modulus _ u v huv]
  simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using
    C.typeII_coefficient_ne_zero ht b hb h hh u v hu hv hne huv

/-- The actual containing rectangle is longer than the proved base
interval. This transfers LOWER bounds; it does not infer a short-interval
bound from a long-interval bound. -/
theorem base_length_le_rectangle (Q U : ℕ) :
    Q/U-Q/(2*U) ≤ Q/U-Q/(4*U) := by
  have hh : Q/(4*U) ≤ Q/(2*U) := by
    have := Nat.div_le_self (Q/(2*U)) 2
    simpa only [Nat.div_div_eq_div_mul, show (2*U)*2=4*U by ring] using this
  exact Nat.sub_le_sub_left hh _

/-- Exact transfer from a natural Ioc interval to the integer intervalSum
convention, including both endpoints. -/
theorem sum_Ioc_eq_intervalSum (A B : ℕ) (f : ℤ → ℂ) :
    (∑ m ∈ Finset.Ioc A B, f (m : ℤ)) = intervalSum ((A : ℤ)+1) (B-A) f := by
  have he : Finset.Ioc A B = Finset.Ico (A+1) (B+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_add_right, intervalSum]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1

/-- Concrete certificate phase saving on the ACTUAL dyadic containing
rectangle length. Every interval/shift boundary obligation is discharged
from the existing BPZ arithmetic scale. -/
theorem certificate_norm_rectangle_phase_le
    {B K n t medium g : ℕ} {S : Erdos387.CoverBPZ.BPZSection6Input B K}
    (C : CertificatePhaseData S n (Erdos387.BPZScale.y t S.k) medium
      (Erdos387.BPZScale.secondMin t S.k) (Erdos387.BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : Erdos387.CoverBPZ.refinementModulus S ≤ t)
    (Q U : ℕ) (hQ : C.q C.i₀ ≤ Q) (hU : 0 < U) (hUQ : U ≤ Q)
    (hUy : U ≤ (Erdos387.BPZScale.y t S.k)^2)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (c a A : ℤ) (hc : (c : ZMod (C.q C.j)) ≠ 0) :
    ‖intervalSum A (Q/U-Q/(4*U)) (fun m => χ m*seq C.modulus c a [] m)‖ ≤
      4*((Q/U-Q/(4*U) : ℕ) : ℝ)/(t : ℝ) := by
  let p := C.q C.j
  let s₀ := g*smallProduct C.f*Erdos387.CoverBPZ.refinementModulus S
  have : NeZero p := ⟨C.terminal_prime.ne_zero⟩
  have : Fact p.Prime := ⟨C.terminal_prime⟩
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨hprime,hgap⟩ := bpz_scale_conditions t S.k (s₀::C.ss).length p U
    S.hk3 ht C.depth C.terminal_large.le hUy
  have hR : 1 ≤ t^(2^(s₀::C.ss).length) := Nat.one_le_pow _ _ ht1
  obtain ⟨hinterval,hboundary⟩ := separated_interval_conditions Q U
    (Erdos387.BPZScale.gap t S.k) p (t^(2^(s₀::C.ss).length))
    hU hUQ hR hgap (C.terminal_gap.trans hQ)
  have hs₀p : s₀ ≤ p := (small_modulus_le C.f hg hM C.small).trans
    ((Nat.pow_le_pow_right ht1 (bpz_exponent_margins S.k S.hk3).2.2).trans C.terminal_large.le)
  apply norm_interval_char_seq_le_div_scale p _ t ht1 s₀ C.ss C.chain
    C.modulus C.modulus_eq χ hχ c a [] A hc
  · simp
  · simpa only [List.length_nil, Nat.zero_add] using hprime
  · exact hinterval.trans (base_length_le_rectangle Q U)
  · intro v hv
    apply (hboundary v ?_).trans (base_length_le_rectangle Q U)
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hs₀p
    · exact C.remaining_max v hv

/-- The off-diagonal correlation on the exact natural rectangle, with
terminal-prime exceptional frequencies kept in the trivial branch. -/
theorem certificate_rectangle_correlation_split
    {B K n t medium g : ℕ} {S : Erdos387.CoverBPZ.BPZSection6Input B K}
    (C : CertificatePhaseData S n (Erdos387.BPZScale.y t S.k) medium
      (Erdos387.BPZScale.secondMin t S.k) (Erdos387.BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : Erdos387.CoverBPZ.refinementModulus S ≤ t)
    (Q U : ℕ) (hQ : C.q C.i₀ ≤ Q) (hU : 0 < U) (hUQ : U ≤ Q)
    (hUy : U ≤ (Erdos387.BPZScale.y t S.k)^2)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (u v : ℕ) (hu : u ≤ (Erdos387.BPZScale.y t S.k)^2)
    (hv : v ≤ (Erdos387.BPZScale.y t S.k)^2) (hne : u ≠ v)
    (huq : Nat.Coprime u C.modulus) (hvq : Nat.Coprime v C.modulus)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ m ∈ Finset.Ioc (Q/(4*U)) (Q/U),
      (χ ((u : ℤ)*m)*seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((u : ℤ)*m))*
        conj (χ ((v : ℤ)*m)*seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((v : ℤ)*m))‖ ≤
      if (h : ZMod (C.q C.j)) = 0 then ((Q/U-Q/(4*U) : ℕ) : ℝ)
      else 4*((Q/U-Q/(4*U) : ℕ) : ℝ)/(t : ℝ) := by
  classical
  simp_rw [linear_seq_product_correlation C.modulus _ u v huq hvq χ hχ]
  rw [sum_Ioc_eq_intervalSum (Q/(4*U)) (Q/U)
    (fun m : ℤ => (χ.mulShift ((u : ℤ)-(v : ℤ))) m *
      seq C.modulus (pairCoefficient C.modulus (h*((b : ℤ)-C.i₀.val)) u v) 0 [] m)]
  have hχ' (m : ℤ) : ‖(χ.mulShift ((u : ℤ)-(v : ℤ))) m‖ = 1 := hχ _
  split_ifs with hh
  · apply norm_intervalSum_le
    intro m
    rw [norm_mul, hχ', one_mul]
    exact norm_seq_le _ _ _ _ _
  · apply certificate_norm_rectangle_phase_le C ht hg hM Q U hQ hU hUQ hUy
      _ hχ' _ 0 _
    apply certificate_pairCoefficient_ne_zero C (by
      have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
      omega) b hb h hh u v hu hv hne (huq.mul_left hvq)

/-- Concrete bounded-weight Type-II estimate on the actual containing
rectangle. The diagonal and terminal-frequency exceptional branch remain
visible in the result. -/
theorem certificate_typeII_sq_le
    {B K n t medium g : ℕ} {S : Erdos387.CoverBPZ.BPZSection6Input B K}
    (C : CertificatePhaseData S n (Erdos387.BPZScale.y t S.k) medium
      (Erdos387.BPZScale.secondMin t S.k) (Erdos387.BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : Erdos387.CoverBPZ.refinementModulus S ≤ t)
    (Q U : ℕ) (hQ : C.q C.i₀ ≤ Q) (hU : 0 < U) (hUQ : U ≤ Q)
    (hUy : U ≤ (Erdos387.BPZScale.y t S.k)^2)
    (us : Finset ℕ) (hus : ∀ u ∈ us, u ≤ (Erdos387.BPZScale.y t S.k)^2)
    (hunit : ∀ u ∈ us, Nat.Coprime u C.modulus)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val) (h : ℤ)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (α β : ℕ → ℂ) (hα : ∀ u ∈ us, ‖α u‖ ≤ 1)
    (hβ : ∀ m ∈ Finset.Ioc (Q/(4*U)) (Q/U), ‖β m‖ ≤ 1) :
    ‖∑ u ∈ us, ∑ m ∈ Finset.Ioc (Q/(4*U)) (Q/U), α u*β m*
      (χ ((u : ℤ)*m)*seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((u : ℤ)*m))‖^2 ≤
      ((Q/U-Q/(4*U) : ℕ) : ℝ)*
        ((us.card : ℝ)*((Q/U-Q/(4*U) : ℕ) : ℝ) +
          (us.card : ℝ)*((us.card-1 : ℕ) : ℝ)*
            (if (h : ZMod (C.q C.j)) = 0 then ((Q/U-Q/(4*U) : ℕ) : ℝ)
             else 4*((Q/U-Q/(4*U) : ℕ) : ℝ)/(t : ℝ))) := by
  classical
  let V := Finset.Ioc (Q/(4*U)) (Q/U)
  let F : ℕ → ℕ → ℂ := fun u m => χ ((u : ℤ)*m)*
    seq C.modulus (h*((b : ℤ)-C.i₀.val)) 0 [] ((u : ℤ)*m)
  let R : ℝ := if (h : ZMod (C.q C.j)) = 0 then ((Q/U-Q/(4*U) : ℕ) : ℝ)
    else 4*((Q/U-Q/(4*U) : ℕ) : ℝ)/(t : ℝ)
  have hc := typeII_cauchy us V α β F hα hβ (by
    intro u hu m hm
    dsimp [F]
    rw [norm_mul, hχ, one_mul]
    exact norm_seq_le _ _ _ _ _)
  have hoff : (∑ u ∈ us, ∑ v ∈ us.erase u, ‖∑ m ∈ V, F u m*conj (F v m)‖) ≤
      (us.card : ℝ)*((us.card-1 : ℕ) : ℝ)*R := by
    calc
      _ ≤ ∑ u ∈ us, ∑ v ∈ us.erase u, R := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        have hv' := Finset.mem_of_mem_erase hv
        exact certificate_rectangle_correlation_split C ht hg hM Q U hQ hU hUQ hUy
          b hb h u v (hus u hu) (hus v hv')
          (fun he => (Finset.ne_of_mem_erase hv) he.symm) (hunit u hu) (hunit v hv') χ hχ
      _ = ∑ _u ∈ us, ((us.card-1 : ℕ) : ℝ)*R := by
        apply Finset.sum_congr rfl
        intro u hu
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hu]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : V.card = Q/U-Q/(4*U) := Nat.card_Ioc _ _
  rw [hcard] at hc
  apply hc.trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hoff) (Nat.cast_nonneg _)

/-- Actual stopped-leaf products in one dyadic block, retaining the
original conductor-unit restriction. -/
noncomputable def dyadicUnits (y M j : ℕ) : Finset ℕ := by
  classical
  exact (((stoppedLeaves y).image (fun l => l.chosen.prod)).filter
    (fun u => 2^j ≤ u ∧ u < 2^(j+1) ∧ Nat.Coprime u M))

theorem dyadicUnits_data (y M j u : ℕ) (hy : 1 ≤ y) (hu : u ∈ dyadicUnits y M j) :
    0 < u ∧ u ≤ y^2 ∧ Nat.Coprime u M ∧ 2^j ≤ u ∧ u < 2^(j+1) := by
  classical
  obtain ⟨hi,hlo,hhi,hcop⟩ := Finset.mem_filter.mp hu
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hl,hs⟩ := (mem_stoppedLeaves y l).mp hl
  have hd := (SeparatedBuchstabDecomposition.e5_leaf_domain y hy l hl).2 hs
  exact ⟨lt_trans (by omega) hd.1, hd.2.1, hcop, hlo, hhi⟩

theorem card_dyadicUnits_le (y M j : ℕ) : (dyadicUnits y M j).card ≤ 2^j := by
  classical
  have hsub : dyadicUnits y M j ⊆ Finset.Ico (2^j) (2^(j+1)) := by
    intro u hu
    have hh := (Finset.mem_filter.mp hu).2
    exact Finset.mem_Ico.mpr ⟨hh.1,hh.2.1⟩
  apply (Finset.card_le_card hsub).trans
  simp only [Nat.card_Ico, pow_succ]
  omega

/-- A nonempty actual dyadic source domain derives BOTH scale bounds
required by the phase consumer; empty source domains need no estimate. -/
theorem scale_bounds_of_actual_pair (y Q j : ℕ) (hy : 1 ≤ y)
    (P : SeparatedBuchstabDecomposition.Leaf → ℕ → Prop)
    (l : SeparatedBuchstabDecomposition.Leaf) (m : ℕ)
    (hm : (l,m) ∈ dyadicPairs y Q j P) : 2^j ≤ Q ∧ 2^j ≤ y^2 := by
  have hh := (mem_dyadicPairs y Q j P l m).mp hm
  obtain ⟨hl,hs⟩ := (mem_stoppedLeaves y l).mp hh.1.1
  have hd := (SeparatedBuchstabDecomposition.e5_leaf_domain y hy l hl).2 hs
  have hmpos : 0 < m := (Nat.zero_le _).trans_lt hh.2.1.1
  exact ⟨hh.1.2.1.trans ((Nat.le_mul_of_pos_right _ hmpos).trans hh.2.2.2.1),
    hh.1.2.1.trans hd.2.1⟩

/-- Explicit normalization of the norm-two window factor. The factor2
must remain outside the corresponding separated sum. -/
theorem normalized_left_weight_le (y A B u p : ℕ)
    (h : ZMod (2*y+1)) (k : ZMod (2*B+1)) (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖a*ZMod.stdAddChar (-(h*(p : ZMod (2*y+1))))*windowLeft A B u k/2‖ ≤ 1 := by
  rw [norm_div, norm_mul, norm_mul]
  simp only [AddChar.norm_apply, mul_one, Complex.norm_ofNat]
  have hw := norm_windowLeft_le A B u k
  have hprod : ‖a‖*‖windowLeft A B u k‖ ≤ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg (windowLeft A B u k)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr (by simpa using hprod)

/-- The m-weight retains BOTH finite Fourier factors and its original
coefficient, and still has norm≤1. -/
theorem right_weight_le (y B m : ℕ) (h : ZMod (2*y+1)) (k : ZMod (2*B+1))
    (b : ℂ) (hb : ‖b‖ ≤ 1) :
    ‖b*ZMod.stdAddChar (h*(SeparatedBuchstabSeparation.roughCutoff y m : ZMod (2*y+1)))*
      windowRight B m k‖ ≤ 1 := by
  simpa only [norm_mul, AddChar.norm_apply, norm_windowRight, mul_one] using hb

end Erdos387Proof.SeparatedTypeIICauchy
