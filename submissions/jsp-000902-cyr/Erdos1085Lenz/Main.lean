import Mathlib

/-!
# Erdős Problem #1085: Lenz's construction `f_d(n) ≥ ((p−1)/(2p)) n² − O(1)` for `d ≥ 4`

Let `f_d(n)` be the maximal number of unit-distance pairs among `n` points of `ℝ^d`.  The
problem page records that a construction of Lenz (points on orthogonal circles) shows that for
`d ≥ 4`, `f_d(n) ≥ ((p−1)/(2p)) n² − O(1)` with `p = ⌊d/2⌋`.  This file proves that bound in the
exact shape of the formal-conjectures statement `Erdos1085.erdos_1085.variants.lower_d4_lenz`
(tagged "research solved" with `sorry`), with the definitions `unitDistNum` and `f` copied
verbatim.

Proof.  For `j < p` place `n_j` points (with `∑ n_j = n`, the `n_j` differing by at most one) on
the circle of radius `1/√2` in the coordinate plane `(2j, 2j+1)`; two points on different circles
are at distance exactly `1` (`‖u‖² + ‖v‖² = 1/2 + 1/2`).  Hence
`f_d(n) ≥ ∑_{j<k} n_j n_k = (n² − ∑ n_j²)/2 ≥ ((p−1)/(2p)) n² − p/8`.  Erdős's matching upper bound
and the questions for `d = 2, 3` are not addressed.
-/

open Filter Finset
open scoped Topology

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart
(formal-conjectures definition). -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` points in
`ℝ^d` make (formal-conjectures definition). -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (EuclideanSpace ℝ (Fin d))) (_ : s.card = n), unitDistNum s

namespace Lenz1085

open Finset

private lemma den_pos (t : ℕ) : (0:ℝ) < 1 + (t:ℝ)^2 := by positivity

private noncomputable def cc (t : ℕ) : ℝ := (1 - (t:ℝ)^2) / (1 + (t:ℝ)^2)
private noncomputable def ss (t : ℕ) : ℝ := (2*(t:ℝ)) / (1 + (t:ℝ)^2)

private lemma cc_sq_add_ss_sq (t : ℕ) : cc t ^ 2 + ss t ^ 2 = 1 := by
  have h := (den_pos t).ne'
  unfold cc ss
  field_simp
  ring

private lemma cc_inj {t t' : ℕ} (h : cc t = cc t') : t = t' := by
  have h1 := (den_pos t).ne'
  have h2 := (den_pos t').ne'
  rw [cc, cc, div_eq_div_iff h1 h2] at h
  have hsq : ((t:ℝ))^2 = ((t':ℝ))^2 := by nlinarith [h]
  have : (t:ℝ) = (t':ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) t', hsq]
  exact_mod_cast this

/-- The Lenz point: on circle `j` (in coordinates `2j, 2j+1`), at rational angle parameter `t`. -/
private noncomputable def PT (D j t : ℕ) : EuclideanSpace ℝ (Fin D) :=
  if h : 2*j+1 < D then
    EuclideanSpace.single (⟨2*j, by omega⟩ : Fin D) (cc t / Real.sqrt 2)
      + EuclideanSpace.single (⟨2*j+1, h⟩ : Fin D) (ss t / Real.sqrt 2)
  else 0

private lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma PT_inner {D j j' t t' : ℕ} (hj : 2*j+1 < D) (hj' : 2*j'+1 < D) :
    inner ℝ (PT D j t) (PT D j' t')
      = if j = j' then (cc t * cc t' + ss t * ss t') / 2 else 0 := by
  have h2 : (Real.sqrt 2) ≠ 0 := by positivity
  simp only [PT, hj, hj', ↓reduceDIte]
  simp only [inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    PiLp.single_apply, starRingEnd_apply, star_trivial, Fin.mk.injEq]
  split_ifs with h1 h2 h3 h4 h5 <;>
    first
      | omega
      | (field_simp; rw [sqrt_two_sq]; ring)
      | ring


private lemma PT_norm_sq {D j t : ℕ} (hj : 2 * j + 1 < D) : ‖PT D j t‖ ^ 2 = 1 / 2 := by
  rw [← real_inner_self_eq_norm_sq, PT_inner hj hj]
  have h := cc_sq_add_ss_sq t
  split_ifs with hx
  · linear_combination h / 2
  · exact absurd rfl hx

private lemma PT_dist_of_ne {D j j' t t' : ℕ} (hj : 2 * j + 1 < D) (hj' : 2 * j' + 1 < D)
    (hne : j ≠ j') : dist (PT D j t) (PT D j' t') = 1 := by
  have hsq : dist (PT D j t) (PT D j' t') ^ 2 = 1 := by
    rw [dist_eq_norm, norm_sub_sq_real, PT_inner hj hj', PT_norm_sq (t := t) hj,
      PT_norm_sq (t := t') hj']
    split_ifs with hx
    · exact absurd hx hne
    · ring
  have h1 : dist (PT D j t) (PT D j' t') = Real.sqrt 1 := by
    rw [← hsq, Real.sqrt_sq dist_nonneg]
  simpa using h1

private lemma PT_eq_iff {D j j' t t' : ℕ} (hj : 2 * j + 1 < D) (hj' : 2 * j' + 1 < D)
    (h : PT D j t = PT D j' t') : j = j' ∧ t = t' := by
  have hjj : j = j' := by
    by_contra hne
    have h1 := PT_dist_of_ne (t := t) (t' := t') hj hj' hne
    rw [h, dist_self] at h1
    norm_num at h1
  subst hjj
  refine ⟨rfl, ?_⟩
  have hd : dist (PT D j t) (PT D j t') = 0 := by rw [h, dist_self]
  have hsq : dist (PT D j t) (PT D j t') ^ 2 = 1 - (cc t * cc t' + ss t * ss t') := by
    rw [dist_eq_norm, norm_sub_sq_real, PT_inner hj hj, PT_norm_sq (t := t) hj,
      PT_norm_sq (t := t') hj]
    split_ifs with hx
    · ring
    · exact absurd rfl hx
  rw [hd] at hsq
  have h1 := cc_sq_add_ss_sq t
  have h2 := cc_sq_add_ss_sq t'
  have hle : (cc t - cc t') ^ 2 ≤ 0 := by nlinarith [sq_nonneg (ss t - ss t')]
  have hz : (cc t - cc t') ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  have : cc t = cc t' := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hz
    linarith
  exact cc_inj this

private lemma dist_out_mk {X : Type*} [MetricSpace X] (a b : X) :
    dist (s(a, b) : Sym2 X).out.1 (s(a, b) : Sym2 X).out.2 = dist a b := by
  rcases hh : (s(a, b) : Sym2 X).out with ⟨x, y⟩
  have h : (s(x, y) : Sym2 X) = s(a, b) := by
    have h0 := Quot.out_eq (s(a, b) : Sym2 X)
    rw [hh] at h0
    exact h0
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact dist_comm _ _

private lemma unitDistNum_le_f {D n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin D)))
    (h : S.card = n) : unitDistNum S ≤ f D n := by
  have hbdd : BddAbove (Set.range fun s : Finset (EuclideanSpace ℝ (Fin D)) =>
      ⨆ (_ : s.card = n), unitDistNum s) := by
    refine ⟨n * n + n, ?_⟩
    rintro x ⟨s, rfl⟩
    show (⨆ (_ : #s = n), unitDistNum s) ≤ n * n + n
    by_cases hs : s.card = n
    · rw [ciSup_pos hs]
      calc unitDistNum s ≤ #(s.sym2) := Finset.card_filter_le _ _
        _ = (s.card + 1).choose 2 := Finset.card_sym2 s
        _ = (n + 1) * n / 2 := by rw [hs, Nat.choose_two_right]; simp
        _ ≤ (n + 1) * n := Nat.div_le_self _ _
        _ = n * n + n := by ring
    · have : IsEmpty (s.card = n) := ⟨hs⟩
      rw [ciSup_of_empty]
      exact bot_le
  refine le_ciSup_of_le hbdd S ?_
  rw [ciSup_pos h]


private lemma count_split (n p : ℕ) :
    n * n = 2 * #{z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p}
      + #{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} := by
  classical
  have hAB : #{z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p}
      = #{z ∈ (range n) ×ˢ (range n) | z.2 % p < z.1 % p} := by
    refine Finset.card_bij' (fun z _ => (z.2, z.1)) (fun z _ => (z.2, z.1)) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hz ⊢
      exact ⟨⟨hz.1.2, hz.1.1⟩, hz.2⟩
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hz ⊢
      exact ⟨⟨hz.1.2, hz.1.1⟩, hz.2⟩
    · intro z _; rfl
    · intro z _; rfl
  have h1 := Finset.card_filter_add_card_filter_not
      (s := (range n) ×ˢ (range n)) (p := fun z : ℕ × ℕ => z.1 % p = z.2 % p)
  have h2 := Finset.card_filter_add_card_filter_not
      (s := {z ∈ (range n) ×ˢ (range n) | ¬ (z.1 % p = z.2 % p)})
      (p := fun z : ℕ × ℕ => z.1 % p < z.2 % p)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : {z ∈ (range n) ×ˢ (range n) | ¬ (z.1 % p = z.2 % p) ∧ z.1 % p < z.2 % p}
      = {z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p} := by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨Nat.ne_of_lt h, h⟩⟩
  have e2 : {z ∈ (range n) ×ˢ (range n) | ¬ (z.1 % p = z.2 % p) ∧ ¬ (z.1 % p < z.2 % p)}
      = {z ∈ (range n) ×ˢ (range n) | z.2 % p < z.1 % p} := by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => ⟨fun h => lt_of_le_of_ne (Nat.not_lt.mp h.2) (Ne.symm h.1),
      fun h => ⟨Ne.symm (Nat.ne_of_lt h), Nat.not_lt.mpr (le_of_lt h)⟩⟩
  rw [e1, e2] at h2
  rw [Finset.card_product, Finset.card_range] at h1
  omega

private lemma card_diag (n p : ℕ) (hp : 0 < p) :
    #{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p}
      = ∑ j ∈ range p, (#{t ∈ range n | t % p = j}) ^ 2 := by
  classical
  have hmaps : Set.MapsTo (fun z : ℕ × ℕ => z.1 % p)
      ↑{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} ↑(range p) := by
    intro z _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hp
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : {z ∈ {z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} | z.1 % p = j}
      = {z ∈ (range n) ×ˢ (range n) | z.1 % p = j ∧ z.2 % p = j} := by
    rw [Finset.filter_filter]
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ =>
      ⟨fun h => ⟨h.2, h.1.symm.trans h.2⟩, fun h => ⟨h.1.trans h.2.symm, h.1⟩⟩
  have e2 : {z ∈ (range n) ×ˢ (range n) | z.1 % p = j ∧ z.2 % p = j}
      = {t ∈ range n | t % p = j} ×ˢ {t ∈ range n | t % p = j} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [e, e2, Finset.card_product, sq]

private lemma nj_ge (n p j : ℕ) (hp : 0 < p) (hj : j < p) :
    n / p ≤ #{t ∈ range n | t % p = j} := by
  classical
  have h := Finset.card_le_card_of_injOn (s := range (n / p))
      (t := {t ∈ range n | t % p = j}) (fun k => p * k + j) ?_ ?_
  · simpa using h
  · intro k hk
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · have h1 : p * k + j < p * (n / p) := by
        have : p * k + p ≤ p * (n / p) := by
          have : k + 1 ≤ n / p := hk
          calc p * k + p = p * (k + 1) := by ring
            _ ≤ p * (n / p) := Nat.mul_le_mul_left p this
        omega
      exact lt_of_lt_of_le h1 (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n p)
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  · intro k _ k' _ hkk
    simp only at hkk
    have : p * k = p * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left hp this

private lemma nj_le (n p j : ℕ) :
    #{t ∈ range n | t % p = j} ≤ n / p + 1 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := {t ∈ range n | t % p = j})
      (t := range (n / p + 1)) (fun t => t / p) ?_ ?_
  · simpa using h
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt ht.1))
  · intro t ht t' ht' hE
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht ht'
    simp only at hE
    calc t = p * (t / p) + t % p := (Nat.div_add_mod t p).symm
      _ = p * (t' / p) + t' % p := by rw [hE, ht.2, ht'.2]
      _ = t' := Nat.div_add_mod t' p

private lemma nj_sum (n p : ℕ) (hp : 0 < p) :
    ∑ j ∈ range p, #{t ∈ range n | t % p = j} = n := by
  classical
  have hmaps : Set.MapsTo (fun t : ℕ => t % p) ↑(range n) ↑(range p) := by
    intro t _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hp
  rw [← Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_range]

private lemma sum_sq_bound (n p : ℕ) (hp : 0 < p) :
    (∑ j ∈ range p, ((#{t ∈ range n | t % p = j} : ℕ) : ℝ) ^ 2)
      ≤ (((n / p : ℕ) : ℝ) + 1) * ((n % p : ℕ) : ℝ) + ((n / p : ℕ) : ℝ) * (n : ℝ) := by
  classical
  set q : ℝ := ((n / p : ℕ) : ℝ) with hq
  set x : ℕ → ℝ := fun j => ((#{t ∈ range n | t % p = j} : ℕ) : ℝ) with hx
  have hxsum : ∑ j ∈ range p, x j = (n : ℝ) := by
    rw [hx]
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (nj_sum n p hp)
  have hxge : ∀ j ∈ range p, q ≤ x j := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [hq, hx]
    exact_mod_cast nj_ge n p j hp hj
  have hxle : ∀ j ∈ range p, x j ≤ q + 1 := by
    intro j _
    simp only [hq, hx]
    exact_mod_cast nj_le n p j
  have hb : ∀ j ∈ range p, (x j) ^ 2 ≤ (q + 1) * (x j - q) + q * x j := by
    intro j hj
    nlinarith [hxge j hj, hxle j hj]
  have hstep : ∑ j ∈ range p, (x j) ^ 2
      ≤ ∑ j ∈ range p, ((q + 1) * (x j - q) + q * x j) := Finset.sum_le_sum hb
  have hval : ∑ j ∈ range p, ((q + 1) * (x j - q) + q * x j)
      = (q + 1) * ((n : ℝ) - (p : ℝ) * q) + q * (n : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, hxsum]
    ring
  have hmod : (n : ℝ) - (p : ℝ) * q = ((n % p : ℕ) : ℝ) := by
    have := Nat.div_add_mod n p
    have h2 : (p : ℝ) * q + ((n % p : ℕ) : ℝ) = (n : ℝ) := by
      rw [hq]; exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
    linarith
  rw [hval, hmod] at hstep
  exact hstep


private lemma exists_config (D n p : ℕ) (hp : 0 < p) (hpD : 2 * p ≤ D) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin D)), S.card = n ∧
      #{z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p} ≤ unitDistNum S := by
  classical
  have hval : ∀ t : ℕ, 2 * (t % p) + 1 < D := by
    intro t
    have := Nat.mod_lt t hp
    omega
  have hQinj : Function.Injective (fun t : ℕ => PT D (t % p) (t / p)) := by
    intro t t' h
    have hh := PT_eq_iff (hval t) (hval t') h
    calc t = p * (t / p) + t % p := (Nat.div_add_mod t p).symm
      _ = p * (t' / p) + t' % p := by rw [hh.2, hh.1]
      _ = t' := Nat.div_add_mod t' p
  refine ⟨(range n).image (fun t : ℕ => PT D (t % p) (t / p)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hQinj, Finset.card_range]
  · rw [unitDistNum]
    refine Finset.card_le_card_of_injOn
      (fun z : ℕ × ℕ => s(PT D (z.1 % p) (z.1 / p), PT D (z.2 % p) (z.2 / p))) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_image_of_mem _ (Finset.mem_range.mpr hz.1.1),
          Finset.mem_image_of_mem _ (Finset.mem_range.mpr hz.1.2)⟩
      · rw [dist_out_mk]
        exact PT_dist_of_ne (hval z.1) (hval z.2) (Nat.ne_of_lt hz.2)
    · intro z hz w hw hzw
      rw [Finset.mem_coe, Finset.mem_filter] at hz hw
      rw [Sym2.eq_iff] at hzw
      rcases hzw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext (hQinj h1) (hQinj h2)
      · exfalso
        have e1 := hQinj h1
        have e2 := hQinj h2
        have hcon : z.1 % p < z.1 % p :=
          calc z.1 % p < z.2 % p := hz.2
            _ = w.1 % p := by rw [e2]
            _ < w.2 % p := hw.2
            _ = z.1 % p := by rw [e1]
        exact absurd hcon (lt_irrefl _)

end Lenz1085

/-- **Lenz's construction, data-binder form.**  For every `d` and `n` there is a constant `C`
(depending only on `d`) with `((⌊(d+4)/2⌋ − 1)/(2⌊(d+4)/2⌋)) n² − C ≤ f (d + 4) n`. -/
theorem lenz_lower_bound (d : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ,
      (((d + 4) / 2 - 1 : ℕ) : ℝ) / (2 * (((d + 4) / 2 : ℕ) : ℝ)) * n ^ 2 - C ≤ f (d + 4) n := by
  classical
  have hp2 : 2 ≤ (d + 4) / 2 := by omega
  have hpD : 2 * ((d + 4) / 2) ≤ d + 4 := by omega
  refine ⟨(((d + 4) / 2 : ℕ) : ℝ) / 8, fun n => ?_⟩
  set p : ℕ := (d + 4) / 2 with hpdef
  obtain ⟨S, hcard, hle⟩ := Lenz1085.exists_config (d + 4) n p (by omega) hpD
  have hfle : unitDistNum S ≤ f (d + 4) n := Lenz1085.unitDistNum_le_f S hcard
  have hsplit := Lenz1085.count_split n p
  have hdiag := Lenz1085.card_diag n p (by omega)
  have hbound := Lenz1085.sum_sq_bound n p (by omega)
  -- move to the reals
  set N : ℝ := (n : ℝ) with hN
  set P : ℝ := (p : ℝ) with hP
  set Qr : ℝ := ((n / p : ℕ) : ℝ) with hQr
  set R : ℝ := ((n % p : ℕ) : ℝ) with hR
  set U : ℝ := ((unitDistNum S : ℕ) : ℝ) with hU
  have hP2 : (2 : ℝ) ≤ P := by rw [hP]; exact_mod_cast hp2
  have hNPQR : N = P * Qr + R := by
    rw [hN, hP, hQr, hR]
    exact_mod_cast (Nat.div_add_mod n p).symm
  have hAU : ((#{z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p} : ℕ) : ℝ) ≤ U := by
    rw [hU]; exact_mod_cast hle
  have hMain : N * N ≤ 2 * U + ((Qr + 1) * R + Qr * N) := by
    have h1 : (N * N : ℝ)
        = 2 * ((#{z ∈ (range n) ×ˢ (range n) | z.1 % p < z.2 % p} : ℕ) : ℝ)
          + ((#{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} : ℕ) : ℝ) := by
      rw [hN]; exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hsplit
    have h2 : ((#{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} : ℕ) : ℝ)
        = ∑ j ∈ range p, ((#{t ∈ range n | t % p = j} : ℕ) : ℝ) ^ 2 := by
      rw [hdiag]; push_cast; ring
    rw [h2] at h1
    linarith [hAU, hbound]
  have harith : 4 * P * ((Qr + 1) * R + Qr * N) ≤ 4 * N ^ 2 + P ^ 2 := by
    rw [hNPQR]
    nlinarith [sq_nonneg (2 * R - P)]
  have hfinal : (P - 1) / (2 * P) * N ^ 2 - P / 8 ≤ U := by
    rw [div_mul_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * P)]
    nlinarith [hMain, harith, hP2]
  have hcast : (((p - 1 : ℕ)) : ℝ) = P - 1 := by
    rw [hP]
    have : (1 : ℕ) ≤ p := by omega
    push_cast [this]
    ring
  rw [hcast]
  have hfR : U ≤ ((f (d + 4) n : ℕ) : ℝ) := by rw [hU]; exact_mod_cast hfle
  linarith [hfinal, hfR]

/-- **Erdős #1085, Lenz's lower bound (formal-conjectures `lower_d4_lenz`).**  For `d ≥ 4`,
`f_d(n) ≥ ((p−1)/(2p)) n² − O(1)` with `p = ⌊d/2⌋`.  The upper bound and the planar questions are
not claimed. -/
theorem erdos_1085_lower_d4_lenz {d : ℕ} (hd : 4 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 - C ≤ f d n := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 4 := ⟨d - 4, by omega⟩
  exact lenz_lower_bound d'
