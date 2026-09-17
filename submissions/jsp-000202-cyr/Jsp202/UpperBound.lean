import Jsp202.DiameterGraph
import Jsp202.CrossingLemma

open scoped Classical RealInnerProductSpace
open Finset

namespace HopfPannwitz

variable {n : ℕ}

/-! ## Step 1 — every two vertex-disjoint edges meet (the thrackle property) -/

/-- **Every two edges meet.**  Two edges of the diameter graph that are vertex-disjoint
(all four indices distinct) have their closed segments sharing a point.  Direct application of
`crossing_lemma`. -/
theorem every_two_edges_meet (P : Fin n → EuclideanSpace ℝ (Fin 2)) (hinj : Function.Injective P)
    (D : ℝ) (hUB : ∀ i j, dist (P i) (P j) ≤ D)
    {i j k l : Fin n}
    (hij : (diameterGraph P D).Adj i j) (hkl : (diameterGraph P D).Adj k l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ∃ O, Wbtw ℝ (P i) O (P j) ∧ Wbtw ℝ (P k) O (P l) := by
  obtain ⟨hijne, hijd⟩ := hij
  obtain ⟨hklne, hkld⟩ := hkl
  exact crossing_lemma (P i) (P j) (P k) (P l) D hijd hkld
    (hUB k i) (hUB k j) (hUB l i) (hUB l j)
    (hUB i k) (hUB i l) (hUB j k) (hUB j l)
    (fun h => hijne (hinj h)) (fun h => hklne (hinj h))
    (fun h => hik (hinj h)) (fun h => hil (hinj h))
    (fun h => hjk (hinj h)) (fun h => hjl (hinj h))

/-! ## Angle bound (law of cosines) -/

open EuclideanGeometry in
/-- If `dist p x = dist p y = D > 0` and `dist x y ≤ D`, then `∠ x p y ≤ π/3`. -/
theorem angle_le_pi_div_three {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p x y : V) (D : ℝ) (hD : 0 < D)
    (hpx : dist p x = D) (hpy : dist p y = D) (hxy : dist x y ≤ D) :
    ∠ x p y ≤ Real.pi / 3 := by
  have hlaw := EuclideanGeometry.law_cos x p y
  rw [dist_comm x p, dist_comm y p, hpx, hpy] at hlaw
  have hcos : (1:ℝ)/2 ≤ Real.cos (∠ x p y) := by
    have hle : dist x y * dist x y ≤ D * D := mul_le_mul hxy hxy dist_nonneg (le_of_lt hD)
    nlinarith [hlaw, hle, mul_pos hD hD]
  have h1 : ∠ x p y ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg x p y, EuclideanGeometry.angle_le_pi x p y⟩
  have h2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hcos3 : Real.cos (Real.pi / 3) = 1/2 := Real.cos_pi_div_three
  have hiff := Real.strictAntiOn_cos.le_iff_ge h2 h1
  rw [hcos3] at hiff
  exact hiff.mp hcos

/-! ## The wedge double-crossing impossibility (the geometric crux) -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `O - p = α • (a - p)` for some `α ∈ [0,1]`, from `Wbtw ℝ p O a`. -/
private theorem wbtw_scalar (p a O : V) (h : Wbtw ℝ p O a) :
    ∃ α : ℝ, α ∈ Set.Icc (0:ℝ) 1 ∧ O - p = α • (a - p) := by
  rw [Wbtw, affineSegment_eq_segment, segment_eq_image_lineMap] at h
  obtain ⟨α, hα, hO⟩ := h
  exact ⟨α, hα, by rw [← hO]; simp [AffineMap.lineMap_apply]⟩

/-- **Wedge double-crossing is impossible.**  `b` in the open cone at `p` spanned by
`a - p`, `c - p` (positive `s, t`, independent directions), `O1 ∈ [p,a]\{p}`, `O2 ∈ [p,c]\{p}`,
both on `[b,q]` — contradictory. -/
theorem wedge_no_double_cross (p a c b q O1 O2 : V)
    (hind : ∀ r₁ r₂ : ℝ, r₁ • (a - p) + r₂ • (c - p) = 0 → r₁ = 0 ∧ r₂ = 0)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hb : b - p = s • (a - p) + t • (c - p))
    (h1 : Wbtw ℝ p O1 a) (h1' : O1 ≠ p)
    (h2 : Wbtw ℝ p O2 c) (h2' : O2 ≠ p)
    (k1 : Wbtw ℝ b O1 q) (k2 : Wbtw ℝ b O2 q) : False := by
  set u := a - p with hu
  set v := c - p with hv
  set w := q - b with hw
  obtain ⟨α, ⟨hα0, hα1⟩, hO1⟩ := wbtw_scalar p a O1 h1
  obtain ⟨β, ⟨hβ0, hβ1⟩, hO2⟩ := wbtw_scalar p c O2 h2
  obtain ⟨l1, ⟨hl10, hl11⟩, hK1⟩ := wbtw_scalar b q O1 k1
  obtain ⟨l2, ⟨hl20, hl21⟩, hK2⟩ := wbtw_scalar b q O2 k2
  have eq1 : α • u = l1 • w + s • u + t • v := by
    have : O1 - p = (O1 - b) + (b - p) := by abel
    rw [hO1, hK1, hb] at this
    rw [this]; abel
  have eq2 : β • v = l2 • w + s • u + t • v := by
    have : O2 - p = (O2 - b) + (b - p) := by abel
    rw [hO2, hK2, hb] at this
    rw [this]; abel
  have hw1 : l1 • w = (α - s) • u + (-t) • v := by
    have : l1 • w = α • u - s • u - t • v := by rw [eq1]; abel
    rw [this]; module
  have hw2 : l2 • w = (-s) • u + (β - t) • v := by
    have : l2 • w = β • v - s • u - t • v := by rw [eq2]; abel
    rw [this]; module
  have hcomb : l2 • ((α - s) • u + (-t) • v) = l1 • ((-s) • u + (β - t) • v) := by
    rw [← hw1, ← hw2, smul_smul, smul_smul, mul_comm]
  have hzero : (l2 * (α - s) - l1 * (-s)) • u + (l2 * (-t) - l1 * (β - t)) • v = 0 := by
    linear_combination (norm := module) hcomb
  obtain ⟨A, B⟩ := hind _ _ hzero
  have hαpos : 0 < α := by
    rcases lt_or_eq_of_le hα0 with h | h
    · exact h
    · exfalso; apply h1'; have : O1 - p = (0:ℝ) • u := by rw [hO1, ← h]
      simp at this; exact sub_eq_zero.mp this
  have hβpos : 0 < β := by
    rcases lt_or_eq_of_le hβ0 with h | h
    · exact h
    · exfalso; apply h2'; have : O2 - p = (0:ℝ) • v := by rw [hO2, ← h]
      simp at this; exact sub_eq_zero.mp this
  have hl1pos : 0 < l1 := by
    rcases lt_or_eq_of_le hl10 with h | h
    · exact h
    · exfalso
      have hwz : l1 • w = 0 := by rw [← h]; simp
      rw [hwz] at hw1
      obtain ⟨_, ht0⟩ := hind (α - s) (-t) hw1.symm
      simp at ht0; linarith
  have hl2pos : 0 < l2 := by
    rcases lt_or_eq_of_le hl20 with h | h
    · exact h
    · exfalso
      have hwz : l2 • w = 0 := by rw [← h]; simp
      rw [hwz] at hw2
      obtain ⟨hs0, _⟩ := hind (-s) (β - t) hw2.symm
      simp at hs0; linarith
  nlinarith [A, B, mul_pos hs (mul_pos hl2pos hαpos), mul_pos ht (mul_pos hl1pos hβpos),
    mul_pos hl2pos hαpos, mul_pos hl1pos hβpos, mul_pos hs ht,
    mul_pos hl1pos hl2pos, mul_pos ht hl1pos, mul_pos hs hl2pos]

/-! ## Cone lemma: among three neighbour-directions, one is a positive combination of the
other two.  A half-plane functional (`u + v + x`) rules out the "positively spanning" case. -/

section Cone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- From `‖u‖ = ‖v‖ = D` and `‖u - v‖ ≤ D`: `⟪u,v⟫ ≥ D²/2`. -/
private theorem inner_ge (u v : E) (D : ℝ) (hu : ‖u‖ = D) (hv : ‖v‖ = D)
    (h : ‖u - v‖ ≤ D) : D^2 / 2 ≤ ⟪u, v⟫ := by
  have hexp : ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * ⟪u, v⟫ := by rw [norm_sub_sq_real]; ring
  have h2 : ‖u - v‖^2 ≤ D^2 := by nlinarith [norm_nonneg (u - v), h]
  rw [hu, hv] at hexp
  nlinarith [hexp, h2]

/-- Two equal-length vectors at angle `< 90°` (positive inner product `≥ D²/2`) that are
distinct are linearly independent. -/
private theorem indep_pair (u v : E) (D : ℝ) (hD : 0 < D) (hu : ‖u‖ = D) (hv : ‖v‖ = D)
    (hinner : D^2 / 2 ≤ ⟪u, v⟫) (hne : u ≠ v) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hts : t • v = -(s • u) := by linear_combination (norm := module) hst
  have hnorm : ‖t • v‖ = ‖s • u‖ := by rw [hts, norm_neg]
  rw [norm_smul, norm_smul, hu, hv, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
  have habs : |t| = |s| := mul_right_cancel₀ (ne_of_gt hD) hnorm
  have hsq : s^2 = t^2 := by
    have h := congrArg (· ^ 2) habs
    simp only [sq_abs] at h
    linarith [h]
  have hfac : (s - t) * (s + t) = 0 := by ring_nf; nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h | h
  · have hst_eq : s = t := by linarith
    subst hst_eq
    have hz : s • (u + v) = 0 := by rw [smul_add]; exact hst
    by_cases hs0 : s = 0
    · exact ⟨hs0, hs0⟩
    · exfalso
      have huv : u + v = 0 := by
        rcases smul_eq_zero.mp hz with h | h
        · exact absurd h hs0
        · exact h
      have hvu : v = -u := by linear_combination (norm := module) huv
      rw [hvu, inner_neg_right, real_inner_self_eq_norm_sq, hu] at hinner
      nlinarith [hinner, hD]
  · have hst_eq : s = -t := by linarith
    subst hst_eq
    have huv : t • (v - u) = 0 := by linear_combination (norm := module) hst
    by_cases ht0 : t = 0
    · refine ⟨?_, ht0⟩; rw [ht0]; ring
    · exfalso
      have hvu : v - u = 0 := by
        rcases smul_eq_zero.mp huv with h | h
        · exact absurd h ht0
        · exact h
      have hvu2 : v = u := by linear_combination (norm := module) hvu
      exact hne hvu2.symm

/-- From `a1•w1 + a2•w2 + a3•w3 = 0` with `a1 ≠ 0` and both ratios positive, `w1` is a positive
combination of `w2, w3`. -/
private theorem posCombo (w1 w2 w3 : E) (a1 a2 a3 : ℝ)
    (hrel : a1 • w1 + a2 • w2 + a3 • w3 = 0) (ha1 : a1 ≠ 0)
    (hs : 0 < -a2 / a1) (ht : 0 < -a3 / a1) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ w1 = s • w2 + t • w3 := by
  refine ⟨-a2/a1, -a3/a1, hs, ht, ?_⟩
  have key : a1 • w1 = a1 • ((-a2/a1) • w2 + (-a3/a1) • w3) := by
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ ha1, mul_div_cancel₀ _ ha1]
    linear_combination (norm := module) hrel
  exact smul_right_injective E ha1 key

/-- **Cone lemma.**  Three equal-length vectors in the plane, pairwise at angle `≤ 60°`
(`⟪·,·⟫ ≥ D²/2`) and pairwise distinct, satisfy: one of them is a strictly positive
combination of the other two. -/
private theorem cone_of_three (u v x : EuclideanSpace ℝ (Fin 2)) (D : ℝ) (hD : 0 < D)
    (hnu : ‖u‖ = D) (hnv : ‖v‖ = D) (hnx : ‖x‖ = D)
    (iuv : D^2/2 ≤ ⟪u,v⟫) (iux : D^2/2 ≤ ⟪u,x⟫) (ivx : D^2/2 ≤ ⟪v,x⟫)
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x) :
    (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ v = s • u + t • x) ∨
    (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ u = s • v + t • x) ∨
    (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ x = s • u + t • v) := by
  have Iuv := indep_pair u v D hD hnu hnv iuv huv
  have Iux := indep_pair u x D hD hnu hnx iux hux
  have Ivx := indep_pair v x D hD hnv hnx ivx hvx
  have hdep : ¬ LinearIndependent ℝ ![u, v, x] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [finrank_euclideanSpace] at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hgsum, i0, hi0⟩ := hdep
  set c0 := g 0 with hc0
  set c1 := g 1 with hc1
  set c2 := g 2 with hc2
  have hrel : c0 • u + c1 • v + c2 • x = 0 := by
    have h := hgsum
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    exact h
  have hc0ne : c0 ≠ 0 := by
    intro h0; rw [h0, zero_smul, zero_add] at hrel
    obtain ⟨e1, e2⟩ := (LinearIndependent.pair_iff.mp Ivx) c1 c2 hrel
    fin_cases i0 <;> simp_all
  have hc1ne : c1 ≠ 0 := by
    intro h0; rw [h0, zero_smul, add_zero] at hrel
    obtain ⟨e1, e2⟩ := (LinearIndependent.pair_iff.mp Iux) c0 c2 hrel
    fin_cases i0 <;> simp_all
  have hc2ne : c2 ≠ 0 := by
    intro h0; rw [h0, zero_smul, add_zero] at hrel
    obtain ⟨e1, e2⟩ := (LinearIndependent.pair_iff.mp Iuv) c0 c1 hrel
    fin_cases i0 <;> simp_all
  have fu : (0:ℝ) < ⟪u, u + v + x⟫ := by
    rw [inner_add_right, inner_add_right, real_inner_self_eq_norm_sq, hnu]; nlinarith [iuv, iux, hD]
  have fv : (0:ℝ) < ⟪v, u + v + x⟫ := by
    rw [inner_add_right, inner_add_right, real_inner_self_eq_norm_sq, hnv]
    nlinarith [iuv, ivx, hD, real_inner_comm v u]
  have fx : (0:ℝ) < ⟪x, u + v + x⟫ := by
    rw [inner_add_right, inner_add_right, real_inner_self_eq_norm_sq, hnx]
    nlinarith [iux, ivx, hD, real_inner_comm x u, real_inner_comm x v]
  have hsum : c0 * ⟪u, u+v+x⟫ + c1 * ⟪v, u+v+x⟫ + c2 * ⟪x, u+v+x⟫ = 0 := by
    have := congrArg (fun w => ⟪w, u + v + x⟫) hrel
    simp only [inner_add_left, inner_smul_left, inner_zero_left,
      RCLike.conj_to_real] at this ⊢
    convert this using 1
  rcases lt_or_gt_of_ne hc0ne with s0 | s0 <;>
  rcases lt_or_gt_of_ne hc1ne with s1 | s1 <;>
  rcases lt_or_gt_of_ne hc2ne with s2 | s2
  · exfalso; nlinarith [mul_neg_of_neg_of_pos s0 fu, mul_neg_of_neg_of_pos s1 fv,
      mul_neg_of_neg_of_pos s2 fx, hsum]
  · right; right
    exact posCombo x u v c2 c0 c1 (by linear_combination (norm := module) hrel) hc2ne
      (div_pos_iff.mpr (Or.inl ⟨by linarith, s2⟩)) (div_pos_iff.mpr (Or.inl ⟨by linarith, s2⟩))
  · left
    exact posCombo v u x c1 c0 c2 (by linear_combination (norm := module) hrel) hc1ne
      (div_pos_iff.mpr (Or.inl ⟨by linarith, s1⟩)) (div_pos_iff.mpr (Or.inl ⟨by linarith, s1⟩))
  · right; left
    exact posCombo u v x c0 c1 c2 (by linear_combination (norm := module) hrel) hc0ne
      (div_pos_iff.mpr (Or.inr ⟨by linarith, s0⟩)) (div_pos_iff.mpr (Or.inr ⟨by linarith, s0⟩))
  · right; left
    exact posCombo u v x c0 c1 c2 (by linear_combination (norm := module) hrel) hc0ne
      (div_pos_iff.mpr (Or.inl ⟨by linarith, s0⟩)) (div_pos_iff.mpr (Or.inl ⟨by linarith, s0⟩))
  · left
    exact posCombo v u x c1 c0 c2 (by linear_combination (norm := module) hrel) hc1ne
      (div_pos_iff.mpr (Or.inr ⟨by linarith, s1⟩)) (div_pos_iff.mpr (Or.inr ⟨by linarith, s1⟩))
  · right; right
    exact posCombo x u v c2 c0 c1 (by linear_combination (norm := module) hrel) hc2ne
      (div_pos_iff.mpr (Or.inr ⟨by linarith, s2⟩)) (div_pos_iff.mpr (Or.inr ⟨by linarith, s2⟩))
  · exfalso; nlinarith [mul_pos s0 fu, mul_pos s1 fv, mul_pos s2 fx, hsum]

end Cone

/-! ## Step 2 — the middle-neighbour lemma -/

/-- A crossing point of `[p,f]` and `[m,q]` that is not the apex `p`.  When the edges `{m,q}`
and `{p,f}` are vertex-disjoint this is `crossing_lemma`; when they share `f` (`q = f`) the
crossing is the shared vertex. -/
private theorem crossPoint (P : Fin n → EuclideanSpace ℝ (Fin 2)) (hinj : Function.Injective P)
    (D : ℝ) (hUB : ∀ i j, dist (P i) (P j) ≤ D) (p m f q : Fin n)
    (hpm : (diameterGraph P D).Adj p m) (hmq : (diameterGraph P D).Adj m q) (hqp : q ≠ p)
    (hpf : (diameterGraph P D).Adj p f) (hmf : m ≠ f) :
    ∃ O, Wbtw ℝ (P p) O (P f) ∧ Wbtw ℝ (P m) O (P q) ∧ O ≠ P p := by
  by_cases hqf : q = f
  · refine ⟨P f, wbtw_self_right ℝ (P p) (P f), ?_, ?_⟩
    · rw [hqf]; exact wbtw_self_right ℝ (P m) (P f)
    · intro h; exact hpf.1 (hinj h).symm
  · obtain ⟨O, hO1, hO2⟩ := every_two_edges_meet P hinj D hUB hpf hmq
      hpm.1 (Ne.symm hqp) (Ne.symm hmf) (Ne.symm hqf)
    refine ⟨O, hO1, hO2, ?_⟩
    intro hOp
    rw [hOp] at hO2
    have hadd := hO2.dist_add_dist
    have hmpd : dist (P m) (P p) = D := by rw [dist_comm]; exact hpm.2
    have hzero : dist (P p) (P q) = 0 := by rw [hmpd, hmq.2] at hadd; linarith
    exact hqp (hinj (dist_eq_zero.mp hzero)).symm

/-- If `m` is a middle neighbour of `p` (in the open cone spanned by neighbours `f1, f2`),
then `m`'s only diameter-neighbour is `p`. -/
private theorem middle_isolated (P : Fin n → EuclideanSpace ℝ (Fin 2))
    (hinj : Function.Injective P) (D : ℝ) (hUB : ∀ i j, dist (P i) (P j) ≤ D)
    (p m f1 f2 : Fin n)
    (hpm : (diameterGraph P D).Adj p m) (hpf1 : (diameterGraph P D).Adj p f1)
    (hpf2 : (diameterGraph P D).Adj p f2) (hmf1 : m ≠ f1) (hmf2 : m ≠ f2)
    (hind : ∀ r1 r2 : ℝ, r1 • (P f1 - P p) + r2 • (P f2 - P p) = 0 → r1 = 0 ∧ r2 = 0)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hb : P m - P p = s • (P f1 - P p) + t • (P f2 - P p)) :
    ∀ q, (diameterGraph P D).Adj m q → q = p := by
  intro q hmq
  by_contra hqp
  obtain ⟨O1, hO1a, hO1b, hO1p⟩ := crossPoint P hinj D hUB p m f1 q hpm hmq hqp hpf1 hmf1
  obtain ⟨O2, hO2a, hO2b, hO2p⟩ := crossPoint P hinj D hUB p m f2 q hpm hmq hqp hpf2 hmf2
  exact wedge_no_double_cross (P p) (P f1) (P f2) (P m) (P q) O1 O2 hind s t hs ht hb
    hO1a hO1p hO2a hO2p hO1b hO2b

/-- **Middle-neighbour lemma.**  If `p` has three distinct diameter-neighbours `i, j, k`, then
one of them has `p` as its unique diameter-neighbour (degree `1`). -/
theorem middle_neighbour (P : Fin n → EuclideanSpace ℝ (Fin 2)) (hinj : Function.Injective P)
    (D : ℝ) (hUB : ∀ a b, dist (P a) (P b) ≤ D)
    (p i j k : Fin n)
    (hpi : (diameterGraph P D).Adj p i) (hpj : (diameterGraph P D).Adj p j)
    (hpk : (diameterGraph P D).Adj p k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ m, (diameterGraph P D).Adj p m ∧ ∀ q, (diameterGraph P D).Adj m q → q = p := by
  -- D > 0 since P p ≠ P i
  have hD : 0 < D := by
    have hne : P p ≠ P i := fun h => hpi.1 (hinj h)
    have : 0 < dist (P p) (P i) := dist_pos.mpr hne
    rw [hpi.2] at this; exact this
  -- norms of the three direction vectors
  have hnorm : ∀ a : Fin n, (diameterGraph P D).Adj p a → ‖P a - P p‖ = D := by
    intro a ha; rw [← dist_eq_norm, dist_comm]; exact ha.2
  have hnu := hnorm i hpi
  have hnv := hnorm j hpj
  have hnx := hnorm k hpk
  -- inner-product lower bounds
  have hinner : ∀ a b : Fin n, ‖(P a - P p) - (P b - P p)‖ ≤ D := by
    intro a b
    have he : (P a - P p) - (P b - P p) = P a - P b := by abel
    rw [he, ← dist_eq_norm]; exact hUB a b
  have iuv := inner_ge (P i - P p) (P j - P p) D hnu hnv (hinner i j)
  have iux := inner_ge (P i - P p) (P k - P p) D hnu hnx (hinner i k)
  have ivx := inner_ge (P j - P p) (P k - P p) D hnv hnx (hinner j k)
  -- distinctness of direction vectors
  have hdist : ∀ a b : Fin n, a ≠ b → P a - P p ≠ P b - P p := by
    intro a b hab hcon; exact hab (hinj (sub_left_injective hcon))
  have huv := hdist i j hij
  have hux := hdist i k hik
  have hvx := hdist j k hjk
  -- independence-as-hind for each pair
  have hindjk : ∀ r1 r2 : ℝ, r1 • (P j - P p) + r2 • (P k - P p) = 0 → r1 = 0 ∧ r2 = 0 :=
    LinearIndependent.pair_iff.mp (indep_pair (P j - P p) (P k - P p) D hD hnv hnx ivx hvx)
  have hindik : ∀ r1 r2 : ℝ, r1 • (P i - P p) + r2 • (P k - P p) = 0 → r1 = 0 ∧ r2 = 0 :=
    LinearIndependent.pair_iff.mp (indep_pair (P i - P p) (P k - P p) D hD hnu hnx iux hux)
  have hindij : ∀ r1 r2 : ℝ, r1 • (P i - P p) + r2 • (P j - P p) = 0 → r1 = 0 ∧ r2 = 0 :=
    LinearIndependent.pair_iff.mp (indep_pair (P i - P p) (P j - P p) D hD hnu hnv iuv huv)
  rcases cone_of_three (P i - P p) (P j - P p) (P k - P p) D hD hnu hnv hnx
    iuv iux ivx huv hux hvx with h | h | h
  · -- j is the middle: P j - P p = s•(P i - P p) + t•(P k - P p)
    obtain ⟨s, t, hs, ht, hb⟩ := h
    exact ⟨j, hpj, middle_isolated P hinj D hUB p j i k hpj hpi hpk (Ne.symm hij) hjk
      hindik s t hs ht hb⟩
  · -- i is the middle
    obtain ⟨s, t, hs, ht, hb⟩ := h
    exact ⟨i, hpi, middle_isolated P hinj D hUB p i j k hpi hpj hpk hij hik
      hindjk s t hs ht hb⟩
  · -- k is the middle
    obtain ⟨s, t, hs, ht, hb⟩ := h
    exact ⟨k, hpk, middle_isolated P hinj D hUB p k i j hpk hpi hpj (Ne.symm hik) (Ne.symm hjk)
      hindij s t hs ht hb⟩

/-! ## Step 3 — vertex-deletion induction -/

/-- A vertex whose only diameter-neighbour is `p` has degree `≤ 1`. -/
private theorem degree_le_one_of_unique_neighbour (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ)
    (m p : Fin n) (h : ∀ q, (diameterGraph P D).Adj m q → q = p) :
    (diameterGraph P D).degree m ≤ 1 := by
  have hsub : (diameterGraph P D).neighborFinset m ⊆ {p} := by
    intro q hq
    rw [SimpleGraph.mem_neighborFinset] at hq
    simp [h q hq]
  calc (diameterGraph P D).degree m
      = ((diameterGraph P D).neighborFinset m).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ ({p} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton p

/-- **Upper bound (Hopf–Pannwitz).**  The diameter graph of `n` planar points at pairwise
distance `≤ D` has at most `n` edges. -/
theorem hopf_pannwitz_upper (n : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin 2))
    (hinj : Function.Injective P) (D : ℝ) (hUB : ∀ i j, dist (P i) (P j) ≤ D) :
    (diameterGraph P D).edgeFinset.card ≤ n := by
  induction n with
  | zero =>
    refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr ?_)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e
    induction e using Sym2.ind with | _ a b => exact a.elim0
  | succ m ih =>
    by_cases hdeg : ∃ x, (diameterGraph P D).degree x ≤ 1
    · -- delete a vertex of degree ≤ 1
      obtain ⟨x, hx⟩ := hdeg
      have hcard : Fintype.card ↥({x}ᶜ : Set (Fin (m + 1))) = m := by
        rw [Fintype.card_compl_set]
        simp
      set e0 : ↥({x}ᶜ : Set (Fin (m + 1))) ≃ Fin m := Fintype.equivFinOfCardEq hcard with he0
      set P' : Fin m → EuclideanSpace ℝ (Fin 2) := fun k => P (↑(e0.symm k)) with hP'
      have hinj' : Function.Injective P' :=
        hinj.comp (Subtype.val_injective.comp e0.symm.injective)
      have hUB' : ∀ a b, dist (P' a) (P' b) ≤ D := fun a b => hUB _ _
      -- iso between the induced subgraph on {x}ᶜ and the diameter graph of P'
      have hPval : ∀ a : ↥({x}ᶜ : Set (Fin (m + 1))), P' (e0 a) = P (↑a) := by
        intro a; simp [hP']
      have φ : ((diameterGraph P D).induce ({x}ᶜ : Set (Fin (m + 1)))) ≃g diameterGraph P' D := by
        refine ⟨e0, ?_⟩
        intro a b
        have hd : dist (P' (e0 a)) (P' (e0 b)) = dist (P ↑a) (P ↑b) := by rw [hPval a, hPval b]
        simp only [diameterGraph, SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
          ne_eq, hd, Equiv.apply_eq_iff_eq, Subtype.coe_inj]
      have hiso : ((diameterGraph P D).induce ({x}ᶜ : Set (Fin (m + 1)))).edgeFinset.card
          = (diameterGraph P' D).edgeFinset.card := φ.card_edgeFinset_eq
      have hdel : ((diameterGraph P D).induce ({x}ᶜ : Set (Fin (m + 1)))).edgeFinset.card
          = (diameterGraph P D).edgeFinset.card - (diameterGraph P D).degree x := by
        rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
          SimpleGraph.card_edgeFinset_deleteIncidenceSet]
      have hIH : (diameterGraph P' D).edgeFinset.card ≤ m := ih P' hinj' hUB'
      have hdle : (diameterGraph P D).degree x ≤ (diameterGraph P D).edgeFinset.card :=
        SimpleGraph.degree_le_card_edgeFinset _ x
      rw [hiso] at hdel
      omega
    · -- no vertex has degree ≤ 1 : then every degree is ≤ 2, apply the handshake bound
      push Not at hdeg
      apply card_edges_le_of_degree_le_two
      intro x
      by_contra hgt
      push Not at hgt
      -- degree x ≥ 3 : extract three distinct neighbours
      have h3 : 2 < ((diameterGraph P D).neighborFinset x).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
      obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp h3
      rw [SimpleGraph.mem_neighborFinset] at hi hj hk
      obtain ⟨mm, _, hmm⟩ := middle_neighbour P hinj D hUB x i j k hi hj hk hij hik hjk
      have h1 : (diameterGraph P D).degree mm ≤ 1 :=
        degree_le_one_of_unique_neighbour P D mm x hmm
      have h2 : 1 < (diameterGraph P D).degree mm := hdeg mm
      omega

end HopfPannwitz
