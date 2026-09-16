import JSP620.Circles
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Avis–Erdős–Pach lower bound for Erdős Problem 754 (JSP-000620)

Let `f n` be the largest `k` such that some set of `n` points in `ℝ⁴` has, at every
point `x`, at least `k` other points at one common distance depending on `x`
(`Erdos754.f`, the definition used by the existing upper-bound formalization).

We formalize the classical lower-bound construction: two orthogonal circles of radius
`1 / √2` in `ℝ⁴`, each carrying finitely many points.  Every point of one circle is at
distance one from every point of the other circle.  Taking `⌈n/2⌉` and `⌊n/2⌋` points
gives `⌊n/2⌋ ≤ f n` for all `n`.  Taking the vertices of `k` inscribed squares on each
circle (all `4k`-th roots of unity, rescaled) additionally gives every point two
neighbours at distance one on its own circle, hence `n/2 + 2 ≤ f n` whenever `8 ∣ n`.
Combined with the existing upper bound `f n ≤ n/2 + 202` this settles
`f n = n/2 + O(1)`.
-/

open Complex Finset

namespace Erdos754Lower

open Erdos754

/-! ## Rescaled roots of unity on a circle -/

/-- A primitive `N`-th root of unity. -/
noncomputable def ζ (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

lemma ζ_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (ζ N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma normSq_ζ_pow (N : ℕ) (hN : N ≠ 0) (m : ℕ) : normSq (ζ N ^ m) = 1 := by
  rw [normSq_eq_norm_sq, norm_pow, (ζ_isPrimitiveRoot N hN).norm'_eq_one hN, one_pow, one_pow]

/-- The `m`-th of `N` equally spaced points on the circle of radius `1 / √2`. -/
noncomputable def pt (N m : ℕ) : ℂ := (ρ : ℂ) * ζ N ^ m

lemma normSq_pt (N : ℕ) (hN : N ≠ 0) (m : ℕ) : normSq (pt N m) = 1 / 2 := by
  rw [pt, normSq_mul, normSq_ofReal, ρ_mul_self, normSq_ζ_pow N hN m, mul_one]

lemma pt_injOn (N : ℕ) (hN : N ≠ 0) : Set.InjOn (pt N) (range N) := by
  intro i hi j hj h
  have hρ : (ρ : ℂ) ≠ 0 := by exact_mod_cast ρ_ne_zero
  have h' : ζ N ^ i = ζ N ^ j := mul_left_cancel₀ hρ h
  exact (ζ_isPrimitiveRoot N hN).pow_inj (mem_range.mp hi) (mem_range.mp hj) h'

/-- `N` distinct points on the circle of radius `1 / √2`. -/
noncomputable def circ (N : ℕ) : Finset ℂ := (range N).image (pt N)

lemma card_circ (N : ℕ) (hN : N ≠ 0) : (circ N).card = N := by
  rw [circ, card_image_of_injOn (pt_injOn N hN), card_range]

lemma normSq_of_mem_circ {N : ℕ} (hN : N ≠ 0) {w : ℂ} (hw : w ∈ circ N) :
    normSq w = 1 / 2 := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  exact normSq_pt N hN m

/-! ## Rotation by a right angle on `4k` points -/

lemma ζ_pow_quarter (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ k = I := by
  unfold ζ
  rw [← Complex.exp_nat_mul]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have : (k : ℂ) * (2 * Real.pi * I / ((4 * k : ℕ) : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma ζ_pow_three_quarter (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ (3 * k) = -I := by
  rw [pow_mul', ζ_pow_quarter k hk, pow_succ, I_sq]
  ring

lemma ζ_pow_full (k : ℕ) (hk : k ≠ 0) : ζ (4 * k) ^ (4 * k) = 1 :=
  (ζ_isPrimitiveRoot (4 * k) (by omega)).pow_eq_one

lemma pt_mul_I (k : ℕ) (hk : k ≠ 0) (m : ℕ) :
    pt (4 * k) m * I = pt (4 * k) ((m + k) % (4 * k)) := by
  rw [pt, pt, mul_assoc, ← ζ_pow_quarter k hk, ← pow_add,
    pow_eq_pow_mod (m + k) (ζ_pow_full k hk)]

lemma pt_mul_neg_I (k : ℕ) (hk : k ≠ 0) (m : ℕ) :
    pt (4 * k) m * (-I) = pt (4 * k) ((m + 3 * k) % (4 * k)) := by
  rw [pt, pt, mul_assoc, ← ζ_pow_three_quarter k hk, ← pow_add,
    pow_eq_pow_mod (m + 3 * k) (ζ_pow_full k hk)]

lemma mul_I_mem_circ {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ∈ circ (4 * k)) :
    w * I ∈ circ (4 * k) := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  rw [pt_mul_I k hk m]
  exact mem_image.mpr ⟨_, mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩

lemma mul_neg_I_mem_circ {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ∈ circ (4 * k)) :
    w * (-I) ∈ circ (4 * k) := by
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  rw [pt_mul_neg_I k hk m]
  exact mem_image.mpr ⟨_, mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩

/-! ## The point set and its favorite-distance degrees -/

/-- The two-circle point set determined by parameter sets `X` (first circle) and
`Y` (second circle). -/
noncomputable def pts (X Y : Finset ℂ) : Finset E4 := X.image e1 ∪ Y.image e2

/-- A parameter set lies on the circle of radius `1 / √2`. -/
def OnCircle (X : Finset ℂ) : Prop := ∀ w ∈ X, normSq w = 1 / 2

lemma onCircle_circ (N : ℕ) (hN : N ≠ 0) : OnCircle (circ N) :=
  fun _ hw => normSq_of_mem_circ hN hw

lemma disjoint_images {X Y : Finset ℂ} (hX : OnCircle X) :
    Disjoint (X.image e1) (Y.image e2) := by
  rw [disjoint_left]
  intro x hx hy
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
  obtain ⟨v, -, hvx⟩ := mem_image.mp hy
  exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hvx.symm

lemma card_pts {X Y : Finset ℂ} (hX : OnCircle X) : (pts X Y).card = X.card + Y.card := by
  rw [pts, card_union_of_disjoint (disjoint_images hX),
    card_image_of_injective _ e1_injective, card_image_of_injective _ e2_injective]

/-- The number of points of `P` other than `x` at distance one from `x`. -/
noncomputable def unitDeg (P : Finset E4) (x : E4) : ℕ :=
  open scoped Classical in
  (P.filter fun y => y ≠ x ∧ dist x y = 1).card

/-- With the constant favorite distance one, `Erdos754.favoriteDegree` is `unitDeg`. -/
lemma favoriteDegree_const_one (P : Finset E4) (x : P) :
    favoriteDegree P (fun _ => (1 : ℝ)) x = unitDeg P x := by
  classical
  unfold favoriteDegree unitDeg
  refine Finset.card_bij (fun y _ => (y : E4)) ?_ ?_ ?_
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    refine Finset.mem_filter.mpr ⟨y.property, ?_, hy'.2⟩
    intro h
    exact hy'.1 (Subtype.ext h.symm)
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, hy'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hy'.2.2⟩, rfl⟩
    intro h
    exact hy'.2.1 (congrArg Subtype.val h).symm

lemma card_le_unitDeg {P T : Finset E4} {x : E4} (hT : T ⊆ P)
    (hne : ∀ y ∈ T, y ≠ x) (hd : ∀ y ∈ T, dist x y = 1) : T.card ≤ unitDeg P x := by
  classical
  unfold unitDeg
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨hT hy, hne y hy, hd y hy⟩

lemma unitDeg_e1_ge {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y) {w : ℂ}
    (hw : w ∈ X) : Y.card ≤ unitDeg (pts X Y) (e1 w) := by
  have h := card_le_unitDeg (P := pts X Y) (T := Y.image e2) (x := e1 w)
    (fun y hy => Finset.mem_union_right _ hy)
    (by
      intro y hy
      obtain ⟨v, -, rfl⟩ := mem_image.mp hy
      exact (e1_ne_e2 (ne_zero_of_normSq (hX w hw))).symm)
    (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      exact dist_e1_e2 (hX w hw) (hY v hv))
  rwa [card_image_of_injective _ e2_injective] at h

lemma unitDeg_e2_ge {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y) {v : ℂ}
    (hv : v ∈ Y) : X.card ≤ unitDeg (pts X Y) (e2 v) := by
  have h := card_le_unitDeg (P := pts X Y) (T := X.image e1) (x := e2 v)
    (fun y hy => Finset.mem_union_left _ hy)
    (by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
      exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)))
    (by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
      exact dist_e2_e1 (hY v hv) (hX w hw))
  rwa [card_image_of_injective _ e1_injective] at h

/-- A parameter set closed under rotation by a right angle. -/
def RotClosed (X : Finset ℂ) : Prop := ∀ w ∈ X, w * I ∈ X ∧ w * (-I) ∈ X

lemma rotClosed_circ (k : ℕ) (hk : k ≠ 0) : RotClosed (circ (4 * k)) :=
  fun _ hw => ⟨mul_I_mem_circ hk hw, mul_neg_I_mem_circ hk hw⟩

lemma unitDeg_e1_ge_rot {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y)
    (hXr : RotClosed X) {w : ℂ} (hw : w ∈ X) :
    Y.card + 2 ≤ unitDeg (pts X Y) (e1 w) := by
  classical
  have hw0 : w ≠ 0 := ne_zero_of_normSq (hX w hw)
  have hwI := (hXr w hw).1
  have hwI' := (hXr w hw).2
  have hnot1 : e1 (w * I) ∉ Y.image e2 := by
    intro h
    obtain ⟨v, -, hv⟩ := mem_image.mp h
    exact e1_ne_e2 (ne_zero_of_normSq (hX _ hwI)) hv.symm
  have hnot2 : e1 (w * (-I)) ∉ insert (e1 (w * I)) (Y.image e2) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact mul_I_ne_mul_neg_I hw0 (e1_injective h).symm
    · obtain ⟨v, -, hv⟩ := mem_image.mp h
      exact e1_ne_e2 (ne_zero_of_normSq (hX _ hwI')) hv.symm
  have h := card_le_unitDeg (P := pts X Y)
    (T := insert (e1 (w * (-I))) (insert (e1 (w * I)) (Y.image e2))) (x := e1 w)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_left _ (mem_image.mpr ⟨_, hwI', rfl⟩)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_left _ (mem_image.mpr ⟨_, hwI, rfl⟩)
      · exact Finset.mem_union_right _ hy)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_neg_I_ne_self hw0 (e1_injective h)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_I_ne_self hw0 (e1_injective h)
      · obtain ⟨v, -, rfl⟩ := mem_image.mp hy
        exact (e1_ne_e2 hw0).symm)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e1_rot' (hX w hw)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e1_rot (hX w hw)
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
        exact dist_e1_e2 (hX w hw) (hY v hv))
  rwa [card_insert_of_notMem hnot2, card_insert_of_notMem hnot1,
    card_image_of_injective _ e2_injective] at h

lemma unitDeg_e2_ge_rot {X Y : Finset ℂ} (hX : OnCircle X) (hY : OnCircle Y)
    (hYr : RotClosed Y) {v : ℂ} (hv : v ∈ Y) :
    X.card + 2 ≤ unitDeg (pts X Y) (e2 v) := by
  classical
  have hv0 : v ≠ 0 := ne_zero_of_normSq (hY v hv)
  have hvI := (hYr v hv).1
  have hvI' := (hYr v hv).2
  have hnot1 : e2 (v * I) ∉ X.image e1 := by
    intro h
    obtain ⟨w, hw, hw'⟩ := mem_image.mp h
    exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hw'
  have hnot2 : e2 (v * (-I)) ∉ insert (e2 (v * I)) (X.image e1) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact mul_I_ne_mul_neg_I hv0 (e2_injective h).symm
    · obtain ⟨w, hw, hw'⟩ := mem_image.mp h
      exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)) hw'
  have h := card_le_unitDeg (P := pts X Y)
    (T := insert (e2 (v * (-I))) (insert (e2 (v * I)) (X.image e1))) (x := e2 v)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ (mem_image.mpr ⟨_, hvI', rfl⟩)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ (mem_image.mpr ⟨_, hvI, rfl⟩)
      · exact Finset.mem_union_left _ hy)
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_neg_I_ne_self hv0 (e2_injective h)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro h
        exact mul_I_ne_self hv0 (e2_injective h)
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
        exact e1_ne_e2 (ne_zero_of_normSq (hX w hw)))
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e2_rot' (hY v hv)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact dist_e2_rot (hY v hv)
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
        exact dist_e2_e1 (hY v hv) (hX w hw))
  rwa [card_insert_of_notMem hnot2, card_insert_of_notMem hnot1,
    card_image_of_injective _ e1_injective] at h

/-! ## Attainable values -/

lemma attainable_of_forall_unitDeg {P : Finset E4} {k : ℕ}
    (h : ∀ x ∈ P, k ≤ unitDeg P x) : Attainable P.card k := by
  refine ⟨P, rfl, fun _ => 1, fun _ => one_pos, fun x => ?_⟩
  rw [favoriteDegree_const_one]
  exact h x x.property

lemma forall_mem_pts {X Y : Finset ℂ} {p : E4 → Prop}
    (h1 : ∀ w ∈ X, p (e1 w)) (h2 : ∀ v ∈ Y, p (e2 v)) : ∀ x ∈ pts X Y, p x := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
    exact h1 w hw
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact h2 v hv

/-- Two circles carrying `a` and `b` points: every point has at least `min a b` others
at distance one. -/
lemma attainable_two_circles (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Attainable (a + b) (min a b) := by
  have hX := onCircle_circ a ha
  have hY := onCircle_circ b hb
  have hcard : (pts (circ a) (circ b)).card = a + b := by
    rw [card_pts hX, card_circ a ha, card_circ b hb]
  rw [← hcard]
  apply attainable_of_forall_unitDeg
  apply forall_mem_pts
  · intro w hw
    exact le_trans (by rw [card_circ b hb]; exact min_le_right a b) (unitDeg_e1_ge hX hY hw)
  · intro v hv
    exact le_trans (by rw [card_circ a ha]; exact min_le_left a b) (unitDeg_e2_ge hX hY hv)

/-- Two circles each carrying the vertices of `k` inscribed squares: every point has at
least `4k + 2` others at distance one. -/
lemma attainable_squares (k : ℕ) (hk : k ≠ 0) : Attainable (8 * k) (4 * k + 2) := by
  have h4 : 4 * k ≠ 0 := by omega
  have hX := onCircle_circ (4 * k) h4
  have hXr := rotClosed_circ k hk
  have hcard : (pts (circ (4 * k)) (circ (4 * k))).card = 8 * k := by
    rw [card_pts hX, card_circ _ h4]
    ring
  rw [← hcard]
  apply attainable_of_forall_unitDeg
  apply forall_mem_pts
  · intro w hw
    have := unitDeg_e1_ge_rot hX hX hXr hw
    rwa [card_circ _ h4] at this
  · intro v hv
    have := unitDeg_e2_ge_rot hX hX hXr hv
    rwa [card_circ _ h4] at this

lemma le_f_of_attainable {n k : ℕ} (hn : n ≠ 0) (h : Attainable n k) : k ≤ f n := by
  have hf : f n = sSup {k : ℕ | Attainable n k} := by simp [f, hn]
  rw [hf]
  exact le_csSup (attainable_bddAbove n hn) h

/-! ## The lower bounds -/

/-- For every `n`, some `n`-point set in `ℝ⁴` has every point at distance one from at
least `⌊n/2⌋` other points. -/
theorem half_le_f (n : ℕ) : n / 2 ≤ f n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hb : n / 2 ≠ 0 := by omega
    have ha : n - n / 2 ≠ 0 := by omega
    have h := attainable_two_circles (n - n / 2) (n / 2) ha hb
    have hsum : n - n / 2 + n / 2 = n := by omega
    have hmin : min (n - n / 2) (n / 2) = n / 2 := by
      apply min_eq_right
      omega
    rw [hsum, hmin] at h
    exact le_f_of_attainable (by omega) h

/-- For `n = 8k` with `k ≥ 1`, some `n`-point set in `ℝ⁴` has every point at distance
one from at least `n/2 + 2` other points (Avis–Erdős–Pach). -/
theorem f_eight_mul (k : ℕ) (hk : k ≠ 0) : 4 * k + 2 ≤ f (8 * k) :=
  le_f_of_attainable (by omega) (attainable_squares k hk)

theorem half_add_two_le_f_of_eight_dvd (n : ℕ) (hn : n ≠ 0) (h8 : 8 ∣ n) :
    n / 2 + 2 ≤ f n := by
  obtain ⟨k, rfl⟩ := h8
  have hk : k ≠ 0 := by omega
  have := f_eight_mul k hk
  have h2 : 8 * k / 2 = 4 * k := by omega
  rw [h2]
  exact this

end Erdos754Lower
