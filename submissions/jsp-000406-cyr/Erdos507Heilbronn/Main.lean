import Mathlib

/-!
# Erdős Problem #507 (Heilbronn's triangle problem): the trivial bounds `1/n² ≪ α(n) ≪ 1/n`

Let `α(n)` be such that every set of `n` points in the unit disk contains three points which
determine a triangle of area at most `α(n)` (the supremum, over `n`-point sets `S` in the disk not
all collinear, of the minimum triangle area of `S`).  Heilbronn's problem asks to estimate
`α(n)` (OPEN; `log n / n² ≪ α(n) ≪ n^{-8/7-1/2000}`).  The problem page records the two
elementary facts: "it is trivial that `α(n) ≪ 1/n`" and "Erdős observed that `α(n) ≫ 1/n²`".
This file proves both, in the exact shape of the formal-conjectures statements
`Erdos507.erdos_507.variants.upper_trivial` and `lower_erdos` (tagged "research solved" with
`sorry`; the formal-conjectures notations `f ≪ g`, `f ≫ g` mean `IsBigO atTop` on `ℕ → ℝ`), with
the definitions `minTriangleArea`, `α` and the helper `EuclideanGeometry.triangle_area`
(oriented area form) copied from the formal-conjectures repository.

Proof.  Upper bound: cut the disk into `⌊(n−1)/2⌋` horizontal strips of height `4/(n−1)`; some
strip contains three points, and a triangle inside a strip of height `h` and width `2` has area
at most `h`, so every `n`-point set has a triangle of area `≪ 1/n`.  Lower bound: for a prime
`p ∈ [n, 2n)` the points `(i/(2p), (i² mod p)/(2p))`, `i < n`, lie in the disk and any three of them
are non-collinear with area at least `1/(8p²)` (the integer determinant is `≡ (j−i)(k−i)(k−j) ≢ 0
(mod p)`).  The true order of `α(n)` is not addressed.
-/

open Asymptotics Filter Topology

/-- Oriented angles make sense in 2d (formal-conjectures instance). -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- Two dimensional euclidean space is two-dimensional (formal-conjectures instance). -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Signed area of the triangle `a b c` (formal-conjectures definition, specialised to `ℝ²`). -/
noncomputable def EuclideanGeometry.triangle_area (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2

/-- The minimum (unsigned) area of a triangle determined by three distinct points in a set `S`
(formal-conjectures definition). -/
noncomputable def minTriangleArea (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
    (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)}

/-- `α(n)` is the supremum of `minTriangleArea S` over all sets `S` of `n` points in the unit
disk (formal-conjectures definition). -/
noncomputable def α (n : ℕ) : ℝ :=
  sSup (minTriangleArea '' { S : Finset (EuclideanSpace ℝ (Fin 2)) |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) })

/-- The signed area as a determinant (formal-conjectures lemma `triangle_area_eq_det`). -/
theorem triangle_area_eq_det (a b c : EuclideanSpace ℝ (Fin 2)) :
    EuclideanGeometry.triangle_area a b c =
      ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
  rw [EuclideanGeometry.triangle_area, Orientation.areaForm_to_volumeForm,
    positiveOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Matrix.det_fin_two, Module.Basis.toMatrix]

/-! ### Auxiliary lemmas

General facts about `triangle_area`, `minTriangleArea` and `α` used in both bounds. -/

private lemma abs_coord_le_one {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (i : Fin 2) : |x i| ≤ 1 := by
  rw [mem_closedBall_zero_iff] at hx
  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 2 => ℝ) x i
  rw [Real.norm_eq_abs] at h
  linarith

private lemma abs_area_le {a b c : EuclideanSpace ℝ (Fin 2)} {h : ℝ} (_hh : 0 ≤ h)
    (ha0 : |a 0 - c 0| ≤ 2) (hb0 : |b 0 - c 0| ≤ 2)
    (ha1 : |a 1 - c 1| ≤ h) (hb1 : |b 1 - c 1| ≤ h) :
    |EuclideanGeometry.triangle_area a b c| ≤ 2 * h := by
  rw [triangle_area_eq_det, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have k1 : |(a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)|
      ≤ |(a 0 - c 0) * (b 1 - c 1)| + |(b 0 - c 0) * (a 1 - c 1)| := abs_sub _ _
  rw [abs_mul, abs_mul] at k1
  have n1 := abs_nonneg (a 0 - c 0)
  have n2 := abs_nonneg (b 0 - c 0)
  have n3 := abs_nonneg (a 1 - c 1)
  have n4 := abs_nonneg (b 1 - c 1)
  nlinarith

private lemma bddBelow_areas (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    BddBelow {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
      (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)} := by
  refine ⟨0, ?_⟩
  rintro x ⟨p, -, -, rfl⟩
  exact abs_nonneg _

private lemma minTriangleArea_nonneg (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    0 ≤ minTriangleArea S := by
  apply Real.sInf_nonneg
  rintro x ⟨p, -, -, rfl⟩
  exact abs_nonneg _

private lemma minTriangleArea_le_of_mem {S : Finset (EuclideanSpace ℝ (Fin 2))}
    {a b c : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    minTriangleArea S ≤ |EuclideanGeometry.triangle_area a b c| := by
  apply csInf_le (bddBelow_areas S)
  refine ⟨![a, b, c], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simpa
  · simp

private lemma minTriangleArea_le_four {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hS : ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : minTriangleArea S ≤ 4 := by
  rcases Set.eq_empty_or_nonempty {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
      (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)}
    with he | ⟨x, hx⟩
  · rw [minTriangleArea, he, Real.sInf_empty]; norm_num
  · refine le_trans (csInf_le (bddBelow_areas S) hx) ?_
    obtain ⟨p, -, hmem, rfl⟩ := hx
    have hb : ∀ i, |p i 0| ≤ 1 ∧ |p i 1| ≤ 1 := fun i =>
      ⟨abs_coord_le_one (hS (hmem i)) 0, abs_coord_le_one (hS (hmem i)) 1⟩
    have e : (4:ℝ) = 2 * 2 := by norm_num
    rw [e]
    refine abs_area_le (by norm_num) ?_ ?_ ?_ ?_ <;>
      · rcases hb 0 with ⟨u1, u2⟩; rcases hb 1 with ⟨v1, v2⟩; rcases hb 2 with ⟨w1, w2⟩
        rw [abs_le] at u1 u2 v1 v2 w1 w2 ⊢
        constructor <;> linarith [u1.1, u1.2, u2.1, u2.2, v1.1, v1.2, v2.1, v2.2, w1.1, w1.2, w2.1, w2.2]

private lemma bddAbove_image (n : ℕ) :
    BddAbove (minTriangleArea '' { S : Finset (EuclideanSpace ℝ (Fin 2)) |
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) }) := by
  refine ⟨4, ?_⟩
  rintro y ⟨S, hS, rfl⟩
  exact minTriangleArea_le_four hS.2.1

private lemma alpha_nonneg (n : ℕ) : 0 ≤ α n := by
  rcases Set.eq_empty_or_nonempty (minTriangleArea '' { S : Finset (EuclideanSpace ℝ (Fin 2)) |
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) }) with he | ⟨y, hy⟩
  · rw [α, he, Real.sSup_empty]
  · obtain ⟨S, hS, rfl⟩ := hy
    exact le_trans (minTriangleArea_nonneg S) (le_csSup (bddAbove_image n) ⟨S, hS, rfl⟩)

private lemma triangle_area_eq_zero_of_collinear {s : Set (EuclideanSpace ℝ (Fin 2))}
    (h : Collinear ℝ s) {a b c : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    EuclideanGeometry.triangle_area a b c = 0 := by
  rw [collinear_iff_of_mem hc] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, rfl⟩ := hv a ha
  obtain ⟨t, rfl⟩ := hv b hb
  simp [EuclideanGeometry.triangle_area]

private lemma strip_bound {m : ℕ} (hm : 0 < m) {x y : ℝ} (hx : -1 ≤ x) (hy : -1 ≤ y)
    (h : ⌊(x + 1) * m / 2⌋₊ = ⌊(y + 1) * m / 2⌋₊) : |x - y| ≤ 2 / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ (x + 1) * m / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) hm'.le
  have hy0 : 0 ≤ (y + 1) * m / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) hm'.le
  have h1 := Nat.floor_le hx0
  have h2 := Nat.lt_floor_add_one ((x + 1) * m / 2)
  have h3 := Nat.floor_le hy0
  have h4 := Nat.lt_floor_add_one ((y + 1) * m / 2)
  rw [h] at h1 h2
  rw [abs_le]
  constructor
  · have e : -(2/(m:ℝ)) = (-2)/m := by ring
    rw [e, div_le_iff₀ hm']
    nlinarith
  · rw [le_div_iff₀ hm']
    nlinarith

private lemma minTriangleArea_le_of_card {n : ℕ} (hn : 6 ≤ n)
    {S : Finset (EuclideanSpace ℝ (Fin 2))} (hcard : S.card = n)
    (hS : ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    minTriangleArea S ≤ 32 / n := by
  classical
  set m : ℕ := n / 4 with hmdef
  have hm : 0 < m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hlt : (Finset.range (m + 1)).card * 2 < S.card := by
    rw [Finset.card_range, hcard]; omega
  set f : EuclideanSpace ℝ (Fin 2) → ℕ := fun x => ⌊(x 1 + 1) * m / 2⌋₊ with hfdef
  have hmaps : ∀ a ∈ S, f a ∈ Finset.range (m + 1) := by
    intro a ha
    have h1 : |a 1| ≤ 1 := abs_coord_le_one (hS ha) 1
    rw [abs_le] at h1
    rw [Finset.mem_range, Nat.lt_succ_iff, hfdef]
    have : (a 1 + 1) * m / 2 ≤ (m : ℝ) := by nlinarith
    calc ⌊(a 1 + 1) * m / 2⌋₊ ≤ ⌊(m : ℝ)⌋₊ := Nat.floor_le_floor this
      _ = m := Nat.floor_natCast m
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hj
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hTcard
  have hmem : ∀ x ∈ ({a, b, c} : Finset (EuclideanSpace ℝ (Fin 2))),
      x ∈ S ∧ f x = j := by
    intro x hx
    have := hTsub hx
    simp only [Finset.mem_filter] at this
    exact this
  obtain ⟨haS, hfa⟩ := hmem a (by simp)
  obtain ⟨hbS, hfb⟩ := hmem b (by simp)
  obtain ⟨hcS, hfc⟩ := hmem c (by simp)
  have hstrip : ∀ x y : EuclideanSpace ℝ (Fin 2), x ∈ S → y ∈ S → f x = f y →
      |x 1 - y 1| ≤ 2 / m := by
    intro x y hx hy hxy
    have h1 : |x 1| ≤ 1 := abs_coord_le_one (hS hx) 1
    have h2 : |y 1| ≤ 1 := abs_coord_le_one (hS hy) 1
    rw [abs_le] at h1 h2
    exact strip_bound hm h1.1 h2.1 hxy
  have hx0 : ∀ x y : EuclideanSpace ℝ (Fin 2), x ∈ S → y ∈ S → |x 0 - y 0| ≤ 2 := by
    intro x y hx hy
    have h1 : |x 0| ≤ 1 := abs_coord_le_one (hS hx) 0
    have h2 : |y 0| ≤ 1 := abs_coord_le_one (hS hy) 0
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have harea : |EuclideanGeometry.triangle_area a b c| ≤ 2 * (2 / m) :=
    abs_area_le (by positivity) (hx0 a c haS hcS) (hx0 b c hbS hcS)
      (hstrip a c haS hcS (hfa.trans hfc.symm)) (hstrip b c hbS hcS (hfb.trans hfc.symm))
  have hle := (minTriangleArea_le_of_mem haS hbS hcS hab hac hbc).trans harea
  refine hle.trans ?_
  have hnm : (n : ℝ) ≤ 7 * m := by
    have : n ≤ 7 * m := by omega
    exact_mod_cast this
  have hn0 : (0:ℝ) < n := by positivity
  have hrw : (2:ℝ) * (2 / m) = 4 / m := by ring
  rw [hrw, div_le_div_iff₀ hm' hn0]
  linarith

/-- **The trivial upper bound.**  `α(n) ≪ 1/n` (formal-conjectures `upper_trivial`). -/
theorem erdos_507_upper_trivial : α =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  refine IsBigO.of_bound 32 ?_
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hn0 : (0:ℝ) < n := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (alpha_nonneg n),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))]
  have : α n ≤ 32 / n := by
    rw [α]
    refine Real.sSup_le ?_ (by positivity)
    rintro x ⟨S, hS, rfl⟩
    exact minTriangleArea_le_of_card hn hS.1 hS.2.1
  calc α n ≤ 32 / n := this
    _ = 32 * (1 / n) := by ring

/-! ### The Erdős point configuration

For a prime `p` the points `(i/(2p), (i² mod p)/(2p))` lie in the unit disk and any three of them
span a triangle of area at least `1/(8p²)`. -/

private noncomputable def erdosPt (p i : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(i : ℝ) / (2 * p), ((i ^ 2 % p : ℕ) : ℝ) / (2 * p)]

private lemma erdosPt_zero (p i : ℕ) : erdosPt p i 0 = (i : ℝ) / (2 * p) := by
  simp [erdosPt]

private lemma erdosPt_one (p i : ℕ) : erdosPt p i 1 = ((i ^ 2 % p : ℕ) : ℝ) / (2 * p) := by
  simp [erdosPt]

private lemma erdosPt_injective {p : ℕ} (hp : 0 < p) : Function.Injective (erdosPt p) := by
  intro i j hij
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
  rw [erdosPt_zero, erdosPt_zero] at h
  have hp' : (0:ℝ) < 2 * p := by positivity
  field_simp at h
  exact_mod_cast h

private lemma erdosPt_mem_ball {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    erdosPt p i ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have h0 : |erdosPt p i 0| ≤ 1/2 := by
    rw [erdosPt_zero, abs_le]
    have : (i:ℝ) ≤ p := by exact_mod_cast hi.le
    constructor
    · rw [le_div_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1 : |erdosPt p i 1| ≤ 1/2 := by
    rw [erdosPt_one, abs_le]
    have : ((i ^ 2 % p : ℕ) : ℝ) ≤ p := by
      have := (Nat.mod_lt (i^2) hp).le
      exact_mod_cast this
    constructor
    · rw [le_div_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) (i^2 % p)]
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have e : √((‖(erdosPt p i).ofLp 0‖) ^ 2 + (‖(erdosPt p i).ofLp 1‖) ^ 2) ≤ √1 := by
    apply Real.sqrt_le_sqrt
    simp only [Real.norm_eq_abs]
    have := abs_nonneg (erdosPt p i 0)
    have := abs_nonneg (erdosPt p i 1)
    nlinarith [h0, h1]
  simpa using e

private lemma det_quot (P : ℝ) (hP : P ≠ 0) (A B C U V W : ℝ) :
    ((A / (2 * P) - C / (2 * P)) * (V / (2 * P) - W / (2 * P))
      - (B / (2 * P) - C / (2 * P)) * (U / (2 * P) - W / (2 * P))) / 2
      = ((A - C) * (V - W) - (B - C) * (U - W)) / (8 * P ^ 2) := by
  field_simp
  ring

private lemma erdosPt_area_lower {p : ℕ} (hp : p.Prime) {i j k : ℕ}
    (hi : i < p) (hj : j < p) (hk : k < p) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    1 / (8 * (p:ℝ)^2) ≤
      |EuclideanGeometry.triangle_area (erdosPt p i) (erdosPt p j) (erdosPt p k)| := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  set D : ℤ := ((i:ℤ) - k) * (((j ^ 2 % p : ℕ):ℤ) - ((k ^ 2 % p : ℕ):ℤ))
             - ((j:ℤ) - k) * (((i ^ 2 % p : ℕ):ℤ) - ((k ^ 2 % p : ℕ):ℤ)) with hD
  have hcast : ((D : ℤ) : ZMod p)
      = ((i : ZMod p) - k) * ((j : ZMod p) - k) * ((j : ZMod p) - i) := by
    rw [hD]; push_cast [ZMod.natCast_mod]; ring
  have hne : ∀ u v : ℕ, u < p → v < p → u ≠ v → ((u : ZMod p) - v) ≠ 0 := by
    intro u v hu hv huv hcontra
    apply huv
    have heq : (u : ZMod p) = v := by
      have := sub_eq_zero.1 hcontra
      exact this
    have := congrArg ZMod.val heq
    rwa [ZMod.val_cast_of_lt hu, ZMod.val_cast_of_lt hv] at this
  have hDne : D ≠ 0 := by
    intro h0
    have hz : ((D:ℤ) : ZMod p) = 0 := by rw [h0]; simp
    rw [hcast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact hne i k hi hk hik h'
      · exact hne j k hj hk hjk h'
    · exact hne j i hj hi (Ne.symm hij) h
  have harea : EuclideanGeometry.triangle_area (erdosPt p i) (erdosPt p j) (erdosPt p k)
      = (D : ℝ) / (8 * (p:ℝ)^2) := by
    simp only [triangle_area_eq_det, erdosPt_zero, erdosPt_one]
    rw [det_quot (p:ℝ) (ne_of_gt hpR), hD]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hone : (1:ℝ) ≤ |(D:ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hDne
  rw [harea, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * (p:ℝ)^2)]
  gcongr

private lemma areas_nonempty {S : Finset (EuclideanSpace ℝ (Fin 2))}
    {a b c : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Set.Nonempty {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
      (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)} := by
  refine ⟨_, ![a, b, c], ?_, ?_, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simpa

/-- **Erdős's lower bound.**  `α(n) ≫ 1/n²` (formal-conjectures `lower_erdos`). -/
theorem erdos_507_lower_erdos : (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) =O[atTop] α := by
  refine IsBigO.of_bound 32 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hp0 : 0 < p := hp.pos
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set S : Finset (EuclideanSpace ℝ (Fin 2)) := (Finset.range n).image (erdosPt p) with hSdef
  have hmemS : ∀ i, i < n → erdosPt p i ∈ S := by
    intro i hi
    rw [hSdef]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hi)
  have hSmem : ∀ x ∈ S, ∃ i, i < n ∧ erdosPt p i = x := by
    intro x hx
    rw [hSdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.mem_range.1 hi, rfl⟩
  have hcard : S.card = n := by
    rw [hSdef, Finset.card_image_of_injective _ (erdosPt_injective hp0), Finset.card_range]
  have hball : ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hSmem x (Finset.mem_coe.1 hx)
    exact erdosPt_mem_ball hp0 (by omega)
  have hdistinct : ∀ u v : ℕ, u ≠ v → erdosPt p u ≠ erdosPt p v := by
    intro u v huv h
    exact huv (erdosPt_injective hp0 h)
  have harea012 : 1 / (8 * (p:ℝ)^2) ≤
      |EuclideanGeometry.triangle_area (erdosPt p 0) (erdosPt p 1) (erdosPt p 2)| :=
    erdosPt_area_lower hp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hpos : (0:ℝ) < 1 / (8 * (p:ℝ)^2) := by positivity
  have hncol : ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hcol
    have hz := triangle_area_eq_zero_of_collinear hcol
      (Finset.mem_coe.2 (hmemS 0 (by omega))) (Finset.mem_coe.2 (hmemS 1 (by omega)))
      (Finset.mem_coe.2 (hmemS 2 (by omega)))
    rw [hz, abs_zero] at harea012
    linarith
  have hmin : 1 / (8 * (p:ℝ)^2) ≤ minTriangleArea S := by
    refine le_csInf (areas_nonempty (hmemS 0 (by omega)) (hmemS 1 (by omega)) (hmemS 2 (by omega))
      (hdistinct 0 1 (by omega)) (hdistinct 0 2 (by omega)) (hdistinct 1 2 (by omega))) ?_
    rintro x ⟨q, hq, hqS, rfl⟩
    choose t ht hPt using fun idx => hSmem (q idx) (hqS idx)
    have hdist : ∀ u v : Fin 3, u ≠ v → t u ≠ t v := by
      intro u v huv hE
      exact huv (hq (by rw [← hPt u, ← hPt v, hE]))
    rw [← hPt 0, ← hPt 1, ← hPt 2]
    exact erdosPt_area_lower (i := t 0) (j := t 1) (k := t 2) hp
      (lt_trans (ht 0) hnp) (lt_trans (ht 1) hnp) (lt_trans (ht 2) hnp)
      (hdist 0 1 (by decide)) (hdist 0 2 (by decide)) (hdist 1 2 (by decide))
  have hAn : 1 / (8 * (p:ℝ)^2) ≤ α n := by
    refine hmin.trans ?_
    exact le_csSup (bddAbove_image n) ⟨S, ⟨hcard, hball, hncol⟩, rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (alpha_nonneg n),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ)^2)]
  have hple : (p:ℝ) ≤ 2 * n := by exact_mod_cast hp2n
  have h1 : 1 / (n:ℝ)^2 ≤ 4 / (p:ℝ)^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 4 / (p:ℝ)^2 = 32 * (1 / (8 * (p:ℝ)^2)) := by
    field_simp
    norm_num
  linarith [mul_le_mul_of_nonneg_left hAn (by norm_num : (0:ℝ) ≤ 32)]


/-- **Erdős #507, the elementary bounds.**  `α(n) ≪ 1/n` and `α(n) ≫ 1/n²`.  The order of
`α(n)` is open and not claimed. -/
theorem erdos_507_trivial_bounds :
    (α =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) ∧ ((fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) =O[atTop] α) :=
  ⟨erdos_507_upper_trivial, erdos_507_lower_erdos⟩
