import Mathlib

/-!
# Erdős Problem #704: the trivial cube-tiling colouring `χ(G_n) ≤ (2 + √n)^n`

Let `G_n` be the unit-distance graph of `ℝ^n` (two points adjacent iff at distance exactly `1`).
Erdős asked to estimate the chromatic number `χ(G_n)`, whether it grows exponentially, and
whether `lim χ(G_n)^{1/n}` exists (OPEN; not addressed here).  The problem page records: "The
trivial colouring (by tiling with cubes) gives `χ(G_n) ≤ (2 + √n)^n`."  This file proves that
bound.  There is no formal-conjectures file for #704, so the definition of `G_n` below is ours
(a `SimpleGraph` on `EuclideanSpace ℝ (Fin n)` with adjacency `dist x y = 1`).  The Frankl–Wilson
and Raigorodsky lower bounds, the Larman–Rogers bound and the open questions are not claimed.

Proof.  Let `s = 1/√n` (for `n ≥ 1`) and `k = ⌈√n⌉₊ + 1`.  Colour `x` by the vector of residues
`(⌊x_i / s⌋ mod k)_{i < n}`, a colouring with `k^n` colours.  If `x` and `y` get the same colour,
then for each `i` either `⌊x_i/s⌋ = ⌊y_i/s⌋`, so `|x_i − y_i| < s`, or the two floors differ by
at least `k`, so `|x_i − y_i| > (k − 1) s ≥ 1`.  In the first case for all `i` we get
`dist x y < √(n s²) = 1`; otherwise `dist x y > 1`; either way `dist x y ≠ 1`.  Finally
`k^n = (⌈√n⌉₊ + 1)^n ≤ (2 + √n)^n`.  (For `n = 0` the graph has one vertex.)
-/

/-- The unit-distance graph `G_n` of `ℝ^n`. -/
def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := dist x y = 1
  symm := ⟨fun x y h => (dist_comm y x).trans h⟩
  loopless := ⟨fun x h => by change dist x x = 1 at h; simp at h⟩

/-- Floors move by less than one more than their arguments: `|⌊a⌋ - ⌊b⌋| < |a - b| + 1`. -/
lemma erdos704_floor_abs_lt (a b : ℝ) :
    |((⌊a⌋ : ℤ) : ℝ) - ((⌊b⌋ : ℤ) : ℝ)| < |a - b| + 1 := by
  have ha1 := Int.floor_le a
  have ha2 := Int.lt_floor_add_one a
  have hb1 := Int.floor_le b
  have hb2 := Int.lt_floor_add_one b
  have h1 : a - b ≤ |a - b| := le_abs_self _
  have h2 : -(a - b) ≤ |a - b| := neg_le_abs _
  rw [abs_lt]
  constructor <;> linarith

/-- Each coordinate difference is bounded by the Euclidean distance. -/
private lemma erdos704_coord_le_dist (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x.ofLp i - y.ofLp i| ≤ dist x y := by
  rw [EuclideanSpace.dist_eq, ← Real.dist_eq, Real.le_sqrt dist_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun j => dist (x.ofLp j) (y.ofLp j) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

/-- The cube-tiling colouring: if `√n ≤ m` then `G_n` is `(m+1)^n`-colourable. -/
private lemma erdos704_colorable (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : Real.sqrt n ≤ m) :
    (unitDistanceGraph n).Colorable ((m + 1) ^ n) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set σ := Real.sqrt n with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hnpos
  have hσsq : σ ^ 2 = (n:ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have C : (unitDistanceGraph n).Coloring (Fin n → ZMod (m + 1)) := by
    refine SimpleGraph.Coloring.mk
      (fun x i => ((⌊x.ofLp i * σ⌋ : ℤ) : ZMod (m + 1))) ?_
    intro x y hadj hc
    change dist x y = 1 at hadj
    have hdvd : ∀ i : Fin n, ((m : ℤ) + 1) ∣ (⌊y.ofLp i * σ⌋ - ⌊x.ofLp i * σ⌋) := by
      intro i
      have h1 : ((⌊x.ofLp i * σ⌋ : ℤ) : ZMod (m + 1)) = ((⌊y.ofLp i * σ⌋ : ℤ) : ZMod (m + 1)) :=
        congrFun hc i
      have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
      exact_mod_cast h2
    by_cases hall : ∀ i : Fin n, ⌊y.ofLp i * σ⌋ - ⌊x.ofLp i * σ⌋ = 0
    · have hlt : ∀ i : Fin n, dist (x.ofLp i) (y.ofLp i) ^ 2 < 1 / (n : ℝ) := by
        intro i
        have he : ⌊y.ofLp i * σ⌋ = ⌊x.ofLp i * σ⌋ := by have := hall i; omega
        have h1 := Int.floor_le (x.ofLp i * σ)
        have h2 := Int.lt_floor_add_one (x.ofLp i * σ)
        have h3 := Int.floor_le (y.ofLp i * σ)
        have h4 := Int.lt_floor_add_one (y.ofLp i * σ)
        rw [he] at h3 h4
        have habs : |x.ofLp i * σ - y.ofLp i * σ| < 1 := by
          rw [abs_lt]; constructor <;> linarith
        have hsq : (x.ofLp i * σ - y.ofLp i * σ) ^ 2 < 1 := by
          nlinarith [abs_nonneg (x.ofLp i * σ - y.ofLp i * σ),
            sq_abs (x.ofLp i * σ - y.ofLp i * σ)]
        have hd : dist (x.ofLp i) (y.ofLp i) ^ 2 = (x.ofLp i - y.ofLp i) ^ 2 := by
          rw [Real.dist_eq, sq_abs]
        rw [hd, lt_div_iff₀ hnpos, ← hσsq]
        nlinarith [hsq]
      have hsum : ∑ i : Fin n, dist (x.ofLp i) (y.ofLp i) ^ 2 < 1 := by
        have h := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin n))
          (fun i (_ : i ∈ Finset.univ) => hlt i)
        simpa [Finset.sum_const, nsmul_eq_mul, mul_one_div,
          mul_inv_cancel₀ (ne_of_gt hnpos)] using h
      have hdlt : dist x y < 1 := by
        rw [EuclideanSpace.dist_eq, Real.sqrt_lt' one_pos]
        simpa using hsum
      linarith
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hd : ((m : ℤ) + 1) ≤ |⌊y.ofLp i * σ⌋ - ⌊x.ofLp i * σ⌋| :=
        Int.le_of_dvd (abs_pos.mpr hi) ((dvd_abs _ _).mpr (hdvd i))
      have hdR : ((m : ℝ) + 1) ≤ |((⌊y.ofLp i * σ⌋ : ℤ) : ℝ) - ((⌊x.ofLp i * σ⌋ : ℤ) : ℝ)| := by
        exact_mod_cast hd
      have hfac : |y.ofLp i * σ - x.ofLp i * σ| = |y.ofLp i - x.ofLp i| * σ := by
        rw [← sub_mul, abs_mul, abs_of_pos hσpos]
      have h5 := erdos704_floor_abs_lt (y.ofLp i * σ) (x.ofLp i * σ)
      rw [hfac] at h5
      have hgt : 1 < |y.ofLp i - x.ofLp i| := by nlinarith [hσpos, hm, hdR, h5]
      have hle := erdos704_coord_le_dist n x y i
      rw [abs_sub_comm] at hle
      linarith
  have hcard : Fintype.card (Fin n → ZMod (m + 1)) = (m + 1) ^ n := by simp
  exact hcard ▸ C.colorable

/-- **Erdős #704, the trivial colouring**: `G_n` has a proper colouring with `k` colours for some
`k ≤ (2 + √n)^n`. -/
theorem erdos_704_trivial_colouring (n : ℕ) :
    ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ (2 + Real.sqrt n) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have C : (unitDistanceGraph 0).Coloring (Fin 1) :=
      SimpleGraph.Coloring.mk (fun _ => 0) (fun {x y} hadj => by
        change dist x y = 1 at hadj
        rw [Subsingleton.elim x y] at hadj
        simp at hadj)
    exact ⟨1, by simpa using C.colorable, by norm_num⟩
  · refine ⟨(⌈Real.sqrt n⌉₊ + 1) ^ n,
      erdos704_colorable n hn ⌈Real.sqrt n⌉₊ (Nat.le_ceil _), ?_⟩
    have h1 : ((⌈Real.sqrt n⌉₊ : ℝ) + 1) ≤ 2 + Real.sqrt n := by
      have := Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))
      linarith
    have h2 : (0:ℝ) ≤ (⌈Real.sqrt n⌉₊ : ℝ) + 1 := by positivity
    calc (((⌈Real.sqrt n⌉₊ + 1) ^ n : ℕ) : ℝ)
        = ((⌈Real.sqrt n⌉₊ : ℝ) + 1) ^ n := by push_cast; ring
      _ ≤ (2 + Real.sqrt n) ^ n := pow_le_pow_left₀ h2 h1 n

/-- The same bound for the chromatic number: `χ(G_n) ≤ ⌊(2 + √n)^n⌋`. -/
theorem erdos_704_chromaticNumber_le (n : ℕ) :
    (unitDistanceGraph n).chromaticNumber ≤ (⌊(2 + Real.sqrt n) ^ n⌋₊ : ℕ∞) := by
  obtain ⟨k, hk, hle⟩ := erdos_704_trivial_colouring n
  exact hk.chromaticNumber_le.trans (by exact_mod_cast Nat.le_floor hle)
