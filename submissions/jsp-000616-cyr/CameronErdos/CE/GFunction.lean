import Mathlib

/-!
# The Cameron–Erdős counting function `g(k)` (Green's note, Proposition 2)

For `k ≥ 1` and `S ⊆ {0, …, 2k-1}` put `w_k(S) = 2^{-|(S+S) ∩ [0,2k-1]|}` and

* `g(k) = 2^{-k} Σ_{S ⊆ [0,2k-1]} w_k(S)`,
* `h(k) = 2^{-k} Σ_{S ⊆ [0,2k-1], 0 ∈ S} w_k(S)`,
* `h_{ij}(k)` the same sum restricted by `(2k ∈ S+S ↔ i)` and `(2k+1 ∈ S+S ↔ j)`.

The file proves the four steps of Green's note:

* `gCE_split` : `g(k) = g(k-1) + h(k)` for `k ≥ 2` (and `gCE_eq_sum`);
* `hCE_recurrence` / `hCE_recurrence'` : the weighted four-term estimate;
* `hCE00_le` : `h₀₀(k) ≤ 2^{-k} τ(2k-2)` together with `tauCE_rec`, `tauCE_le`;
* `gCE_bounded` : `∃ G, ∀ k ≥ 1, g(k) ≤ G`.
-/

namespace CameronErdos

open Finset
open scoped Pointwise

/-! ## Definitions -/

/-- The weight `w_k(S) = 2^{-|(S+S) ∩ [0, 2k-1]|}`. -/
noncomputable def wCE (k : ℕ) (S : Finset ℕ) : ℝ :=
  (1/2 : ℝ) ^ ((S + S) ∩ Finset.range (2 * k)).card

/-- `g(k) = 2^{-k} Σ_{S ⊆ [0,2k-1]} w_k(S)`. -/
noncomputable def gCE (k : ℕ) : ℝ :=
  (1/2 : ℝ) ^ k * ∑ S ∈ (Finset.range (2 * k)).powerset, wCE k S

/-- `h(k) = 2^{-k} Σ_{S ⊆ [0,2k-1], 0 ∈ S} w_k(S)`. -/
noncomputable def hCE (k : ℕ) : ℝ :=
  (1/2 : ℝ) ^ k * ∑ S ∈ (Finset.range (2 * k)).powerset.filter (fun S => 0 ∈ S), wCE k S

/-- `h_{ij}(k)`: the sum defining `h(k)` restricted to the sets `S` with
`(2k ∈ S + S ↔ i)` and `(2k+1 ∈ S + S ↔ j)`. -/
noncomputable def hCEij (i j : Bool) (k : ℕ) : ℝ :=
  (1/2 : ℝ) ^ k * ∑ S ∈ (Finset.range (2 * k)).powerset.filter
    (fun S => 0 ∈ S ∧ ((2 * k ∈ S + S) ↔ i = true) ∧ ((2 * k + 1 ∈ S + S) ↔ j = true)), wCE k S

lemma wCE_nonneg (k : ℕ) (S : Finset ℕ) : 0 ≤ wCE k S := by
  unfold wCE; positivity

lemma wCE_le_one (k : ℕ) (S : Finset ℕ) : wCE k S ≤ 1 := by
  unfold wCE
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma gCE_nonneg (k : ℕ) : 0 ≤ gCE k := by
  unfold gCE
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun S _ => wCE_nonneg k S)

lemma hCE_nonneg (k : ℕ) : 0 ≤ hCE k := by
  unfold hCE
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun S _ => wCE_nonneg k S)

lemma hCEij_nonneg (i j : Bool) (k : ℕ) : 0 ≤ hCEij i j k := by
  unfold hCEij
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun S _ => wCE_nonneg k S)

/-- Crude bound: `h(k) ≤ 2^k`.  (Every weight is at most `1` and there are `2^{2k}` sets.) -/
lemma hCE_le_pow (k : ℕ) : hCE k ≤ 2 ^ k := by
  unfold hCE
  have h1 : ∑ S ∈ (Finset.range (2 * k)).powerset.filter (fun S => 0 ∈ S), wCE k S
      ≤ ∑ S ∈ (Finset.range (2 * k)).powerset.filter (fun S => 0 ∈ S), (1 : ℝ) :=
    Finset.sum_le_sum fun S _ => wCE_le_one k S
  have h2 : ∑ S ∈ (Finset.range (2 * k)).powerset.filter (fun S => 0 ∈ S), (1 : ℝ)
      ≤ ∑ S ∈ (Finset.range (2 * k)).powerset, (1 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; norm_num)
  have h3 : ∑ S ∈ (Finset.range (2 * k)).powerset, (1 : ℝ) = (2 : ℝ) ^ (2 * k) := by
    rw [Finset.sum_const, Finset.card_powerset, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  have h4 : (1/2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) = 2 ^ k := by
    rw [pow_mul, ← mul_pow]; norm_num
  calc (1/2 : ℝ) ^ k * ∑ S ∈ (Finset.range (2 * k)).powerset.filter (fun S => 0 ∈ S), wCE k S
      ≤ (1/2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) := by
        apply mul_le_mul_of_nonneg_left (by linarith [h1, h2, h3.le, h3.ge]) (by positivity)
    _ = 2 ^ k := h4

/-- Crude bound: `g(k) ≤ 2^k`. -/
lemma gCE_le_pow (k : ℕ) : gCE k ≤ 2 ^ k := by
  unfold gCE
  have h1 : ∑ S ∈ (Finset.range (2 * k)).powerset, wCE k S
      ≤ ∑ S ∈ (Finset.range (2 * k)).powerset, (1 : ℝ) :=
    Finset.sum_le_sum fun S _ => wCE_le_one k S
  have h3 : ∑ S ∈ (Finset.range (2 * k)).powerset, (1 : ℝ) = (2 : ℝ) ^ (2 * k) := by
    rw [Finset.sum_const, Finset.card_powerset, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  have h4 : (1/2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) = 2 ^ k := by
    rw [pow_mul, ← mul_pow]; norm_num
  calc (1/2 : ℝ) ^ k * ∑ S ∈ (Finset.range (2 * k)).powerset, wCE k S
      ≤ (1/2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) := by
        apply mul_le_mul_of_nonneg_left (by linarith [h1, h3.le, h3.ge]) (by positivity)
    _ = 2 ^ k := h4

/-! ## The path generating function `τ` -/

/-- `U` contains no two consecutive integers. -/
def NoAdj (U : Finset ℕ) : Prop := ∀ x ∈ U, x + 1 ∉ U

instance : DecidablePred NoAdj := fun U => by unfold NoAdj; infer_instance

/-- Independent sets of the path on the vertices `0, 1, …, n-1`. -/
def indSets (n : ℕ) : Finset (Finset ℕ) := (Finset.range n).powerset.filter NoAdj

/-- `τ(n) = Σ_{U independent in the n-vertex path} 2^{-|U|}`. -/
noncomputable def tauCE (n : ℕ) : ℝ := ∑ U ∈ indSets n, (1/2 : ℝ) ^ U.card

lemma mem_indSets {n : ℕ} {U : Finset ℕ} : U ∈ indSets n ↔ U ⊆ Finset.range n ∧ NoAdj U := by
  simp [indSets, Finset.mem_filter, Finset.mem_powerset]

lemma tauCE_nonneg (n : ℕ) : 0 ≤ tauCE n :=
  Finset.sum_nonneg fun U _ => by positivity

@[simp] lemma tauCE_zero : tauCE 0 = 1 := by
  rw [tauCE, show indSets 0 = {∅} from by decide]
  simp

@[simp] lemma tauCE_one : tauCE 1 = 3/2 := by
  rw [tauCE, show indSets 1 = {∅, {0}} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- `τ(n+2) = τ(n+1) + τ(n)/2`. -/
lemma tauCE_rec (n : ℕ) : tauCE (n + 2) = tauCE (n + 1) + tauCE n / 2 := by
  classical
  rw [tauCE, ← Finset.sum_filter_add_sum_filter_not (indSets (n+2)) (fun U => (n+1) ∈ U),
    add_comm]
  congr 1
  · have h : (indSets (n+2)).filter (fun U => ¬ ((n+1) ∈ U)) = indSets (n+1) := by
      ext U
      simp only [Finset.mem_filter, mem_indSets]
      constructor
      · rintro ⟨⟨hsub, hadj⟩, hno⟩
        refine ⟨fun x hx => ?_, hadj⟩
        have := hsub hx
        simp only [Finset.mem_range] at this ⊢
        rcases Nat.lt_or_ge x (n+1) with h | h
        · exact h
        · exfalso; apply hno
          have hxe : x = n + 1 := by omega
          exact hxe ▸ hx
      · rintro ⟨hsub, hadj⟩
        have hr : Finset.range (n+1) ⊆ Finset.range (n+2) :=
          Finset.range_subset.2 (fun x hx => Finset.mem_range.2 (by omega))
        refine ⟨⟨hsub.trans hr, hadj⟩, fun hmem => ?_⟩
        have := hsub hmem
        simp only [Finset.mem_range] at this
        omega
    rw [h, tauCE]
  · rw [tauCE, Finset.sum_div]
    refine Finset.sum_nbij' (fun U => U.erase (n+1)) (fun V => insert (n+1) V) ?_ ?_ ?_ ?_ ?_
    · rintro U hU
      simp only [Finset.mem_filter, mem_indSets] at hU
      obtain ⟨⟨hsub, hadj⟩, hmem⟩ := hU
      refine mem_indSets.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have hx' := Finset.mem_of_mem_erase hx
        have hne := Finset.ne_of_mem_erase hx
        have hlt := Finset.mem_range.1 (hsub hx')
        simp only [Finset.mem_range]
        rcases Nat.lt_or_ge x n with h | h
        · exact h
        · exfalso
          have hxn : x = n := by omega
          subst hxn
          exact hadj x hx' hmem
      · exact fun hc => hadj x (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hc)
    · rintro V hV
      obtain ⟨hsub, hadj⟩ := mem_indSets.1 hV
      simp only [Finset.mem_filter, mem_indSets]
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · simp
        · have := Finset.mem_range.1 (hsub hx); simp only [Finset.mem_range]; omega
      · intro x hx hc
        rcases Finset.mem_insert.1 hx with rfl | hx
        · rcases Finset.mem_insert.1 hc with h | h
          · omega
          · have := Finset.mem_range.1 (hsub h); omega
        · rcases Finset.mem_insert.1 hc with h | h
          · have := Finset.mem_range.1 (hsub hx); omega
          · exact hadj x hx h
    · intro U hU
      simp only [Finset.mem_filter] at hU
      exact Finset.insert_erase hU.2
    · intro V hV
      refine Finset.erase_insert (fun hc => ?_)
      have := Finset.mem_range.1 ((mem_indSets.1 hV).1 hc); omega
    · intro U hU
      simp only [Finset.mem_filter] at hU
      have hcard : U.card = (U.erase (n+1)).card + 1 := by
        rw [Finset.card_erase_of_mem hU.2]
        have : 0 < U.card := Finset.card_pos.2 ⟨_, hU.2⟩
        omega
      rw [hcard, pow_succ]
      ring

/-- The closed form of `τ` from Green's note. -/
lemma tauCE_closed (n : ℕ) :
    tauCE n = ((3 + 2*Real.sqrt 3)/6) * ((1 + Real.sqrt 3)/2)^n
            + ((3 - 2*Real.sqrt 3)/6) * ((1 - Real.sqrt 3)/2)^n := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [tauCE_zero, pow_zero, pow_zero]; ring
    | 1 => rw [tauCE_one, pow_one, pow_one]; nlinarith [h3]
    | (m+2) =>
      have hα : ((1 + Real.sqrt 3)/2)^(m+2)
          = ((1 + Real.sqrt 3)/2)^(m+1) + ((1 + Real.sqrt 3)/2)^m / 2 := by
        have e : ((1 + Real.sqrt 3)/2)^(m+2)
            = ((1 + Real.sqrt 3)/2)^m * (((1 + Real.sqrt 3)/2)^2) := by ring
        have e2 : ((1 + Real.sqrt 3)/2)^2 = ((1 + Real.sqrt 3)/2) + 1/2 := by nlinarith [h3]
        rw [e, e2]; ring
      have hβ : ((1 - Real.sqrt 3)/2)^(m+2)
          = ((1 - Real.sqrt 3)/2)^(m+1) + ((1 - Real.sqrt 3)/2)^m / 2 := by
        have e : ((1 - Real.sqrt 3)/2)^(m+2)
            = ((1 - Real.sqrt 3)/2)^m * (((1 - Real.sqrt 3)/2)^2) := by ring
        have e2 : ((1 - Real.sqrt 3)/2)^2 = ((1 - Real.sqrt 3)/2) + 1/2 := by nlinarith [h3]
        rw [e, e2]; ring
      rw [tauCE_rec, ih (m+1) (by omega), ih m (by omega), hα, hβ]
      ring

/-- `τ(n) ≤ 2 ((1+√3)/2)^n`, the sharp exponential bound of Green's note. -/
lemma tauCE_le (n : ℕ) : tauCE n ≤ 2 * ((1 + Real.sqrt 3) / 2) ^ n := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs1 : (1:ℝ) ≤ Real.sqrt 3 := by nlinarith
  set c : ℝ := (1 + Real.sqrt 3) / 2 with hc
  have hc0 : (0:ℝ) < c := by rw [hc]; linarith
  have hkey : 2 * c ^ 2 = 2 * c + 1 := by rw [hc]; nlinarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => rw [tauCE_one, pow_one, hc]; linarith
    | (m+2) =>
      have h1 := ih (m+1) (by omega)
      have h2 := ih m (by omega)
      have hcm : (0:ℝ) ≤ c ^ m := by positivity
      rw [tauCE_rec]
      calc tauCE (m+1) + tauCE m / 2 ≤ 2 * c ^ (m+1) + (2 * c ^ m) / 2 := by linarith
        _ = c ^ m * (2 * c + 1) := by ring
        _ = c ^ m * (2 * c ^ 2) := by rw [hkey]
        _ = 2 * c ^ (m+2) := by ring

/-- The rational form of the bound: `τ(n) ≤ 2·(1.37)^n`. -/
lemma tauCE_le' (n : ℕ) : tauCE n ≤ 2 * (137/100 : ℝ) ^ n := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hle : (1 + Real.sqrt 3) / 2 ≤ (137/100 : ℝ) := by nlinarith
  have hpos : (0:ℝ) ≤ (1 + Real.sqrt 3) / 2 := by linarith
  refine (tauCE_le n).trans ?_
  have := pow_le_pow_left₀ hpos hle n
  linarith

/-! ## Step 1: `g(k) = g(k-1) + h(k)` -/

lemma image_succ_add (T : Finset ℕ) :
    (T.image (· + 1)) + (T.image (· + 1)) = (T + T).image (· + 2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.1 hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
    exact Finset.mem_image.2 ⟨a + b, Finset.add_mem_add ha hb, by omega⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hy
    have h1 : a + 1 ∈ T.image (· + 1) := Finset.mem_image.2 ⟨a, ha, rfl⟩
    have h2 : b + 1 ∈ T.image (· + 1) := Finset.mem_image.2 ⟨b, hb, rfl⟩
    have h3 := Finset.add_mem_add h1 h2
    have e : a + b + 2 = (a + 1) + (b + 1) := by omega
    show a + b + 2 ∈ _
    rw [e]; exact h3

/-- Shifting a subset of `[0,2k-1]` by one does not change its weight. -/
lemma wCE_shift (k : ℕ) (T : Finset ℕ) : wCE (k + 1) (T.image (· + 1)) = wCE k T := by
  unfold wCE
  congr 1
  have h : ((T.image (· + 1)) + (T.image (· + 1))) ∩ Finset.range (2 * (k+1))
      = ((T + T) ∩ Finset.range (2 * k)).image (· + 2) := by
    rw [image_succ_add]
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hlt⟩
      exact ⟨y, ⟨hy, by omega⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hylt⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by omega⟩
  rw [h, Finset.card_image_of_injective _ (add_left_injective 2)]

/-- Adjoining the top point `2k+1` to a shifted set does not change its weight either:
the extra sums all lie beyond `2k+1`. -/
lemma wCE_shift_insert (k : ℕ) (T : Finset ℕ) :
    wCE (k + 1) (insert (2 * k + 1) (T.image (· + 1))) = wCE k T := by
  rw [← wCE_shift k T]
  unfold wCE
  congr 2
  set T' := T.image (· + 1) with hT'
  have hT'pos : ∀ x ∈ T', 1 ≤ x := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx
    omega
  ext x
  simp only [Finset.mem_inter, Finset.mem_range]
  constructor
  · rintro ⟨hx, hlt⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exfalso
      rcases Finset.mem_insert.1 hb with rfl | hb'
      · omega
      · have hb1 := hT'pos b hb'; omega
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · exfalso; have ha1 := hT'pos a ha'; omega
      · exact ⟨Finset.add_mem_add ha' hb', hlt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨Finset.add_subset_add (Finset.subset_insert _ _) (Finset.subset_insert _ _) hx, hlt⟩

lemma gCE_succ (k : ℕ) : gCE (k + 1) = gCE k + hCE (k + 1) := by
  classical
  have hr : Finset.range (2 * (k+1)) = insert 0 (Finset.Ico 1 (2*k+2)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_insert]; omega
  have h0 : (0:ℕ) ∉ Finset.Ico 1 (2*k+2) := by simp
  have hg : ∑ S ∈ (Finset.range (2*(k+1))).powerset, wCE (k+1) S
      = (∑ T ∈ (Finset.Ico 1 (2*k+2)).powerset, wCE (k+1) T)
        + ∑ T ∈ (Finset.Ico 1 (2*k+2)).powerset, wCE (k+1) (insert 0 T) := by
    rw [hr, Finset.sum_powerset_insert h0]
  have hh : ∑ S ∈ (Finset.range (2*(k+1))).powerset.filter (fun S => 0 ∈ S), wCE (k+1) S
      = ∑ T ∈ (Finset.Ico 1 (2*k+2)).powerset, wCE (k+1) (insert 0 T) := by
    rw [Finset.sum_filter, hr, Finset.sum_powerset_insert h0]
    have e1 : ∑ T ∈ (Finset.Ico 1 (2*k+2)).powerset,
        (if 0 ∈ T then wCE (k+1) T else 0) = 0 := by
      refine Finset.sum_eq_zero fun T hT => ?_
      have hnot : (0:ℕ) ∉ T := fun hc => h0 (Finset.mem_powerset.1 hT hc)
      simp [hnot]
    rw [e1, zero_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp
  have hsplit : ∑ T ∈ (Finset.Ico 1 (2*k+2)).powerset, wCE (k+1) T
      = 2 * ∑ U ∈ (Finset.range (2*k)).powerset, wCE k U := by
    have hi : Finset.Ico 1 (2*k+2) = insert (2*k+1) (Finset.Ico 1 (2*k+1)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hni : (2*k+1) ∉ Finset.Ico 1 (2*k+1) := by simp
    have him : Finset.Ico 1 (2*k+1) = (Finset.range (2*k)).image (· + 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega
    have hinj : Set.InjOn (fun (U : Finset ℕ) => U.image (· + 1))
        ((Finset.range (2*k)).powerset : Set (Finset ℕ)) :=
      Set.injOn_of_injective (Finset.image_injective (add_left_injective 1))
    rw [hi, Finset.sum_powerset_insert hni, him, Finset.powerset_image,
      Finset.sum_image hinj, Finset.sum_image hinj]
    simp only [wCE_shift, wCE_shift_insert]
    ring
  rw [gCE, gCE, hCE, hg, hh, hsplit]
  ring

/-- **Step 1 (Green's note).** For `k ≥ 2`, `g(k) = g(k-1) + h(k)`. -/
theorem gCE_split {k : ℕ} (hk : 2 ≤ k) : gCE k = gCE (k - 1) + hCE k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using gCE_succ m

/-- `g(k) = g(1) + Σ_{j=2}^{k} h(j)`. -/
theorem gCE_eq_sum {k : ℕ} (hk : 1 ≤ k) : gCE k = gCE 1 + ∑ j ∈ Finset.Icc 2 k, hCE j := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · simp [← h]
    · have hn : 1 ≤ n := by omega
      rw [gCE_succ n, ih hn, Finset.sum_Icc_succ_top (by omega)]
      ring

/-! ## Step 2: the recurrence for `h` -/

/-- The coefficient `9/8, 3/4, 3/4, 1/2` attached to `S` according to whether `2k` and `2k+1`
already lie in `S + S`. -/
noncomputable def coefCE (k : ℕ) (S : Finset ℕ) : ℝ :=
  if 2*k ∈ S + S then (if 2*k+1 ∈ S + S then 1/2 else 3/4)
  else (if 2*k+1 ∈ S + S then 3/4 else 9/8)

/-- The summand of `h_{ij}(k)`. -/
noncomputable def fCE (k : ℕ) (i j : Bool) (S : Finset ℕ) : ℝ :=
  if (0 ∈ S ∧ ((2 * k ∈ S + S) ↔ i = true) ∧ ((2 * k + 1 ∈ S + S) ↔ j = true)) then wCE k S else 0

lemma hCE_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    hCE (k+1) = (1/2:ℝ)^(k+1) * ∑ S ∈ (Finset.range (2*k)).powerset,
      (if 0 ∈ S then wCE (k+1) S + wCE (k+1) (insert (2*k) S)
        + wCE (k+1) (insert (2*k+1) S) + wCE (k+1) (insert (2*k+1) (insert (2*k) S)) else 0) := by
  classical
  rw [hCE, Finset.sum_filter]
  congr 1
  have e1 : Finset.range (2*(k+1)) = insert (2*k+1) (Finset.range (2*k+1)) := by
    have h : 2*(k+1) = (2*k+1)+1 := by ring
    rw [h, Finset.range_add_one]
  have e2 : Finset.range (2*k+1) = insert (2*k) (Finset.range (2*k)) := Finset.range_add_one
  have hn1 : (2*k+1) ∉ Finset.range (2*k+1) := by simp
  have hn2 : (2*k) ∉ Finset.range (2*k) := by simp
  rw [e1, Finset.sum_powerset_insert hn1, e2, Finset.sum_powerset_insert hn2,
    Finset.sum_powerset_insert hn2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have ha : (0:ℕ) ≠ 2*k := by omega
  by_cases h : (0:ℕ) ∈ S <;> simp [h, Finset.mem_insert, ha]
  ring


lemma hCEij_eq (k : ℕ) (i j : Bool) :
    hCEij i j k = (1/2:ℝ)^k * ∑ S ∈ (Finset.range (2*k)).powerset, fCE k i j S := by
  rw [hCEij, Finset.sum_filter]; rfl

lemma hCEij_combo (k : ℕ) :
    9/8 * hCEij false false k + 3/4 * (hCEij false true k + hCEij true false k)
      + 1/2 * hCEij true true k
    = (1/2:ℝ)^k * ∑ S ∈ (Finset.range (2*k)).powerset,
        (if 0 ∈ S then coefCE k S * wCE k S else 0) := by
  classical
  have key : ∀ S : Finset ℕ, (if 0 ∈ S then coefCE k S * wCE k S else 0)
      = 9/8 * fCE k false false S + 3/4 * fCE k false true S + 3/4 * fCE k true false S
        + 1/2 * fCE k true true S := by
    intro S
    by_cases h0 : (0:ℕ) ∈ S <;> by_cases ha : 2*k ∈ S + S <;> by_cases hb : 2*k+1 ∈ S + S <;>
      simp [coefCE, fCE, h0, ha, hb]
  have hsum : ∑ S ∈ (Finset.range (2*k)).powerset, (if 0 ∈ S then coefCE k S * wCE k S else 0)
      = 9/8 * (∑ S ∈ (Finset.range (2*k)).powerset, fCE k false false S)
        + 3/4 * (∑ S ∈ (Finset.range (2*k)).powerset, fCE k false true S)
        + 3/4 * (∑ S ∈ (Finset.range (2*k)).powerset, fCE k true false S)
        + 1/2 * (∑ S ∈ (Finset.range (2*k)).powerset, fCE k true true S) := by
    rw [Finset.sum_congr rfl (fun S (_ : S ∈ (Finset.range (2*k)).powerset) => key S)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hCEij_eq, hCEij_eq, hCEij_eq, hCEij_eq, hsum]
  ring
lemma wCE_succ_le (k : ℕ) (S T A : Finset ℕ) (hST : S ⊆ T)
    (hA : ∀ x ∈ A, x = 2*k ∨ x = 2*k+1) (hA2 : ∀ x ∈ A, x ∈ T + T) :
    wCE (k+1) T ≤ (1/2:ℝ) ^ (((S + S) ∩ Finset.range (2*k)).card + A.card) := by
  classical
  set M := (S + S) ∩ Finset.range (2*k) with hM
  have hdisj : Disjoint M A := by
    rw [Finset.disjoint_left]
    intro x hx hxA
    have h1 : x ∈ Finset.range (2*k) := (Finset.mem_inter.1 hx).2
    rw [Finset.mem_range] at h1
    rcases hA x hxA with h | h <;> omega
  have hsub : M ∪ A ⊆ (T + T) ∩ Finset.range (2*(k+1)) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · have h1 := Finset.mem_inter.1 h
      refine Finset.mem_inter.2 ⟨Finset.add_subset_add hST hST h1.1, ?_⟩
      have := Finset.mem_range.1 h1.2
      exact Finset.mem_range.2 (by omega)
    · refine Finset.mem_inter.2 ⟨hA2 x h, Finset.mem_range.2 ?_⟩
      rcases hA x h with h' | h' <;> omega
  have hcard : M.card + A.card ≤ ((T + T) ∩ Finset.range (2*(k+1))).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard


lemma four_term_le (k : ℕ) (S : Finset ℕ) (h0 : (0:ℕ) ∈ S) :
    (1/2:ℝ) * (wCE (k+1) S + wCE (k+1) (insert (2*k) S)
      + wCE (k+1) (insert (2*k+1) S) + wCE (k+1) (insert (2*k+1) (insert (2*k) S)))
    ≤ coefCE k S * wCE k S := by
  classical
  set M := (S + S) ∩ Finset.range (2*k) with hM
  set x : ℝ := (1/2:ℝ) ^ M.card with hx
  have hwS : wCE k S = x := rfl
  have hx0 : 0 < x := by rw [hx]; positivity
  have e1 : (1/2:ℝ)^(M.card + 1) = x / 2 := by rw [hx, pow_succ]; ring
  have e2 : (1/2:ℝ)^(M.card + 2) = x / 4 := by rw [hx, pow_succ, pow_succ]; ring
  have e0 : (1/2:ℝ)^(M.card + 0) = x := by rw [hx, Nat.add_zero]
  -- the four sets
  set T1 := insert (2*k) S with hT1
  set T2 := insert (2*k+1) S with hT2
  set T3 := insert (2*k+1) (insert (2*k) S) with hT3
  have s1 : S ⊆ T1 := Finset.subset_insert _ _
  have s2 : S ⊆ T2 := Finset.subset_insert _ _
  have s3 : S ⊆ T3 := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have m1 : 2*k ∈ T1 + T1 :=
    Finset.mem_add.2 ⟨0, s1 h0, 2*k, Finset.mem_insert_self _ _, by omega⟩
  have m2 : 2*k+1 ∈ T2 + T2 :=
    Finset.mem_add.2 ⟨0, s2 h0, 2*k+1, Finset.mem_insert_self _ _, by omega⟩
  have m3a : 2*k ∈ T3 + T3 :=
    Finset.mem_add.2 ⟨0, s3 h0, 2*k,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by omega⟩
  have m3b : 2*k+1 ∈ T3 + T3 :=
    Finset.mem_add.2 ⟨0, s3 h0, 2*k+1, Finset.mem_insert_self _ _, by omega⟩
  have hAempty : ∀ x ∈ (∅ : Finset ℕ), x = 2*k ∨ x = 2*k+1 := by simp
  have hAempty2 : ∀ (T : Finset ℕ), ∀ x ∈ (∅ : Finset ℕ), x ∈ T + T := by simp
  have hA1 : ∀ x ∈ ({2*k} : Finset ℕ), x = 2*k ∨ x = 2*k+1 := by simp
  have hA2' : ∀ x ∈ ({2*k+1} : Finset ℕ), x = 2*k ∨ x = 2*k+1 := by simp
  have hA3 : ∀ x ∈ ({2*k, 2*k+1} : Finset ℕ), x = 2*k ∨ x = 2*k+1 := by
    intro x hx; rcases Finset.mem_insert.1 hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.1 h)
  have c1 : ({2*k} : Finset ℕ).card = 1 := Finset.card_singleton _
  have c2 : ({2*k+1} : Finset ℕ).card = 1 := Finset.card_singleton _
  have c3 : ({2*k, 2*k+1} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
  by_cases ha : 2*k ∈ S + S <;> by_cases hb : 2*k+1 ∈ S + S
  · -- a = 1, b = 1
    have b0 : wCE (k+1) S ≤ x / 4 := by
      have h := wCE_succ_le k S S {2*k, 2*k+1} (subset_refl _) hA3
        (by intro y hy; rcases hA3 y hy with h | h <;> subst h <;> assumption)
      rw [c3, e2] at h; exact h
    have b1 : wCE (k+1) T1 ≤ x / 4 := by
      have h := wCE_succ_le k S T1 {2*k, 2*k+1} s1 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m1
        · subst h; exact Finset.add_subset_add s1 s1 hb)
      rw [c3, e2] at h; exact h
    have b2 : wCE (k+1) T2 ≤ x / 4 := by
      have h := wCE_succ_le k S T2 {2*k, 2*k+1} s2 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact Finset.add_subset_add s2 s2 ha
        · subst h; exact m2)
      rw [c3, e2] at h; exact h
    have b3 : wCE (k+1) T3 ≤ x / 4 := by
      have h := wCE_succ_le k S T3 {2*k, 2*k+1} s3 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m3a
        · subst h; exact m3b)
      rw [c3, e2] at h; exact h
    rw [hwS, coefCE]
    simp only [ha, hb, ite_true]
    linarith
  · -- a = 1, b = 0
    have b0 : wCE (k+1) S ≤ x / 2 := by
      have h := wCE_succ_le k S S {2*k} (subset_refl _) hA1
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact ha)
      rw [c1, e1] at h; exact h
    have b1 : wCE (k+1) T1 ≤ x / 2 := by
      have h := wCE_succ_le k S T1 {2*k} s1 hA1
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact m1)
      rw [c1, e1] at h; exact h
    have b2 : wCE (k+1) T2 ≤ x / 4 := by
      have h := wCE_succ_le k S T2 {2*k, 2*k+1} s2 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact Finset.add_subset_add s2 s2 ha
        · subst h; exact m2)
      rw [c3, e2] at h; exact h
    have b3 : wCE (k+1) T3 ≤ x / 4 := by
      have h := wCE_succ_le k S T3 {2*k, 2*k+1} s3 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m3a
        · subst h; exact m3b)
      rw [c3, e2] at h; exact h
    rw [hwS, coefCE]
    simp only [ha, hb, ite_true, ite_false]
    linarith
  · -- a = 0, b = 1
    have b0 : wCE (k+1) S ≤ x / 2 := by
      have h := wCE_succ_le k S S {2*k+1} (subset_refl _) hA2'
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact hb)
      rw [c2, e1] at h; exact h
    have b1 : wCE (k+1) T1 ≤ x / 4 := by
      have h := wCE_succ_le k S T1 {2*k, 2*k+1} s1 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m1
        · subst h; exact Finset.add_subset_add s1 s1 hb)
      rw [c3, e2] at h; exact h
    have b2 : wCE (k+1) T2 ≤ x / 2 := by
      have h := wCE_succ_le k S T2 {2*k+1} s2 hA2'
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact m2)
      rw [c2, e1] at h; exact h
    have b3 : wCE (k+1) T3 ≤ x / 4 := by
      have h := wCE_succ_le k S T3 {2*k, 2*k+1} s3 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m3a
        · subst h; exact m3b)
      rw [c3, e2] at h; exact h
    rw [hwS, coefCE]
    simp only [ha, hb, ite_true, ite_false]
    linarith
  · -- a = 0, b = 0
    have b0 : wCE (k+1) S ≤ x := by
      have h := wCE_succ_le k S S ∅ (subset_refl _) hAempty (hAempty2 S)
      rw [Finset.card_empty, e0] at h; exact h
    have b1 : wCE (k+1) T1 ≤ x / 2 := by
      have h := wCE_succ_le k S T1 {2*k} s1 hA1
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact m1)
      rw [c1, e1] at h; exact h
    have b2 : wCE (k+1) T2 ≤ x / 2 := by
      have h := wCE_succ_le k S T2 {2*k+1} s2 hA2'
        (by intro y hy; rw [Finset.mem_singleton.1 hy]; exact m2)
      rw [c2, e1] at h; exact h
    have b3 : wCE (k+1) T3 ≤ x / 4 := by
      have h := wCE_succ_le k S T3 {2*k, 2*k+1} s3 hA3 (by
        intro y hy; rcases hA3 y hy with h | h
        · subst h; exact m3a
        · subst h; exact m3b)
      rw [c3, e2] at h; exact h
    rw [hwS, coefCE]
    simp only [ha, hb, ite_false]
    linarith

lemma hCE_eq_sum (k : ℕ) :
    hCE k = (1/2:ℝ)^k * ∑ S ∈ (Finset.range (2*k)).powerset,
      (if 0 ∈ S then wCE k S else 0) := by
  rw [hCE, Finset.sum_filter]

/-- `h(k) = h₀₀(k) + h₀₁(k) + h₁₀(k) + h₁₁(k)`. -/
lemma hCE_split4 (k : ℕ) :
    hCE k = hCEij false false k + hCEij false true k + hCEij true false k
      + hCEij true true k := by
  classical
  have key : ∀ S : Finset ℕ, (if 0 ∈ S then wCE k S else 0)
      = fCE k false false S + fCE k false true S + fCE k true false S + fCE k true true S := by
    intro S
    by_cases h0 : (0:ℕ) ∈ S <;> by_cases ha : 2*k ∈ S + S <;> by_cases hb : 2*k+1 ∈ S + S <;>
      simp [fCE, h0, ha, hb]
  rw [hCE_eq_sum, Finset.sum_congr rfl (fun S (_ : S ∈ (Finset.range (2*k)).powerset) => key S),
    hCEij_eq, hCEij_eq, hCEij_eq, hCEij_eq, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  ring

/-- **Step 2 (Green's note).**
`h(k+1) ≤ (9/8) h₀₀(k) + (3/4)(h₀₁(k) + h₁₀(k)) + (1/2) h₁₁(k)`. -/
theorem hCE_recurrence {k : ℕ} (hk : 1 ≤ k) :
    hCE (k+1) ≤ 9/8 * hCEij false false k + 3/4 * (hCEij false true k + hCEij true false k)
      + 1/2 * hCEij true true k := by
  classical
  rw [hCE_succ_eq k hk, hCEij_combo k]
  have hterm : ∀ S ∈ (Finset.range (2*k)).powerset,
      (1/2:ℝ) * (if 0 ∈ S then wCE (k+1) S + wCE (k+1) (insert (2*k) S)
        + wCE (k+1) (insert (2*k+1) S) + wCE (k+1) (insert (2*k+1) (insert (2*k) S)) else 0)
      ≤ (if 0 ∈ S then coefCE k S * wCE k S else 0) := by
    intro S _
    by_cases h : (0:ℕ) ∈ S
    · simp only [h, ite_true]
      exact four_term_le k S h
    · simp only [h, ite_false]
      norm_num
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  rw [pow_succ, mul_assoc]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The consequence used below: `h(k+1) ≤ (3/4) h(k) + (3/8) h₀₀(k)`. -/
theorem hCE_recurrence' {k : ℕ} (hk : 1 ≤ k) :
    hCE (k+1) ≤ 3/4 * hCE k + 3/8 * hCEij false false k := by
  have h := hCE_recurrence hk
  rw [hCE_split4 k]
  have h11 := hCEij_nonneg true true k
  linarith

/-! ## Step 3: `h₀₀(k) ≤ 2^{-k} τ(2k-2)` -/

lemma hCE00_eq (k : ℕ) : hCEij false false k
    = (1/2:ℝ)^k * ∑ S ∈ (Finset.range (2*k)).powerset.filter
        (fun S => 0 ∈ S ∧ 2*k ∉ S + S ∧ 2*k+1 ∉ S + S), wCE k S := by
  rw [hCEij]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr fun S _ => ?_
  simp

/-- Position of `a` on the path `1, 2k-1, 2, 2k-2, …, k-1, k+1`. -/
def pathPos (k a : ℕ) : ℕ := if a < k then 2*a - 2 else 4*k - 1 - 2*a

lemma pathPos_injOn (k : ℕ) : ∀ a ∈ Finset.Ico 1 (2*k), ∀ b ∈ Finset.Ico 1 (2*k),
    pathPos k a = pathPos k b → a = b := by
  intro a ha b hb hab
  simp only [Finset.mem_Ico] at ha hb
  unfold pathPos at hab
  split_ifs at hab <;> omega

lemma pathPos_lt {k a : ℕ} (h1 : 1 ≤ a) (h2 : a < 2*k) (h3 : a ≠ k) : pathPos k a < 2*k - 2 := by
  unfold pathPos
  split_ifs <;> omega
lemma key_facts {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range (2*k))
    (ha : 2*k ∉ S + S) : ∀ a ∈ S.erase 0, 1 ≤ a ∧ a < 2*k ∧ a ≠ k := by
  intro a hae
  have haS := Finset.mem_of_mem_erase hae
  have hane : a ≠ 0 := Finset.ne_of_mem_erase hae
  have hlt := Finset.mem_range.1 (hS haS)
  refine ⟨by omega, hlt, ?_⟩
  rintro rfl
  exact ha (by
    have := Finset.add_mem_add haS haS
    have e : a + a = 2 * a := by omega
    rwa [e] at this)

lemma image_mem_indSets {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range (2*k)) (h0 : (0:ℕ) ∈ S)
    (ha : 2*k ∉ S + S) (hb : 2*k+1 ∉ S + S) :
    (S.erase 0).image (pathPos k) ∈ indSets (2*k-2) := by
  have _ := h0
  have facts := key_facts hS ha
  refine mem_indSets.2 ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨a, hae, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨f1, f2, f3⟩ := facts a hae
    exact Finset.mem_range.2 (pathPos_lt f1 f2 f3)
  · intro u hu hu1
    obtain ⟨a, hae, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hbe, hbeq⟩ := Finset.mem_image.1 hu1
    obtain ⟨a1, a2, a3⟩ := facts a hae
    obtain ⟨b1, b2, b3⟩ := facts b hbe
    have haS := Finset.mem_of_mem_erase hae
    have hbS := Finset.mem_of_mem_erase hbe
    unfold pathPos at hbeq
    split_ifs at hbeq with h1 h2 h2
    · omega
    · exact hb (by
        have e : a + b = 2*k+1 := by omega
        have := Finset.add_mem_add haS hbS
        rwa [e] at this)
    · exact ha (by
        have e : a + b = 2*k := by omega
        have := Finset.add_mem_add haS hbS
        rwa [e] at this)
    · omega
theorem hCE00_le (k : ℕ) :
    hCEij false false k ≤ (1/2:ℝ)^k * tauCE (2*k-2) := by
  classical
  rw [hCE00_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set A := (Finset.range (2*k)).powerset.filter
    (fun S => 0 ∈ S ∧ 2*k ∉ S + S ∧ 2*k+1 ∉ S + S) with hA
  have hmemA : ∀ S ∈ A, S ⊆ Finset.range (2*k) ∧ 0 ∈ S ∧ 2*k ∉ S+S ∧ 2*k+1 ∉ S+S := by
    intro S hS
    have h := Finset.mem_filter.1 hS
    exact ⟨Finset.mem_powerset.1 h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  set Φ : Finset ℕ → Finset ℕ := fun S => (S.erase 0).image (pathPos k) with hΦ
  have hmaps : ∀ S ∈ A, Φ S ∈ indSets (2*k-2) := by
    intro S hS
    obtain ⟨p, q, r, s⟩ := hmemA S hS
    exact image_mem_indSets p q r s
  have hIco : ∀ S ∈ A, ∀ a ∈ S.erase 0, a ∈ Finset.Ico 1 (2*k) := by
    intro S hS a hae
    obtain ⟨p, q, r, s⟩ := hmemA S hS
    obtain ⟨f1, f2, -⟩ := key_facts p r a hae
    exact Finset.mem_Ico.2 ⟨f1, f2⟩
  have hinj : Set.InjOn Φ (A : Set (Finset ℕ)) := by
    intro S hS S' hS' hEq
    have hSA : S ∈ A := Finset.mem_coe.1 hS
    have hSA' : S' ∈ A := Finset.mem_coe.1 hS'
    have h1 := hmemA S hSA
    have h1' := hmemA S' hSA'
    have herase : S.erase 0 = S'.erase 0 := by
      ext a
      constructor
      · intro hae
        have hm : pathPos k a ∈ Φ S := Finset.mem_image.2 ⟨a, hae, rfl⟩
        rw [hEq] at hm
        obtain ⟨b, hbe, hbeq⟩ := Finset.mem_image.1 hm
        exact (pathPos_injOn k b (hIco S' hSA' b hbe) a (hIco S hSA a hae) hbeq) ▸ hbe
      · intro hae
        have hm : pathPos k a ∈ Φ S' := Finset.mem_image.2 ⟨a, hae, rfl⟩
        rw [← hEq] at hm
        obtain ⟨b, hbe, hbeq⟩ := Finset.mem_image.1 hm
        exact (pathPos_injOn k b (hIco S hSA b hbe) a (hIco S' hSA' a hae) hbeq) ▸ hbe
    rw [← Finset.insert_erase h1.2.1, ← Finset.insert_erase h1'.2.1, herase]
  have hle : ∀ S ∈ A, wCE k S ≤ (1/2:ℝ)^(Φ S).card := by
    intro S hS
    obtain ⟨p, q, r, s⟩ := hmemA S hS
    have hsub : S ⊆ (S + S) ∩ Finset.range (2*k) := by
      intro a haS
      exact Finset.mem_inter.2 ⟨Finset.mem_add.2 ⟨0, q, a, haS, by omega⟩, p haS⟩
    have c1 : (Φ S).card ≤ S.card :=
      le_trans Finset.card_image_le (Finset.card_le_card (Finset.erase_subset _ _))
    have c2 : S.card ≤ ((S + S) ∩ Finset.range (2*k)).card := Finset.card_le_card hsub
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans c1 c2)
  calc ∑ S ∈ A, wCE k S ≤ ∑ S ∈ A, (1/2:ℝ)^(Φ S).card := Finset.sum_le_sum hle
    _ = ∑ U ∈ A.image Φ, (1/2:ℝ)^U.card :=
        (Finset.sum_image (f := fun U : Finset ℕ => (1/2:ℝ)^U.card) hinj).symm
    _ ≤ ∑ U ∈ indSets (2*k-2), (1/2:ℝ)^U.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro U hU
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hU
        exact hmaps S hS
    _ = tauCE (2*k-2) := rfl

/-! ## Step 4: `g` is bounded

With `c = 1.37` (an admissible substitute for `(1+√3)/2 ≈ 1.3660…`) and
`ρ = c²/2 = 0.93845 < 1` we get `h(k+1) ≤ (3/4) h(k) + (2/5) ρ^k`, hence `h(k) ≤ 3 ρ^k`
and `g(k) ≤ 50 - 50 ρ^k ≤ 50`. -/

lemma hCE00_bound {k : ℕ} (hk : 1 ≤ k) :
    3/8 * hCEij false false k ≤ (2/5 : ℝ) * (18769/20000 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 := hCE00_le (m+1)
  have h2 := tauCE_le' (2*(m+1)-2)
  have he : 2*(m+1)-2 = 2*m := by omega
  rw [he] at h1 h2
  have h3 : (137/100:ℝ)^(2*m) = (18769/10000:ℝ)^m := by
    rw [pow_mul]; norm_num
  rw [h3] at h2
  have hpos : (0:ℝ) < (1/2:ℝ)^(m+1) := by positivity
  have h4 : (1/2:ℝ)^(m+1) * tauCE (2*m) ≤ (1/2:ℝ)^(m+1) * (2 * (18769/10000:ℝ)^m) :=
    mul_le_mul_of_nonneg_left h2 hpos.le
  have key : (1/2:ℝ)^(m+1) * (2 * (18769/10000:ℝ)^m) = (18769/20000:ℝ)^m := by
    have e : ((1/2:ℝ)^m * (1/2)) * (2 * (18769/10000:ℝ)^m)
        = (1/2:ℝ)^m * (18769/10000:ℝ)^m := by ring
    rw [pow_succ, e, ← mul_pow]
    norm_num
  have hrm : (0:ℝ) ≤ (18769/20000:ℝ)^m := by positivity
  calc 3/8 * hCEij false false (m+1)
      ≤ 3/8 * ((1/2:ℝ)^(m+1) * tauCE (2*m)) := by linarith
    _ ≤ 3/8 * ((1/2:ℝ)^(m+1) * (2 * (18769/10000:ℝ)^m)) := by linarith
    _ = 3/8 * (18769/20000:ℝ)^m := by rw [key]
    _ ≤ 2/5 * (18769/20000:ℝ)^(m+1) := by rw [pow_succ]; nlinarith

lemma hCE_bound : ∀ {k : ℕ}, 1 ≤ k → hCE k ≤ 3 * (18769/20000:ℝ)^k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h := hCE_le_pow 1
      rw [pow_one] at h ⊢
      norm_num at h ⊢
      linarith
    · have h1 := ih hm
      have h2 := hCE_recurrence' hm
      have h3 := hCE00_bound hm
      have hrm : (0:ℝ) ≤ (18769/20000:ℝ)^m := by positivity
      rw [pow_succ]
      nlinarith

lemma gCE_bound : ∀ {k : ℕ}, 1 ≤ k → gCE k ≤ 50 - 50 * (18769/20000:ℝ)^k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h := gCE_le_pow 1
      rw [pow_one] at h ⊢
      norm_num at h ⊢
      linarith
    · have h1 := ih hm
      have h2 := gCE_succ m
      have h3 := hCE_bound (k := m+1) (by omega)
      have hrm : (0:ℝ) ≤ (18769/20000:ℝ)^m := by positivity
      rw [pow_succ] at h3 ⊢
      nlinarith

/-- **Step 4 (Green's note, Proposition 2).**  `g` is bounded: there is a `G` with
`g(k) ≤ G` for every `k ≥ 1`. -/
theorem gCE_bounded : ∃ G : ℝ, ∀ k : ℕ, 1 ≤ k → gCE k ≤ G := by
  refine ⟨50, fun k hk => ?_⟩
  have h := gCE_bound hk
  have hrm : (0:ℝ) ≤ (18769/20000:ℝ)^k := by positivity
  linarith


/-! ## Axiom audit -/

#print axioms wCE_nonneg
#print axioms wCE_le_one
#print axioms gCE_nonneg
#print axioms hCE_nonneg
#print axioms hCEij_nonneg
#print axioms hCE_le_pow
#print axioms gCE_le_pow
#print axioms mem_indSets
#print axioms tauCE_nonneg
#print axioms tauCE_zero
#print axioms tauCE_one
#print axioms tauCE_rec
#print axioms tauCE_closed
#print axioms tauCE_le
#print axioms tauCE_le'
#print axioms image_succ_add
#print axioms wCE_shift
#print axioms wCE_shift_insert
#print axioms gCE_succ
#print axioms gCE_split
#print axioms gCE_eq_sum
#print axioms hCE_succ_eq
#print axioms hCEij_eq
#print axioms hCEij_combo
#print axioms wCE_succ_le
#print axioms four_term_le
#print axioms hCE_eq_sum
#print axioms hCE_split4
#print axioms hCE_recurrence
#print axioms hCE_recurrence'
#print axioms hCE00_eq
#print axioms pathPos_injOn
#print axioms pathPos_lt
#print axioms key_facts
#print axioms image_mem_indSets
#print axioms hCE00_le
#print axioms hCE00_bound
#print axioms hCE_bound
#print axioms gCE_bound
#print axioms gCE_bounded

end CameronErdos
