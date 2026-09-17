import Erdos210Ordinary.Cell

/-!
# Erdős Problem 210 — visibility from a point of order zero

Two facts about a point `p` of order zero of a non-collinear finite set `P`, both phrased through
the open ordinary cell `W P p` (route memo, Phase 3 (i)–(ii)).

* `sameSide_of_visible`: if the whole open segment `(p, x)` stays inside `W P p` and `x` is off a
  connecting line `c d` missing `p`, then `x` lies strictly on the same side of that line as `p`.
  Indeed, otherwise `exists_cross_of_oppSide` produces a point of `line(c, d)` on `(p, x)`, hence
  inside `W P p`, contradicting Lemma B (`not_mem_W_of_conn_missing`).

* `exists_visible_ordinary`: every point of order zero sees, along a segment contained in
  `W P p`, a point `x ∉ P` of some *ordinary* line. This re-runs the first-crossing construction
  of `Cell.lean` from an arbitrary connecting line missing `p` (supplied by Lemma 2,
  `exists_conn_missing`): slide the connecting line's point `q` to a point `w₁` off every ray
  issued from `p` through a point of `P`, take the first connecting line missing `p` that crosses
  the half-open segment `(p, w₁]`, and let `x` be that first crossing point. Lemma A
  (`ordinary_of_visible`) makes the crossed pair ordinary, and the crossing-freeness of `(p, x)`
  turns into the containment `(p, x) ⊆ W P p` by an affine sign argument.

The private helpers `onLine_shift'`, `shift_injective'`, `ray_meets_line_at_most_once'`,
`exists_good_shift'`, `crossParam'`, `crossParam_spec'` and `crossParam_eq'` are copies of the
homonymous private helpers of `Cell.lean`, which are not exported.
-/

namespace Erdos210

/-! ### Copies of the private helpers of `Cell.lean` -/

/-- Shifting a point of the line `c d` by a multiple of the direction `d - c` keeps it on the
line. -/
private theorem onLine_shift' {c d w : ℝ × ℝ} (hw : OnLine c d w) (t : ℝ) :
    OnLine c d (w + t • (d - c)) := by
  simp only [OnLine, D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hw ⊢
  linear_combination hw

/-- Along a nonzero direction the parametrisation `t ↦ p + t • v` is injective. -/
private theorem shift_injective' {p v : ℝ × ℝ} (hv : v ≠ 0) {t t' : ℝ}
    (h : p + t • v = p + t' • v) : t = t' := by
  have h1 : (t - t') • v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel h
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 hv

/-- A ray issued from a point `p` off the line `c d` meets that line at most once. -/
private theorem ray_meets_line_at_most_once' {c d p w : ℝ × ℝ} (hcd : c ≠ d) (hw : OnLine c d w)
    (hpcd : ¬ OnLine c d p) (r : ℝ × ℝ) :
    Set.Subsingleton {t : ℝ | ∃ l : ℝ, 0 < l ∧ w + t • (d - c) = p + l • (r - p)} := by
  rintro t ⟨l, -, hteq⟩ t' ⟨l', -, hteq'⟩
  by_contra hne
  have hdc : d - c ≠ (0 : ℝ × ℝ) := sub_ne_zero.mpr (Ne.symm hcd)
  have hzne : w + t • (d - c) ≠ w + t' • (d - c) := fun h => hne (shift_injective' hdc h)
  have hz : OnLine c d (w + t • (d - c)) := onLine_shift' hw t
  have hz' : OnLine c d (w + t' • (d - c)) := onLine_shift' hw t'
  by_cases hpr : p = r
  · subst hpr
    refine hpcd ?_
    have hzp : w + t • (d - c) = p := by rw [hteq, sub_self, smul_zero, add_zero]
    rwa [hzp] at hz
  · have h1 : OnLine p r (w + t • (d - c)) := by rw [hteq]; exact onLine_param p r l
    have h2 : OnLine p r (w + t' • (d - c)) := by rw [hteq']; exact onLine_param p r l'
    exact hpcd ((onLine_iff_of_two hpr hcd h1 h2 hz hz' hzne p).mp (onLine_left p r))

/-- An arbitrarily small shift along the line `c d` avoiding every ray issued from `p` through a
point of `P`. -/
private theorem exists_good_shift' (P : Finset (ℝ × ℝ)) {c d p w : ℝ × ℝ} (hcd : c ≠ d)
    (hw : OnLine c d w) (hpcd : ¬ OnLine c d p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁ : ℝ, |t₁| < δ ∧ ∀ r ∈ P, ∀ l : ℝ, 0 < l → w + t₁ • (d - c) ≠ p + l • (r - p) := by
  have hBfin : (⋃ r ∈ (P : Set (ℝ × ℝ)),
      {t : ℝ | ∃ l : ℝ, 0 < l ∧ w + t • (d - c) = p + l • (r - p)}).Finite :=
    Set.Finite.biUnion P.finite_toSet
      fun r _ => (ray_meets_line_at_most_once' hcd hw hpcd r).finite
  have hinf : (Set.Ioo (-δ) δ).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨t₁, ht₁⟩ := (hinf.sdiff hBfin).nonempty
  obtain ⟨ht₁mem, ht₁nb⟩ := ht₁
  refine ⟨t₁, abs_lt.mpr ⟨ht₁mem.1, ht₁mem.2⟩, fun r hr l hl heq => ht₁nb ?_⟩
  exact Set.mem_biUnion (Finset.mem_coe.mpr hr) ⟨l, hl, heq⟩

open scoped Classical in
/-- The parameter at which the line `u.1 u.2` crosses the half-open segment from `p` to `q`,
when it does (and `0` otherwise). -/
private noncomputable def crossParam' (p q : ℝ × ℝ) (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if h : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (q - p)) then h.choose else 0

/-- Defining property of `crossParam'`. -/
private theorem crossParam_spec' (p q : ℝ × ℝ) (u : (ℝ × ℝ) × (ℝ × ℝ))
    (h : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (q - p))) :
    0 < crossParam' p q u ∧ crossParam' p q u ≤ 1 ∧
      OnLine u.1 u.2 (p + crossParam' p q u • (q - p)) := by
  have hc : crossParam' p q u = h.choose := by simp only [crossParam', dite_eq_left h]
  rw [hc]
  exact h.choose_spec

/-- A line missing `p` meets the line through `p` and `q ≠ p` in at most one point. -/
private theorem crossParam_eq' {p q : ℝ × ℝ} (hpq : p ≠ q) {a b : ℝ × ℝ} (hab : a ≠ b)
    (hp : ¬ OnLine a b p) {t t' : ℝ} (ht : OnLine a b (p + t • (q - p)))
    (ht' : OnLine a b (p + t' • (q - p))) : t = t' := by
  by_contra hne
  have hqp : q - p ≠ (0 : ℝ × ℝ) := sub_ne_zero.mpr (Ne.symm hpq)
  have hzz : p + t • (q - p) ≠ p + t' • (q - p) := fun h => hne (shift_injective' hqp h)
  exact hp ((onLine_iff_of_two hpq hab (onLine_param p q t) (onLine_param p q t') ht ht'
    hzz p).mp (onLine_left p q))

/-! ### (ii) Visibility forces the same side -/

/-- (ii): visibility through `W P p` forces the same side of every connecting line missing `p`. -/
theorem sameSide_of_visible {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) {c d : ℝ × ℝ} (hc : c ∈ P) (hd : d ∈ P) (hcd : c ≠ d)
    (hpcd : ¬ OnLine c d p) {x : ℝ × ℝ} (hx : ¬ OnLine c d x)
    (hvis : ∀ t : ℝ, 0 < t → t < 1 → p + t • (x - p) ∈ W P p) : SameSide c d p x := by
  by_contra hns
  have hne : D c d p * D c d x ≠ 0 := mul_ne_zero hpcd hx
  have hopp : OppSide c d p x := lt_of_le_of_ne (not_lt.1 hns) hne
  obtain ⟨t, ht0, ht1, hon⟩ := exists_cross_of_oppSide hopp
  exact not_mem_W_of_conn_missing hP hp hc hd hcd hpcd hon (hvis t ht0 ht1)

/-- A crossing-free open segment stays strictly on one side of the line. -/
private theorem sameSide_of_nocross {a b p x : ℝ × ℝ} (hnp : ¬ OnLine a b p)
    (hcross : ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine a b (p + t • (x - p)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : SameSide a b p (p + t • (x - p)) := by
  by_contra hns
  have hne : D a b p * D a b (p + t • (x - p)) ≠ 0 := mul_ne_zero hnp (hcross t ht0 ht1)
  have hopp : OppSide a b p (p + t • (x - p)) := lt_of_le_of_ne (not_lt.1 hns) hne
  obtain ⟨t', ht'0, ht'1, hon⟩ := exists_cross_of_oppSide hopp
  have hkey : p + t' • (p + t • (x - p) - p) = p + (t' * t) • (x - p) := by module
  rw [hkey] at hon
  exact hcross (t' * t) (mul_pos ht'0 ht0) (by nlinarith) hon

/-! ### (i) Every point of order zero sees an ordinary line -/

/-- (i): every point of order zero sees a point off `P` of some ordinary line. -/
theorem exists_visible_ordinary {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) :
    ∃ a b : ℝ × ℝ, a ≠ b ∧ ({a, b} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P ∧
      ∃ x : ℝ × ℝ, OnLine a b x ∧ x ∉ P ∧ ∀ t : ℝ, 0 < t → t < 1 → p + t • (x - p) ∈ W P p := by
  classical
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  -- a point of `P` other than `p`
  obtain ⟨q, hqP, hqp⟩ : ∃ q ∈ P, q ≠ p := by
    obtain ⟨a₀, ha₀, b₀, hb₀, c₀, hc₀, habc⟩ := hP
    by_contra hcon
    have hall : ∀ r ∈ P, r = p := fun r hr => by
      by_contra hrp
      exact hcon ⟨r, hr, hrp⟩
    rw [hall a₀ ha₀, hall b₀ hb₀, hall c₀ hc₀] at habc
    exact habc (D_self_left p p)
  -- Lemma 2: a connecting line through `q` missing `p`
  obtain ⟨c, hc, d, hd, hcd, hcdq, hpcd⟩ := exists_conn_missing hP hpP hqP (Ne.symm hqp)
  -- slide `q` off every ray issued from `p` through a point of `P`
  obtain ⟨t₁, -, ht₁good⟩ := exists_good_shift' P hcd hcdq hpcd (δ := 1) one_pos
  set w₁ := q + t₁ • (d - c) with hw₁def
  have hw₁line : OnLine c d w₁ := onLine_shift' hcdq t₁
  have hw₁p : w₁ ≠ p := fun h => hpcd (h ▸ hw₁line)
  have hw₁mp : w₁ - p ≠ (0 : ℝ × ℝ) := sub_ne_zero.mpr hw₁p
  -- the crossing family
  obtain ⟨T, hT⟩ : ∃ T : Finset ((ℝ × ℝ) × (ℝ × ℝ)), ∀ u, u ∈ T ↔
      (u.1 ∈ P ∧ u.2 ∈ P ∧ u.1 ≠ u.2 ∧ ¬ OnLine u.1 u.2 p ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (w₁ - p))) := by
    refine ⟨(P ×ˢ P).filter fun u => u.1 ≠ u.2 ∧ ¬ OnLine u.1 u.2 p ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (w₁ - p)), fun u => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product]
    tauto
  have hTne : T.Nonempty := by
    refine ⟨(c, d), (hT (c, d)).2 ⟨hc, hd, hcd, hpcd, 1, one_pos, le_refl 1, ?_⟩⟩
    have h1 : p + (1 : ℝ) • (w₁ - p) = w₁ := by module
    rw [h1]
    exact hw₁line
  obtain ⟨s, hsT, hsmin⟩ := T.exists_min_image (crossParam' p w₁) hTne
  obtain ⟨hs1P, hs2P, hsne, hsp, hsex⟩ := (hT s).1 hsT
  obtain ⟨ht₀pos, ht₀le, ht₀on⟩ := crossParam_spec' p w₁ s hsex
  set t₀ := crossParam' p w₁ s with ht₀def
  -- the first crossing point
  have hxp : p + t₀ • (w₁ - p) ≠ p := by
    intro h
    have h2 : p + t₀ • (w₁ - p) = p + (0 : ℝ) • (w₁ - p) := by
      rw [zero_smul, add_zero]; exact h
    exact absurd (shift_injective' hw₁mp h2) (ne_of_gt ht₀pos)
  have hxP : p + t₀ • (w₁ - p) ∉ P := by
    intro hmem
    refine ht₁good _ hmem (1 / t₀) (one_div_pos.mpr ht₀pos) ?_
    have h1 : (1 / t₀) * t₀ = 1 := one_div_mul_cancel (ne_of_gt ht₀pos)
    calc w₁ = p + ((1 / t₀) * t₀) • (w₁ - p) := by rw [h1]; module
      _ = p + (1 / t₀) • (p + t₀ • (w₁ - p) - p) := by module
  -- minimality: the open segment `(p, x)` is crossed by no connecting line missing `p`
  have hvis : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ OnLine a b p →
      ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine a b (p + t • (p + t₀ • (w₁ - p) - p)) := by
    intro a ha b hb hab hnp t ht0 ht1 hon
    have hkey : p + t • (p + t₀ • (w₁ - p) - p) = p + (t * t₀) • (w₁ - p) := by module
    rw [hkey] at hon
    have hlt : t * t₀ < t₀ := by nlinarith
    have hex : ∃ t' : ℝ, 0 < t' ∧ t' ≤ 1 ∧ OnLine a b (p + t' • (w₁ - p)) :=
      ⟨t * t₀, mul_pos ht0 ht₀pos, le_trans (le_of_lt hlt) ht₀le, hon⟩
    have hmem : ((a, b) : (ℝ × ℝ) × (ℝ × ℝ)) ∈ T := (hT (a, b)).2 ⟨ha, hb, hab, hnp, hex⟩
    obtain ⟨-, -, hon'⟩ := crossParam_spec' p w₁ (a, b) hex
    have heq : crossParam' p w₁ (a, b) = t * t₀ :=
      crossParam_eq' (Ne.symm hw₁p) hab hnp hon' hon
    have hge := hsmin (a, b) hmem
    rw [heq] at hge
    exact absurd hge (not_le.mpr hlt)
  -- Lemma A makes the crossed pair ordinary
  have hpair := ordinary_of_visible hp hxP hxp hvis hs1P hs2P hsne hsp ht₀on
  refine ⟨s.1, s.2, hsne, hpair, p + t₀ • (w₁ - p), ht₀on, hxP, ?_⟩
  intro t ht0 ht1
  have hmemW : ∀ e ∈ ordinaryPairs P, ∀ a' ∈ e, ∀ b' ∈ e, a' ≠ b' →
      SameSide a' b' p (p + t • (p + t₀ • (w₁ - p) - p)) := by
    intro e he a' ha' b' hb' hab'
    obtain ⟨hsub, -, hline⟩ := mem_ordinaryPairs.1 he
    have hnp : ¬ OnLine a' b' p := fun hon => hpe e he (hline a' ha' b' hb' hab' p hpP hon)
    exact sameSide_of_nocross hnp (hvis a' (hsub ha') b' (hsub hb') hab' hnp) ht0 ht1
  exact hmemW

end Erdos210
