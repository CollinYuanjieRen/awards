import Erdos210Ordinary.Core

/-!
# Erdős Problem 210 — the cell lemma (Lemma B)

No connecting line of `P` that misses a point `p` of order zero meets the open cell `W P p`
(route memo §3.6).

Suppose `w ∈ W P p` lies on the connecting line `c d`, which misses `p`. Sliding `w` along the
direction `d - c` stays on that line (`onLine_shift`) and, for small shifts, stays inside `W P p`
(`W_small`). Each point `r` of `P` contributes at most one bad shift, because the ray from `p`
through `r` meets the line `c d` at most once (`ray_meets_line_at_most_once`); as the bad shifts
form a finite set inside an infinite interval, some admissible shift avoids all of them
(`exists_good_shift`), producing `w₁ ∈ W P p` on the line `c d`, off every ray from `p` through a
point of `P`.

Now take the *first* crossing of the segment `(p, w₁]` by a connecting line missing `p`: the
crossing family `T` is a nonempty finite set (it contains `(c, d)`), each of its members crosses the
line `p w₁` in exactly one point (`crossParam`, `crossParam_eq`), and minimising the crossing
parameter gives `s ∈ T` and `x := p + t₀ • (w₁ - p)` with `x ∉ P`, `x ≠ p`, and `(p, x)` free of
crossings. Lemma A (`ordinary_of_visible`) then makes `{s.1, s.2}` an ordinary pair, so
`x ∉ W P p`; but `x` lies on the segment from `p` to `w₁`, hence in `W P p` by convexity.
-/

namespace Erdos210

/-- Shifting a point of the line `c d` by a multiple of the direction `d - c` keeps it on the
line. -/
private theorem onLine_shift {c d w : ℝ × ℝ} (hw : OnLine c d w) (t : ℝ) :
    OnLine c d (w + t • (d - c)) := by
  simp only [OnLine, D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hw ⊢
  linear_combination hw

/-- Along a nonzero direction the parametrisation `t ↦ p + t • v` is injective. -/
private theorem shift_injective {p v : ℝ × ℝ} (hv : v ≠ 0) {t t' : ℝ}
    (h : p + t • v = p + t' • v) : t = t' := by
  have h1 : (t - t') • v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel h
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 hv

/-- A ray issued from a point `p` off the line `c d` meets that line at most once: at most one
shift parameter `t` puts `w + t • (d - c)` on the ray from `p` through `r`. -/
private theorem ray_meets_line_at_most_once {c d p w : ℝ × ℝ} (hcd : c ≠ d) (hw : OnLine c d w)
    (hpcd : ¬ OnLine c d p) (r : ℝ × ℝ) :
    Set.Subsingleton {t : ℝ | ∃ l : ℝ, 0 < l ∧ w + t • (d - c) = p + l • (r - p)} := by
  rintro t ⟨l, -, hteq⟩ t' ⟨l', -, hteq'⟩
  by_contra hne
  have hdc : d - c ≠ (0 : ℝ × ℝ) := sub_ne_zero.mpr (Ne.symm hcd)
  have hzne : w + t • (d - c) ≠ w + t' • (d - c) := fun h => hne (shift_injective hdc h)
  have hz : OnLine c d (w + t • (d - c)) := onLine_shift hw t
  have hz' : OnLine c d (w + t' • (d - c)) := onLine_shift hw t'
  by_cases hpr : p = r
  · subst hpr
    refine hpcd ?_
    have hzp : w + t • (d - c) = p := by rw [hteq, sub_self, smul_zero, add_zero]
    rwa [hzp] at hz
  · have h1 : OnLine p r (w + t • (d - c)) := by rw [hteq]; exact onLine_param p r l
    have h2 : OnLine p r (w + t' • (d - c)) := by rw [hteq']; exact onLine_param p r l'
    exact hpcd ((onLine_iff_of_two hpr hcd h1 h2 hz hz' hzne p).mp (onLine_left p r))

/-- An arbitrarily small shift along the line `c d` avoiding every ray issued from `p` through a
point of `P`: the bad shifts form a finite set, while the admissible interval is infinite. -/
private theorem exists_good_shift (P : Finset (ℝ × ℝ)) {c d p w : ℝ × ℝ} (hcd : c ≠ d)
    (hw : OnLine c d w) (hpcd : ¬ OnLine c d p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁ : ℝ, |t₁| < δ ∧ ∀ r ∈ P, ∀ l : ℝ, 0 < l → w + t₁ • (d - c) ≠ p + l • (r - p) := by
  have hBfin : (⋃ r ∈ (P : Set (ℝ × ℝ)),
      {t : ℝ | ∃ l : ℝ, 0 < l ∧ w + t • (d - c) = p + l • (r - p)}).Finite :=
    Set.Finite.biUnion P.finite_toSet
      fun r _ => (ray_meets_line_at_most_once hcd hw hpcd r).finite
  have hinf : (Set.Ioo (-δ) δ).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨t₁, ht₁⟩ := (hinf.sdiff hBfin).nonempty
  obtain ⟨ht₁mem, ht₁nb⟩ := ht₁
  refine ⟨t₁, abs_lt.mpr ⟨ht₁mem.1, ht₁mem.2⟩, fun r hr l hl heq => ht₁nb ?_⟩
  exact Set.mem_biUnion (Finset.mem_coe.mpr hr) ⟨l, hl, heq⟩

open scoped Classical in
/-- The parameter at which the line `u.1 u.2` crosses the half-open segment from `p` to `q`,
when it does (and `0` otherwise). -/
private noncomputable def crossParam (p q : ℝ × ℝ) (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if h : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (q - p)) then h.choose else 0

/-- Defining property of `crossParam`. -/
private theorem crossParam_spec (p q : ℝ × ℝ) (u : (ℝ × ℝ) × (ℝ × ℝ))
    (h : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ OnLine u.1 u.2 (p + t • (q - p))) :
    0 < crossParam p q u ∧ crossParam p q u ≤ 1 ∧
      OnLine u.1 u.2 (p + crossParam p q u • (q - p)) := by
  have hc : crossParam p q u = h.choose := by simp only [crossParam, dite_eq_left h]
  rw [hc]
  exact h.choose_spec

/-- A line missing `p` meets the line through `p` and `q ≠ p` in at most one point. -/
private theorem crossParam_eq {p q : ℝ × ℝ} (hpq : p ≠ q) {a b : ℝ × ℝ} (hab : a ≠ b)
    (hp : ¬ OnLine a b p) {t t' : ℝ} (ht : OnLine a b (p + t • (q - p)))
    (ht' : OnLine a b (p + t' • (q - p))) : t = t' := by
  by_contra hne
  have hqp : q - p ≠ (0 : ℝ × ℝ) := sub_ne_zero.mpr (Ne.symm hpq)
  have hzz : p + t • (q - p) ≠ p + t' • (q - p) := fun h => hne (shift_injective hqp h)
  exact hp ((onLine_iff_of_two hpq hab (onLine_param p q t) (onLine_param p q t') ht ht'
    hzz p).mp (onLine_left p q))

/-- Lemma B. -/
theorem not_mem_W_of_conn_missing {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) {c d : ℝ × ℝ} (hc : c ∈ P) (hd : d ∈ P) (hcd : c ≠ d)
    (hpcd : ¬ OnLine c d p) {w : ℝ × ℝ} (hw : OnLine c d w) : w ∉ W P p := by
  classical
  -- `hP` is part of the frozen interface; the proof below does not need it.
  have _hP : NotCollinear P := hP
  intro hwW
  -- a nearby point `w₁` of the line `c d`, inside `W P p`, off every ray from `p` through `P`
  obtain ⟨δ, hδ, hδmem⟩ := W_small hwW (d - c)
  obtain ⟨t₁, ht₁abs, ht₁good⟩ := exists_good_shift P hcd hw hpcd hδ
  set w₁ := w + t₁ • (d - c) with hw₁def
  have hw₁W : w₁ ∈ W P p := hδmem t₁ ht₁abs
  have hw₁line : OnLine c d w₁ := onLine_shift hw t₁
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
  obtain ⟨s, hsT, hsmin⟩ := T.exists_min_image (crossParam p w₁) hTne
  obtain ⟨hs1P, hs2P, hsne, hsp, hsex⟩ := (hT s).1 hsT
  obtain ⟨ht₀pos, ht₀le, ht₀on⟩ := crossParam_spec p w₁ s hsex
  set t₀ := crossParam p w₁ s with ht₀def
  -- `x := p + t₀ • (w₁ - p)` satisfies the hypotheses of Lemma A
  have hxp : p + t₀ • (w₁ - p) ≠ p := by
    intro h
    have h2 : p + t₀ • (w₁ - p) = p + (0 : ℝ) • (w₁ - p) := by
      rw [zero_smul, add_zero]; exact h
    exact absurd (shift_injective hw₁mp h2) (ne_of_gt ht₀pos)
  have hxP : p + t₀ • (w₁ - p) ∉ P := by
    intro hmem
    refine ht₁good _ hmem (1 / t₀) (one_div_pos.mpr ht₀pos) ?_
    have h1 : (1 / t₀) * t₀ = 1 := one_div_mul_cancel (ne_of_gt ht₀pos)
    calc w₁ = p + ((1 / t₀) * t₀) • (w₁ - p) := by rw [h1]; module
      _ = p + (1 / t₀) • (p + t₀ • (w₁ - p) - p) := by module
  have hvis : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ OnLine a b p →
      ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine a b (p + t • (p + t₀ • (w₁ - p) - p)) := by
    intro a ha b hb hab hnp t ht0 ht1 hon
    have hkey : p + t • (p + t₀ • (w₁ - p) - p) = p + (t * t₀) • (w₁ - p) := by module
    rw [hkey] at hon
    have hlt : t * t₀ < t₀ := by nlinarith
    have hex : ∃ t' : ℝ, 0 < t' ∧ t' ≤ 1 ∧ OnLine a b (p + t' • (w₁ - p)) :=
      ⟨t * t₀, mul_pos ht0 ht₀pos, le_trans (le_of_lt hlt) ht₀le, hon⟩
    have hmem : ((a, b) : (ℝ × ℝ) × (ℝ × ℝ)) ∈ T := (hT (a, b)).2 ⟨ha, hb, hab, hnp, hex⟩
    obtain ⟨-, -, hon'⟩ := crossParam_spec p w₁ (a, b) hex
    have heq : crossParam p w₁ (a, b) = t * t₀ :=
      crossParam_eq (Ne.symm hw₁p) hab hnp hon' hon
    have hge := hsmin (a, b) hmem
    rw [heq] at hge
    exact absurd hge (not_le.mpr hlt)
  have hpair := ordinary_of_visible hp hxP hxp hvis hs1P hs2P hsne hsp ht₀on
  have hxW : p + t₀ • (w₁ - p) ∈ W P p :=
    W_segment (mem_W_self hp) hw₁W (le_of_lt ht₀pos) ht₀le
  exact not_mem_W_of_onLine hpair hsne ht₀on hxW

end Erdos210
