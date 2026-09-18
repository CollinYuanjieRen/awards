import CameronErdos.Counting.Basic

/-!
# `Lem11_Projection`: the Lev–Smeliansky projection `π : ℤ → ℤ/tℤ`

This file formalises Green's Lemma 11 (Green, *The Cameron–Erdős conjecture*, 2004, p. 9).

Throughout, `A ⊆ [1, N]` is a finite set of integers, `t` is a positive modulus with
`N/4 < t`, and `π : ℤ → ZMod t` is reduction mod `t` (`Int.cast`).  We write
`projImage t A = π(A)`.

The three parts are:

* `card_le_card_projImage` (and the `Ioo`/`Icc` variants): `π` is injective on any subset of
  an interval of length `t`, so `|π(A)| ≥ |B|` for every such `B ⊆ A`;
* `projection_popularDiff_mem`: `d ∈ D(A, 4δN) → π(d) ∈ D(π(A), δN)` — each residue class
  meets `A` in at most `4` points, so the map on representations is at most `4`-to-one;
* `projection_popularDiff_lift`: `e ∈ D(π(A), 8δN) → ∃ d ∈ π⁻¹(e) ∩ (−N, N), d ∈ D(A, δN)` —
  the differences `a − a'` lie in `(−N, N)`, an interval meeting the residue class `e` in at
  most `8` points, so pigeonhole supplies a popular lift.
-/

open Finset

namespace CameronErdos

section Projection

variable {N t : ℕ} {A : Finset ℤ}

/-- `projImage t A = π(A)`, the image of `A` under reduction mod `t`. -/
def projImage (t : ℕ) (A : Finset ℤ) : Finset (ZMod t) :=
  A.image (Int.cast : ℤ → ZMod t)

@[simp] lemma mem_projImage {t : ℕ} {A : Finset ℤ} {b : ZMod t} :
    b ∈ projImage t A ↔ ∃ a ∈ A, (a : ZMod t) = b := by
  simp [projImage]

lemma mem_projImage_of_mem {t : ℕ} {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    (a : ZMod t) ∈ projImage t A :=
  mem_projImage.2 ⟨a, ha, rfl⟩

lemma projImage_subset {t : ℕ} {A B : Finset ℤ} (h : B ⊆ A) :
    projImage t B ⊆ projImage t A :=
  Finset.image_subset_image h

/-! ### An interval of length `t` injects into `ZMod t` -/

/-- Two integers with the same residue mod `t` and differing by less than `t` are equal. -/
lemma eq_of_intCast_eq_of_abs_sub_lt (ht : 0 < t) {a b : ℤ}
    (hcast : (a : ZMod t) = (b : ZMod t)) (hab : b - a < t) (hba : a - b < t) : a = b := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b t).1 hcast
  have htZ : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have hc1 : c < 1 := by
    have : (t : ℤ) * c < (t : ℤ) * 1 := by rw [← hc]; simpa using hab
    exact lt_of_mul_lt_mul_left this htZ.le
  have hc2 : -1 < c := by
    have : (t : ℤ) * (-1) < (t : ℤ) * c := by rw [← hc]; linarith
    exact lt_of_mul_lt_mul_left this htZ.le
  have hc0 : c = 0 := by omega
  rw [hc0, mul_zero] at hc
  omega

/-- **Lemma 11 (i)**, injectivity.  Reduction mod `t` is injective on any set of integers
contained in a window of `t` consecutive integers. -/
lemma injOn_intCast_Ico (ht : 0 < t) {m : ℤ} {B : Finset ℤ}
    (hB : B ⊆ Finset.Ico m (m + t)) :
    Set.InjOn (Int.cast : ℤ → ZMod t) (B : Set ℤ) := by
  intro a ha b hb hcast
  have ha' := Finset.mem_Ico.1 (hB (by simpa using ha))
  have hb' := Finset.mem_Ico.1 (hB (by simpa using hb))
  exact eq_of_intCast_eq_of_abs_sub_lt ht hcast (by omega) (by omega)

/-- **Lemma 11 (i)**.  `π` is injective on a subset of an interval of length `t`. -/
theorem card_projImage_eq_of_Ico (ht : 0 < t) {m : ℤ} {B : Finset ℤ}
    (hB : B ⊆ Finset.Ico m (m + t)) : #(projImage t B) = #B :=
  Finset.card_image_of_injOn (injOn_intCast_Ico ht hB)

/-- **Lemma 11 (i)**.  If `B ⊆ A` lies in an interval of length `t`, then `|π(A)| ≥ |B|`. -/
theorem card_le_card_projImage (ht : 0 < t) {m : ℤ} {B : Finset ℤ} (hBA : B ⊆ A)
    (hB : B ⊆ Finset.Ico m (m + t)) : #B ≤ #(projImage t A) := by
  calc #B = #(projImage t B) := (card_projImage_eq_of_Ico ht hB).symm
    _ ≤ #(projImage t A) := Finset.card_le_card (projImage_subset hBA)

/-- **Lemma 11 (i)**, `Ioo` form: `B ⊆ (m, m + t)`. -/
theorem card_le_card_projImage_Ioo (ht : 0 < t) {m : ℤ} {B : Finset ℤ} (hBA : B ⊆ A)
    (hB : B ⊆ Finset.Ioo m (m + t)) : #B ≤ #(projImage t A) := by
  refine card_le_card_projImage (m := m + 1) ht hBA ?_
  intro a ha
  have := Finset.mem_Ioo.1 (hB ha)
  exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- **Lemma 11 (i)**, `Icc` form: `B ⊆ [m + 1, m + t]`. -/
theorem card_le_card_projImage_Icc (ht : 0 < t) {m : ℤ} {B : Finset ℤ} (hBA : B ⊆ A)
    (hB : B ⊆ Finset.Icc (m + 1) (m + t)) : #B ≤ #(projImage t A) := by
  refine card_le_card_projImage (m := m + 1) ht hBA ?_
  intro a ha
  have := Finset.mem_Icc.1 (hB ha)
  exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-! ### Residue classes meet short intervals in few points -/

/-- A set of integers lying in a single residue class mod `t` and inside a window of length
`k * t` has at most `k` elements. -/
lemma card_le_of_residue (ht : 0 < t) {S : Finset ℤ} {lo : ℤ} {k : ℕ} {b : ZMod t}
    (hlo : ∀ a ∈ S, lo ≤ a) (hhi : ∀ a ∈ S, a < lo + k * t)
    (hb : ∀ a ∈ S, (a : ZMod t) = b) : #S ≤ k := by
  classical
  have htZ : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have htne : (t : ℤ) ≠ 0 := ne_of_gt htZ
  have hmaps : Set.MapsTo (fun a : ℤ => (a - lo) / (t : ℤ)) (S : Set ℤ)
      (Finset.Ico (0 : ℤ) (k : ℤ) : Set ℤ) := by
    intro a ha
    have haS : a ∈ S := by simpa using ha
    have h1 : lo ≤ a := hlo a haS
    have h2 : a < lo + k * t := hhi a haS
    have hdm : (t : ℤ) * ((a - lo) / (t : ℤ)) + (a - lo) % (t : ℤ) = a - lo :=
      Int.mul_ediv_add_emod _ _
    have hr0 : 0 ≤ (a - lo) % (t : ℤ) := Int.emod_nonneg _ htne
    have hrt : (a - lo) % (t : ℤ) < (t : ℤ) := Int.emod_lt_of_pos _ htZ
    have hq0 : 0 ≤ (a - lo) / (t : ℤ) := by
      by_contra hcon
      rw [not_le] at hcon
      have : (t : ℤ) * ((a - lo) / (t : ℤ)) ≤ (t : ℤ) * (-1) := by
        exact mul_le_mul_of_nonneg_left (by omega) htZ.le
      simp only [mul_neg, mul_one] at this
      omega
    have hqk : (a - lo) / (t : ℤ) < (k : ℤ) := by
      have hlt : (t : ℤ) * ((a - lo) / (t : ℤ)) < (t : ℤ) * (k : ℤ) := by
        have : (t : ℤ) * (k : ℤ) = (k : ℤ) * (t : ℤ) := by ring
        omega
      exact lt_of_mul_lt_mul_left hlt htZ.le
    simpa using Finset.mem_Ico.2 ⟨hq0, hqk⟩
  have hinj : Set.InjOn (fun a : ℤ => (a - lo) / (t : ℤ)) (S : Set ℤ) := by
    intro a ha a' ha' hq
    have haS : a ∈ S := by simpa using ha
    have haS' : a' ∈ S := by simpa using ha'
    have hcast : (a : ZMod t) = (a' : ZMod t) := by rw [hb a haS, hb a' haS']
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a a' t).1 hcast
    have hdvd : (t : ℤ) ∣ (a' - lo) - (a - lo) := ⟨c, by linarith [hc]⟩
    have hmod : (a - lo) % (t : ℤ) = (a' - lo) % (t : ℤ) := Int.modEq_iff_dvd.2 hdvd
    have e1 : (t : ℤ) * ((a - lo) / (t : ℤ)) + (a - lo) % (t : ℤ) = a - lo :=
      Int.mul_ediv_add_emod _ _
    have e2 : (t : ℤ) * ((a' - lo) / (t : ℤ)) + (a' - lo) % (t : ℤ) = a' - lo :=
      Int.mul_ediv_add_emod _ _
    simp only at hq
    rw [hq, hmod, e2] at e1
    omega
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-- With `t > N/4`, every residue class mod `t` meets `A ⊆ [1, N]` in at most `4` points. -/
theorem card_fiber_le_four (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (ht : 0 < t)
    (htN : (N : ℝ) / 4 < t) (b : ZMod t) : #{a ∈ A | ((a : ℤ) : ZMod t) = b} ≤ 4 := by
  have hNt : (N : ℤ) < 4 * (t : ℤ) := by
    have : (N : ℝ) < 4 * (t : ℝ) := by linarith
    exact_mod_cast this
  refine card_le_of_residue (b := b) ht (lo := 1) (k := 4) ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_Icc.1 (hA (Finset.mem_filter.1 ha).1)).1
  · intro a ha
    have := (Finset.mem_Icc.1 (hA (Finset.mem_filter.1 ha).1)).2
    push_cast
    omega
  · intro a ha
    exact (Finset.mem_filter.1 ha).2

/-! ### Lemma 11 (ii): pushing popular differences forward -/

/-- The map `(a, a') ↦ (π a, π a')` on representations of `d` is at most `4`-to-one, so
`r_A(d) ≤ 4 · r_{π(A)}(π d)`. -/
theorem diffReps_le_four_mul (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (ht : 0 < t)
    (htN : (N : ℝ) / 4 < t) (d : ℤ) :
    diffReps A d ≤ 4 * diffReps (projImage t A) ((d : ZMod t)) := by
  classical
  set f : ℤ × ℤ → ZMod t × ZMod t := fun q => ((q.1 : ZMod t), (q.2 : ZMod t)) with hf
  have hmaps : ∀ q ∈ {q ∈ A ×ˢ A | q.1 - q.2 = d},
      f q ∈ {p ∈ projImage t A ×ˢ projImage t A | p.1 - p.2 = ((d : ZMod t))} := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · exact mem_projImage_of_mem hq.1.1
    · exact mem_projImage_of_mem hq.1.2
    · simp only [hf]
      rw [← Int.cast_sub, hq.2]
  have hfib : ∀ p ∈ {p ∈ projImage t A ×ˢ projImage t A | p.1 - p.2 = ((d : ZMod t))},
      #{q ∈ {q ∈ A ×ˢ A | q.1 - q.2 = d} | f q = p} ≤ 4 := by
    intro p _
    refine le_trans (Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_)
      (card_fiber_le_four hA ht htN p.1)
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_product] at hq
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hq.1.1.1, ?_⟩)
      have := hq.2
      simp only [hf, Prod.ext_iff] at this
      exact this.1
    · intro q hq q' hq' hqq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_product] at hq hq'
      simp only at hqq
      have h1 : q.1 - q.2 = d := hq.1.2
      have h2 : q'.1 - q'.2 = d := hq'.1.2
      have : q.2 = q'.2 := by omega
      exact Prod.ext hqq this
  simpa [diffReps] using
    Finset.card_le_mul_card_image_of_maps_to hmaps 4 hfib

/-- **Lemma 11 (ii)**.  If `d` is a `4δN`-popular difference of `A`, then `π d` is a
`δN`-popular difference of `π(A)`. -/
theorem projection_popularDiff_mem (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (ht : 0 < t)
    (htN : (N : ℝ) / 4 < t) {δ : ℝ} (hδ : 0 < δ) {d : ℤ}
    (hd : d ∈ popularDiff A (4 * δ * (N : ℝ))) :
    ((d : ZMod t)) ∈ popularDiff (projImage t A) (δ * (N : ℝ)) := by
  classical
  -- `A` is nonempty, hence `1 ≤ N`
  obtain ⟨a, ha, a', _, _⟩ := Finset.mem_sub.1 (Finset.mem_filter.1 hd).1
  have hN1 : 1 ≤ N := by
    have := Finset.mem_Icc.1 (hA ha)
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hKpos : 0 < 4 * δ * (N : ℝ) := by positivity
  have hδNpos : 0 < δ * (N : ℝ) := by positivity
  have h1 : 4 * δ * (N : ℝ) ≤ (diffReps A d : ℝ) := (mem_popularDiff_iff hKpos d).1 hd
  have h2 : (diffReps A d : ℝ) ≤ 4 * (diffReps (projImage t A) ((d : ZMod t)) : ℝ) := by
    have := diffReps_le_four_mul hA ht htN d
    exact_mod_cast this
  refine (mem_popularDiff_iff hδNpos _).2 ?_
  linarith

/-! ### Lemma 11 (iii): lifting popular differences -/

/-- **Lemma 11 (iii)**.  If `e` is an `8δN`-popular difference of `π(A)`, then some integer
lift `d ∈ (−N, N)` of `e` is a `δN`-popular difference of `A`. -/
theorem projection_popularDiff_lift (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (ht : 0 < t)
    (htN : (N : ℝ) / 4 < t) {δ : ℝ} (hδ : 0 < δ) {e : ZMod t}
    (he : e ∈ popularDiff (projImage t A) (8 * δ * (N : ℝ))) :
    ∃ d : ℤ, (d : ZMod t) = e ∧ -(N : ℤ) < d ∧ d < (N : ℤ) ∧
      d ∈ popularDiff A (δ * (N : ℝ)) := by
  classical
  -- `π(A)` is nonempty, hence so is `A`, hence `1 ≤ N`
  obtain ⟨b, hb, _, _, _⟩ := Finset.mem_sub.1 (Finset.mem_filter.1 he).1
  obtain ⟨a₀, ha₀, _⟩ := mem_projImage.1 hb
  have hN1 : 1 ≤ N := by
    have := Finset.mem_Icc.1 (hA ha₀)
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hKpos : 0 < 8 * δ * (N : ℝ) := by positivity
  have hδNpos : 0 < δ * (N : ℝ) := by positivity
  have hNt : (N : ℤ) < 4 * (t : ℤ) := by
    have : (N : ℝ) < 4 * (t : ℝ) := by linarith
    exact_mod_cast this
  -- the set of pairs of `A` whose projections differ by `e`
  set R : Finset (ℤ × ℤ) := {q ∈ A ×ˢ A | ((q.1 : ZMod t) - (q.2 : ZMod t)) = e} with hR
  -- every representation of `e` in `π(A)` comes from one in `R`
  have hTR : diffReps (projImage t A) e ≤ #R := by
    have hcard : #({p ∈ projImage t A ×ˢ projImage t A | p.1 - p.2 = e}) ≤ #R := by
      refine Finset.card_le_card_of_surjOn
        (fun q : ℤ × ℤ => ((q.1 : ZMod t), (q.2 : ZMod t))) ?_
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨u, hu, hu'⟩ := mem_projImage.1 hp.1.1
      obtain ⟨v, hv, hv'⟩ := mem_projImage.1 hp.1.2
      refine ⟨(u, v), ?_, ?_⟩
      · simp only [Finset.mem_coe, hR, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hu, hv⟩, by rw [hu', hv']; exact hp.2⟩
      · simp [hu', hv']
    simpa [diffReps] using hcard
  have hRlarge : 8 * δ * (N : ℝ) ≤ (#R : ℝ) := by
    have h1 : 8 * δ * (N : ℝ) ≤ (diffReps (projImage t A) e : ℝ) :=
      (mem_popularDiff_iff hKpos e).1 he
    have h2 : (diffReps (projImage t A) e : ℝ) ≤ (#R : ℝ) := by exact_mod_cast hTR
    linarith
  -- the candidate lifts
  set L : Finset ℤ := {d ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ) | (d : ZMod t) = e} with hL
  have hLcard : #L ≤ 8 := by
    refine card_le_of_residue (b := e) ht (lo := -(N : ℤ) + 1) (k := 8) ?_ ?_ ?_
    · intro d hd
      have := Finset.mem_Ioo.1 (Finset.mem_filter.1 hd).1
      omega
    · intro d hd
      have := Finset.mem_Ioo.1 (Finset.mem_filter.1 hd).1
      push_cast
      omega
    · intro d hd
      exact (Finset.mem_filter.1 hd).2
  have hmaps : ∀ q ∈ R, q.1 - q.2 ∈ L := by
    intro q hq
    rw [hR, Finset.mem_filter, Finset.mem_product] at hq
    have h1 := Finset.mem_Icc.1 (hA hq.1.1)
    have h2 := Finset.mem_Icc.1 (hA hq.1.2)
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by omega, by omega⟩, ?_⟩
    rw [Int.cast_sub]
    exact hq.2
  have hfw : #R = ∑ d ∈ L, #{q ∈ R | q.1 - q.2 = d} :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- pigeonhole over the (at most 8) lifts
  have hLne : L.Nonempty := by
    rcases Finset.eq_empty_or_nonempty L with hLe | h
    · exfalso
      rw [hLe] at hfw
      simp only [Finset.sum_empty] at hfw
      rw [hfw] at hRlarge
      simp only [Nat.cast_zero] at hRlarge
      linarith
    · exact h
  have hsum : ∑ _d ∈ L, δ * (N : ℝ) ≤ ∑ d ∈ L, (#{q ∈ R | q.1 - q.2 = d} : ℝ) := by
    have h1 : ∑ _d ∈ L, δ * (N : ℝ) = (#L : ℝ) * (δ * (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (#L : ℝ) ≤ 8 := by exact_mod_cast hLcard
    have h3 : ∑ d ∈ L, (#{q ∈ R | q.1 - q.2 = d} : ℝ) = (#R : ℝ) := by
      rw [hfw]; push_cast; ring
    rw [h1, h3]
    nlinarith [hδNpos, hRlarge]
  obtain ⟨d, hdL, hd⟩ := Finset.exists_le_of_sum_le hLne hsum
  have hdmem := Finset.mem_filter.1 hdL
  have hdIoo := Finset.mem_Ioo.1 hdmem.1
  refine ⟨d, hdmem.2, hdIoo.1, hdIoo.2, ?_⟩
  refine (mem_popularDiff_iff hδNpos d).2 ?_
  have hsub : {q ∈ R | q.1 - q.2 = d} = {q ∈ A ×ˢ A | q.1 - q.2 = d} := by
    ext q
    simp only [hR, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [← Int.cast_sub, h2, hdmem.2]
  rw [hsub] at hd
  simpa [diffReps] using hd

end Projection

/-! ## Axiom audit -/

#print axioms CameronErdos.eq_of_intCast_eq_of_abs_sub_lt
#print axioms CameronErdos.injOn_intCast_Ico
#print axioms CameronErdos.card_projImage_eq_of_Ico
#print axioms CameronErdos.card_le_card_projImage
#print axioms CameronErdos.card_le_card_projImage_Ioo
#print axioms CameronErdos.card_le_card_projImage_Icc
#print axioms CameronErdos.card_le_of_residue
#print axioms CameronErdos.card_fiber_le_four
#print axioms CameronErdos.diffReps_le_four_mul
#print axioms CameronErdos.projection_popularDiff_mem
#print axioms CameronErdos.projection_popularDiff_lift

end CameronErdos
