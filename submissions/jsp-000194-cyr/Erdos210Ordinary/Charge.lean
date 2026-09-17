import Erdos210Ordinary.Neighbour
import Erdos210Ordinary.Vision
import Erdos210Ordinary.Count

/-!
# Erdős Problem 210 — the charging argument and the linear bound

Phase 3 (iv).  Every point `p` of order zero is charged to the triple

* the ordinary pair `e_p = {a, b}` of `exists_visible_ordinary` (Neighbour.lean), i.e. an ordinary
  line carrying a point `x_p ∉ P` visible from `p` through the cell `W P p`;
* the side of that line on which `p` lies, as a `Bool`;
* which of the three pieces of `line(a, b) \ {a, b}` the visible point `x_p` lands in, as a
  `Fin 3` (`piece` of Vision.lean).

Two points of order zero with the same charge are equal: orienting the common pair as
`rep e = (r₁, r₂)` and writing `x_p = r₁ + s_p • (r₂ - r₁)`, one of the two vertices `r₁`, `r₂` is
not collinear with `p` and `p'` (otherwise the line `p p'` would be the line `r₁ r₂`, which misses
both points).  With that vertex `v`, visibility (`sameSide_of_visible`) applied to the connecting
line `v p'` — which misses `p` — gives `SameSide v p' p x_p`, and symmetrically
`SameSide v p p' x_{p'}`; the same `Bool` puts `p` and `p'` strictly on the same side of `r₁ r₂`
and the same `Fin 3` puts `x_p` and `x_{p'}` on the same side of `v`, so `no_double_vision`
(resp. `no_double_vision'` at `v = r₂`) is contradicted.

Hence `|orderZero P| ≤ 6 m` with `m = |ordinaryPairs P|`, and with Lemma 1
(`|P \ orderZero P| ≤ 2 m`) this gives the linear bound `|P| ≤ 8 m`.
-/

namespace Erdos210

/-! ### Algebraic identities -/

/-- `D` at the vertex `a` of the parametrised line: `D a c (a + s • (b - a)) = -s * D a b c`. -/
private theorem D_side_left (a b c : ℝ × ℝ) (s : ℝ) :
    D a c (a + s • (b - a)) = -s * D a b c := by
  simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- `D` at the vertex `b` of the parametrised line: `D b c (b + s • (b - a)) = -s * D a b c`. -/
private theorem D_side_right (a b c : ℝ × ℝ) (s : ℝ) :
    D b c (b + s • (b - a)) = -s * D a b c := by
  simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- The same point of the line, seen from the other vertex. -/
private theorem vertex_shift (a b : ℝ × ℝ) (s : ℝ) :
    a + s • (b - a) = b + (s - 1) • (b - a) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

private theorem param_zero (a b : ℝ × ℝ) : a + (0 : ℝ) • (b - a) = a := by
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

private theorem param_one (a b : ℝ × ℝ) : a + (1 : ℝ) • (b - a) = b := by
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

/-- Two unordered pairs agree in one of the two orders. -/
private theorem pair_eq_cases {a b c d : ℝ × ℝ} (hab : a ≠ b)
    (h : ({a, b} : Finset (ℝ × ℝ)) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset (ℝ × ℝ)) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hb : b ∈ ({c, d} : Finset (ℝ × ℝ)) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-! ### The charge -/

open scoped Classical in
/-- A choice of visibility data for `p`: an ordinary pair `(a, b)` of `P` together with a point `x`
of `line(a, b)` off `P` whose open segment to `p` stays inside the cell `W P p`
(`exists_visible_ordinary`).  Junk outside `orderZero P`. -/
noncomputable def visData (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  if h : ∃ v : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ), v.1 ≠ v.2.1 ∧
      ({v.1, v.2.1} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P ∧ OnLine v.1 v.2.1 v.2.2 ∧
      v.2.2 ∉ P ∧ ∀ t : ℝ, 0 < t → t < 1 → p + t • (v.2.2 - p) ∈ W P p
    then h.choose else (0, 0, 0)

/-- The ordinary pair charged by `p`. -/
noncomputable def visPair (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  {(visData P p).1, (visData P p).2.1}

/-- The point of that ordinary line which `p` sees. -/
noncomputable def visPoint (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ × ℝ := (visData P p).2.2

open scoped Classical in
/-- The parameter of `visPoint P p` on the line `visPair P p`, in the orientation given by `rep`. -/
noncomputable def visParam (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  if h : ∃ s : ℝ, visPoint P p =
      (rep (visPair P p)).1 + s • ((rep (visPair P p)).2 - (rep (visPair P p)).1)
    then h.choose else 0

/-- The charge of `p`: its ordinary pair, its side of that line, and the piece of the line in which
the visible point lands. -/
noncomputable def key (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : Finset (ℝ × ℝ) × Bool × Fin 3 :=
  (visPair P p, decide (0 < D (rep (visPair P p)).1 (rep (visPair P p)).2 p),
    piece (visParam P p))

private theorem visPair_eq (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) :
    visPair P p = {(visData P p).1, (visData P p).2.1} := rfl

private theorem visPoint_eq (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) :
    visPoint P p = (visData P p).2.2 := rfl

/-- The defining property of `visData` on `orderZero P`. -/
private theorem visData_spec {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) :
    (visData P p).1 ≠ (visData P p).2.1 ∧ visPair P p ∈ ordinaryPairs P ∧
      OnLine (visData P p).1 (visData P p).2.1 (visPoint P p) ∧ visPoint P p ∉ P ∧
      ∀ t : ℝ, 0 < t → t < 1 → p + t • (visPoint P p - p) ∈ W P p := by
  have h : ∃ v : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ), v.1 ≠ v.2.1 ∧
      ({v.1, v.2.1} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P ∧ OnLine v.1 v.2.1 v.2.2 ∧
      v.2.2 ∉ P ∧ ∀ t : ℝ, 0 < t → t < 1 → p + t • (v.2.2 - p) ∈ W P p := by
    obtain ⟨a, b, hab, he, x, hxline, hxP, hvis⟩ := exists_visible_ordinary hP hp
    exact ⟨(a, b, x), hab, he, hxline, hxP, hvis⟩
  have hd : visData P p = h.choose := by simp only [visData, dite_eq_left h]
  rw [visPair_eq, visPoint_eq, hd]
  exact h.choose_spec

/-- Everything the charging argument needs about the data attached to a point of order zero. -/
private theorem charge_spec {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) :
    ∃ r₁ r₂ : ℝ × ℝ, rep (visPair P p) = (r₁, r₂) ∧ r₁ ≠ r₂ ∧ visPair P p = {r₁, r₂} ∧
      visPair P p ∈ ordinaryPairs P ∧ r₁ ∈ P ∧ r₂ ∈ P ∧ p ∉ visPair P p ∧
      D r₁ r₂ p ≠ 0 ∧ visPoint P p = r₁ + visParam P p • (r₂ - r₁) ∧
      visParam P p ≠ 0 ∧ visParam P p ≠ 1 ∧
      ∀ t : ℝ, 0 < t → t < 1 → p + t • (visPoint P p - p) ∈ W P p := by
  obtain ⟨hab, he, hxline, hxP, hvis⟩ := visData_spec hP hp
  obtain ⟨hsub, hcard, hline⟩ := mem_ordinaryPairs.1 he
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  obtain ⟨r₁, r₂, hrr⟩ : ∃ r₁ r₂ : ℝ × ℝ, rep (visPair P p) = (r₁, r₂) := ⟨_, _, rfl⟩
  have hrne : r₁ ≠ r₂ := by simpa only [hrr] using (rep_spec hcard).1
  have hrpair : visPair P p = {r₁, r₂} := by simpa only [hrr] using (rep_spec hcard).2
  have hr₁ : r₁ ∈ visPair P p := by rw [hrpair]; exact Finset.mem_insert_self _ _
  have hr₂ : r₂ ∈ visPair P p := by
    rw [hrpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxr : OnLine r₁ r₂ (visPoint P p) := by
    have hpe2 : ({(visData P p).1, (visData P p).2.1} : Finset (ℝ × ℝ)) = {r₁, r₂} := by
      rw [← visPair_eq]; exact hrpair
    rcases pair_eq_cases hab hpe2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hxline
    · rw [← h1, ← h2]; exact onLine_comm.1 hxline
  have hex : ∃ s : ℝ, visPoint P p =
      (rep (visPair P p)).1 + s • ((rep (visPair P p)).2 - (rep (visPair P p)).1) := by
    simp only [hrr]
    exact exists_param_of_onLine hrne hxr
  have hparam : visPoint P p = r₁ + visParam P p • (r₂ - r₁) := by
    have hval : visParam P p = hex.choose := by simp only [visParam, dite_eq_left hex]
    have hr1eq : (rep (visPair P p)).1 = r₁ := by rw [hrr]
    have hr2eq : (rep (visPair P p)).2 = r₂ := by rw [hrr]
    have hspec : visPoint P p = (rep (visPair P p)).1 +
        visParam P p • ((rep (visPair P p)).2 - (rep (visPair P p)).1) := by
      rw [hval]; exact hex.choose_spec
    rw [hr1eq, hr2eq] at hspec
    exact hspec
  refine ⟨r₁, r₂, hrr, hrne, hrpair, he, hsub hr₁, hsub hr₂, hpe _ he,
    fun h0 => hpe _ he (hline _ hr₁ _ hr₂ hrne p hpP h0), hparam, ?_, ?_, hvis⟩
  · intro h0
    exact hxP (by rw [hparam, h0, param_zero]; exact hsub hr₁)
  · intro h1
    exact hxP (by rw [hparam, h1, param_one]; exact hsub hr₂)

/-- The charge determines the point of order zero. -/
private theorem injOn_key {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    Set.InjOn (key P) ↑(orderZero P) := by
  intro p hpm p' hpm' hkey
  have hp : p ∈ orderZero P := Finset.mem_coe.1 hpm
  have hp' : p' ∈ orderZero P := Finset.mem_coe.1 hpm'
  by_contra hne
  obtain ⟨hpP, -⟩ := mem_orderZero.1 hp
  obtain ⟨hp'P, -⟩ := mem_orderZero.1 hp'
  obtain ⟨r₁, r₂, hrep, hrne, hrpair, -, hr₁P, hr₂P, hpnot, hDp, hx, hs0, hs1, hvis⟩ :=
    charge_spec hP hp
  obtain ⟨q₁, q₂, hrep', -, hrpair', -, -, -, hp'not, hDp', hx', hs0', hs1', hvis'⟩ :=
    charge_spec hP hp'
  -- the two charges use the same ordinary pair, hence the same orientation
  have hpair : visPair P p = visPair P p' := congrArg Prod.fst hkey
  have hqr : (q₁, q₂) = (r₁, r₂) := by rw [← hrep', ← hpair, hrep]
  have hq₁ : q₁ = r₁ := congrArg Prod.fst hqr
  have hq₂ : q₂ = r₂ := congrArg Prod.snd hqr
  rw [hq₁, hq₂] at hrep' hrpair' hDp' hx'
  -- the two points lie strictly on the same side of that line
  have hkey2 : decide (0 < D r₁ r₂ p) = decide (0 < D r₁ r₂ p') := by
    have hc := congrArg (fun z => z.2.1) hkey
    simp only [key, hrep, hrep'] at hc
    exact hc
  have hside : 0 < D r₁ r₂ p * D r₁ r₂ p' := pos_mul_of_decide_eq' hDp hDp' hkey2
  -- the two visible points lie in the same piece of that line
  have hkey3 : piece (visParam P p) = piece (visParam P p') := congrArg (fun z => z.2.2) hkey
  obtain ⟨hss, hss'⟩ := piece_eq_imp hs0 hs1 hs0' hs1' hkey3
  -- neither point is a vertex of the pair
  have hr₁p : r₁ ≠ p := by
    intro h; exact hpnot (by rw [hrpair, ← h]; exact Finset.mem_insert_self _ _)
  have hr₂p : r₂ ≠ p := by
    intro h
    exact hpnot (by
      rw [hrpair, ← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hr₁p' : r₁ ≠ p' := by
    intro h; exact hp'not (by rw [hrpair', ← h]; exact Finset.mem_insert_self _ _)
  have hr₂p' : r₂ ≠ p' := by
    intro h
    exact hp'not (by
      rw [hrpair', ← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  by_cases hcol : OnLine r₁ p' p
  · -- `r₁`, `p`, `p'` are collinear, so `r₂`, `p`, `p'` are not: use the vertex `r₂`
    have hcol2 : ¬ OnLine r₂ p' p := by
      intro h2
      refine hDp ?_
      have e1 : OnLine p p' r₁ := by
        show D p p' r₁ = 0
        have hid : D p p' r₁ = - D r₁ p' p := by simp only [D]; ring
        rw [hid, show D r₁ p' p = 0 from hcol, neg_zero]
      have e2 : OnLine p p' r₂ := by
        show D p p' r₂ = 0
        have hid : D p p' r₂ = - D r₂ p' p := by simp only [D]; ring
        rw [hid, show D r₂ p' p = 0 from h2, neg_zero]
      exact (onLine_iff_of_onLine hne e1 e2 hrne p).2 (onLine_left p p')
    have hcol2' : ¬ OnLine r₂ p p' := by
      intro hcon
      refine hcol2 ?_
      show D r₂ p' p = 0
      have hid : D r₂ p' p = - D r₂ p p' := by simp only [D]; ring
      rw [hid, show D r₂ p p' = 0 from hcon, neg_zero]
    have hx2 : visPoint P p = r₂ + (visParam P p - 1) • (r₂ - r₁) := by
      rw [hx]; exact vertex_shift r₁ r₂ _
    have hx2' : visPoint P p' = r₂ + (visParam P p' - 1) • (r₂ - r₁) := by
      rw [hx']; exact vertex_shift r₁ r₂ _
    have hnx : ¬ OnLine r₂ p' (visPoint P p) := by
      show ¬ D r₂ p' (visPoint P p) = 0
      rw [hx2, D_side_right]
      exact mul_ne_zero (neg_ne_zero.2 (sub_ne_zero_of_ne hs1)) hDp'
    have hnx' : ¬ OnLine r₂ p (visPoint P p') := by
      show ¬ D r₂ p (visPoint P p') = 0
      rw [hx2', D_side_right]
      exact mul_ne_zero (neg_ne_zero.2 (sub_ne_zero_of_ne hs1')) hDp
    have h1 : SameSide r₂ p' p (visPoint P p) :=
      sameSide_of_visible hP hp hr₂P hp'P hr₂p' hcol2 hnx hvis
    have h2 : SameSide r₂ p p' (visPoint P p') :=
      sameSide_of_visible hP hp' hr₂P hpP hr₂p hcol2' hnx' hvis'
    exact no_double_vision' hx2 hx2' hss' hside h1 h2
  · -- `r₁`, `p`, `p'` are not collinear: use the vertex `r₁`
    have hcol' : ¬ OnLine r₁ p p' := by
      intro hcon
      refine hcol ?_
      show D r₁ p' p = 0
      have hid : D r₁ p' p = - D r₁ p p' := by simp only [D]; ring
      rw [hid, show D r₁ p p' = 0 from hcon, neg_zero]
    have hnx : ¬ OnLine r₁ p' (visPoint P p) := by
      show ¬ D r₁ p' (visPoint P p) = 0
      rw [hx, D_side_left]
      exact mul_ne_zero (neg_ne_zero.2 hs0) hDp'
    have hnx' : ¬ OnLine r₁ p (visPoint P p') := by
      show ¬ D r₁ p (visPoint P p') = 0
      rw [hx', D_side_left]
      exact mul_ne_zero (neg_ne_zero.2 hs0') hDp
    have h1 : SameSide r₁ p' p (visPoint P p) :=
      sameSide_of_visible hP hp hr₁P hp'P hr₁p' hcol hnx hvis
    have h2 : SameSide r₁ p p' (visPoint P p') :=
      sameSide_of_visible hP hp' hr₁P hpP hr₁p hcol' hnx' hvis'
    exact no_double_vision hx hx' hss hside h1 h2

/-! ### The count -/

/-- Each ordinary pair is charged by at most `2 * 3` points of order zero. -/
theorem card_orderZero_le_six_mul {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    (orderZero P).card ≤ 6 * (ordinaryPairs P).card := by
  have hmem : ∀ p ∈ orderZero P, key P p ∈
      ordinaryPairs P ×ˢ (Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro p hp
    obtain ⟨-, -, -, -, -, he, -, -, -, -, -, -, -, -⟩ := charge_spec hP hp
    simp only [key, Finset.mem_product, Finset.mem_univ, and_true]
    exact he
  calc (orderZero P).card
      ≤ (ordinaryPairs P ×ˢ (Finset.univ : Finset Bool) ×ˢ
          (Finset.univ : Finset (Fin 3))).card :=
        Finset.card_le_card_of_injOn (key P) hmem (injOn_key hP)
    _ = 6 * (ordinaryPairs P).card := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
          Fintype.card_bool, Fintype.card_fin]
        ring

/-- The linear bound: `n` non-collinear points determine at least `n / 8` ordinary lines. -/
theorem card_le_of_notCollinear_linear {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    P.card ≤ 8 * (ordinaryPairs P).card := by
  have hsub : orderZero P ⊆ P := fun x hx => (mem_orderZero.1 hx).1
  calc P.card = (P \ orderZero P).card + (orderZero P).card :=
        (Finset.card_sdiff_add_card_eq_card hsub).symm
    _ ≤ 2 * (ordinaryPairs P).card + 6 * (ordinaryPairs P).card :=
        Nat.add_le_add (card_sdiff_orderZero_le P) (card_orderZero_le_six_mul hP)
    _ = 8 * (ordinaryPairs P).card := by ring

end Erdos210
