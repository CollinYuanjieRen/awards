import Erdos210Ordinary.Cell

/-!
# Erdős Problem 210 — Lemma C and the count

The sign vector of a point of order zero, taken over the ordinary pairs of `P`, determines the
point (Lemma C). Concretely, choose an orientation `rep e = (a, b)` of each ordinary pair
`e = {a, b}` and send `p` to the Boolean vector `e ↦ decide (0 < D a b p)`.

If two points `p q` of order zero have the same sign vector then, for every ordinary pair and both
of its orientations, `p` and `q` lie strictly on the same side of the corresponding line (the
determinants do not vanish, because a point of order zero lies on no ordinary line), i.e.
`q ∈ W P p`. Were `q ≠ p`, non-collinearity would give a connecting line through `q` missing `p`
(`exists_conn_missing`), and Lemma B (`not_mem_W_of_conn_missing`) would put `q` outside `W P p`.

Hence `orderZero P` injects into the `2 ^ |ordinaryPairs P|` Boolean vectors, and together with
Lemma 1 (`card_sdiff_orderZero_le`) this bounds `|P|` by `2 m + 2 ^ m`.
-/

namespace Erdos210

/-! ### An orientation of each ordinary pair -/

open scoped Classical in
/-- A choice of orientation for a two-element set of points. -/
noncomputable def rep (e : Finset (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  if h : ∃ a b : ℝ × ℝ, a ≠ b ∧ e = {a, b} then (h.choose, h.choose_spec.choose) else (0, 0)

/-- Defining property of `rep` on two-element sets. -/
theorem rep_spec {e : Finset (ℝ × ℝ)} (he : e.card = 2) :
    (rep e).1 ≠ (rep e).2 ∧ e = {(rep e).1, (rep e).2} := by
  have h : ∃ a b : ℝ × ℝ, a ≠ b ∧ e = {a, b} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 he
    exact ⟨a, b, hab, rfl⟩
  have hr : rep e = (h.choose, h.choose_spec.choose) := by
    simp only [rep, dite_eq_left h]
  rw [hr]
  exact h.choose_spec.choose_spec

/-- The sign vector of `p` over the ordinary pairs of `P`, in the chosen orientations. -/
private noncomputable def sgn (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) :
    {e // e ∈ ordinaryPairs P} → Bool :=
  fun e => decide (0 < D (rep e.1).1 (rep e.1).2 p)

/-- Two nonzero reals whose strict positivity decides the same way have a positive product. -/
private theorem pos_mul_of_decide_eq {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : decide (0 < u) = decide (0 < v)) : 0 < u * v := by
  rw [decide_eq_decide] at h
  rcases lt_trichotomy u 0 with hu' | hu' | hu'
  · have hv0 : ¬ (0 < v) := fun hv' => absurd (h.2 hv') (not_lt.2 hu'.le)
    exact mul_pos_of_neg_of_neg hu' (lt_of_le_of_ne (not_lt.1 hv0) hv)
  · exact absurd hu' hu
  · exact mul_pos hu' (h.1 hu')

/-! ### Lemma C -/

/-- Equal sign vectors put `p` and `q` strictly on the same side of every ordinary line. -/
private theorem sameSide_of_sgn_eq {P : Finset (ℝ × ℝ)} {p q : ℝ × ℝ} (hp : p ∈ orderZero P)
    (hq : q ∈ orderZero P) (h : sgn P p = sgn P q) {e : Finset (ℝ × ℝ)}
    (he : e ∈ ordinaryPairs P) {a b : ℝ × ℝ} (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    SameSide a b p q := by
  obtain ⟨-, hcard, hline⟩ := mem_ordinaryPairs.1 he
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  obtain ⟨hqP, hqe⟩ := mem_orderZero.1 hq
  obtain ⟨r₁, r₂, hrr, hne, hrep⟩ :
      ∃ r₁ r₂ : ℝ × ℝ, rep e = (r₁, r₂) ∧ r₁ ≠ r₂ ∧ e = {r₁, r₂} :=
    ⟨(rep e).1, (rep e).2, rfl, (rep_spec hcard).1, (rep_spec hcard).2⟩
  have hr₁ : r₁ ∈ e := by rw [hrep]; exact Finset.mem_insert_self _ _
  have hr₂ : r₂ ∈ e := by
    rw [hrep]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hDp : D r₁ r₂ p ≠ 0 := fun h0 => hpe e he (hline _ hr₁ _ hr₂ hne p hpP h0)
  have hDq : D r₁ r₂ q ≠ 0 := fun h0 => hqe e he (hline _ hr₁ _ hr₂ hne q hqP h0)
  have hsg : decide (0 < D r₁ r₂ p) = decide (0 < D r₁ r₂ q) := by
    have hcf := congrFun h ⟨e, he⟩
    simpa only [sgn, hrr] using hcf
  have hkey : 0 < D r₁ r₂ p * D r₁ r₂ q := pos_mul_of_decide_eq hDp hDq hsg
  rw [hrep] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact hkey
  · exact sameSide_swap.1 hkey
  · exact absurd rfl hab

/-- Lemma C: the sign vector is injective on the points of order zero. -/
theorem injOn_sgn {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    Set.InjOn (sgn P) ↑(orderZero P) := by
  intro p hp q hq h
  have hp' : p ∈ orderZero P := Finset.mem_coe.1 hp
  have hq' : q ∈ orderZero P := Finset.mem_coe.1 hq
  by_contra hpq
  have hqW : q ∈ W P p := fun e he a ha b hb hab =>
    sameSide_of_sgn_eq hp' hq' h he ha hb hab
  obtain ⟨hpP, -⟩ := mem_orderZero.1 hp'
  obtain ⟨hqP, -⟩ := mem_orderZero.1 hq'
  obtain ⟨c, hc, d, hd, hcd, hcdq, hcdp⟩ := exists_conn_missing hP hpP hqP hpq
  exact not_mem_W_of_conn_missing hP hp' hc hd hcd hcdp hcdq hqW

/-! ### The count -/

theorem card_orderZero_le {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    (orderZero P).card ≤ 2 ^ (ordinaryPairs P).card := by
  have hmem : ∀ p ∈ orderZero P,
      sgn P p ∈ (Finset.univ : Finset ({e // e ∈ ordinaryPairs P} → Bool)) :=
    fun p _ => Finset.mem_univ _
  calc (orderZero P).card
      ≤ (Finset.univ : Finset ({e // e ∈ ordinaryPairs P} → Bool)).card :=
        Finset.card_le_card_of_injOn (sgn P) hmem (injOn_sgn hP)
    _ = 2 ^ (ordinaryPairs P).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

theorem card_le_of_notCollinear {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    P.card ≤ 2 * (ordinaryPairs P).card + 2 ^ (ordinaryPairs P).card := by
  have hsub : orderZero P ⊆ P := fun x hx => (mem_orderZero.1 hx).1
  calc P.card = (P \ orderZero P).card + (orderZero P).card :=
        (Finset.card_sdiff_add_card_eq_card hsub).symm
    _ ≤ 2 * (ordinaryPairs P).card + 2 ^ (ordinaryPairs P).card :=
        Nat.add_le_add (card_sdiff_orderZero_le P) (card_orderZero_le hP)

end Erdos210
