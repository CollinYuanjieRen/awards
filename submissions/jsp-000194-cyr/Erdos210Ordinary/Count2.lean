import Erdos210Ordinary.Count
import Erdos210Ordinary.Arrangement

/-!
# Erdős Problem 210 — Motzkin's bound

Lemma C sends a point of order zero to its sign vector over the ordinary pairs of `P`, injectively
(`injOn_sgn`). Enumerating the ordinary pairs as an arrangement of `m := |ordinaryPairs P|`
oriented lines `L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)` (each pair in the orientation `rep`), a point of
order zero lies on none of these lines and its sign vector is one of the sign vectors realized by
the arrangement.

Motzkin's cell count (`ncard_realized_le`) bounds the number of those vectors by `1 + m(m+1)/2`,
so `|orderZero P| ≤ 1 + m(m+1)/2` and, with Lemma 1 (`card_sdiff_orderZero_le`),
`|P| ≤ 2 m + 1 + m(m+1)/2`, replacing the `2 ^ m` of `Count.lean`.
-/

namespace Erdos210

/-- The arrangement attached to `P`: the ordinary pairs of `P`, enumerated by `Finset.equivFin`
and oriented by `rep`. -/
private noncomputable def arr (P : Finset (ℝ × ℝ)) :
    Fin (ordinaryPairs P).card → (ℝ × ℝ) × (ℝ × ℝ) :=
  fun i => rep ((ordinaryPairs P).equivFin.symm i).1

private theorem arr_ne {P : Finset (ℝ × ℝ)} (i : Fin (ordinaryPairs P).card) :
    (arr P i).1 ≠ (arr P i).2 :=
  (rep_spec (mem_ordinaryPairs.1 ((ordinaryPairs P).equivFin.symm i).2).2.1).1

/-- A point of `P` on the line of an ordinary pair, in the orientation `rep`, belongs to the pair. -/
private theorem mem_of_rep_onLine {P : Finset (ℝ × ℝ)} {e : Finset (ℝ × ℝ)}
    (he : e ∈ ordinaryPairs P) {p : ℝ × ℝ} (hpP : p ∈ P)
    (h0 : D (rep e).1 (rep e).2 p = 0) : p ∈ e := by
  obtain ⟨-, hcard, hline⟩ := mem_ordinaryPairs.1 he
  obtain ⟨hne, hrep⟩ := rep_spec hcard
  have hr₁ : (rep e).1 ∈ e := (Finset.ext_iff.1 hrep _).2 (Finset.mem_insert_self _ _)
  have hr₂ : (rep e).2 ∈ e :=
    (Finset.ext_iff.1 hrep _).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact hline _ hr₁ _ hr₂ hne p hpP h0

/-- A point of order zero lies on none of the lines of the arrangement. -/
private theorem offLines_of_mem_orderZero {P : Finset (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ orderZero P) : OffLines (arr P) (ordinaryPairs P).card p := by
  intro i _ h0
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  exact hpe _ ((ordinaryPairs P).equivFin.symm i).2
    (mem_of_rep_onLine ((ordinaryPairs P).equivFin.symm i).2 hpP h0)

/-- The sign vector over the arrangement determines the point of order zero. -/
private theorem injOn_sv {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    Set.InjOn (fun p => sv (arr P) (ordinaryPairs P).card p) ↑(orderZero P) := by
  intro p hp q hq h
  simp only at h
  refine injOn_sgn hP hp hq ?_
  funext x
  have hval : ((ordinaryPairs P).equivFin x).val < (ordinaryPairs P).card :=
    ((ordinaryPairs P).equivFin x).isLt
  have hsv : ∀ r : ℝ × ℝ, sv (arr P) (ordinaryPairs P).card r ((ordinaryPairs P).equivFin x)
      = decide (0 < D (rep x.1).1 (rep x.1).2 r) := by
    intro r
    have : sv (arr P) (ordinaryPairs P).card r ((ordinaryPairs P).equivFin x)
        = decide (0 < D (arr P ((ordinaryPairs P).equivFin x)).1
            (arr P ((ordinaryPairs P).equivFin x)).2 r) := by
      simp only [sv]
      exact ite_eq_left hval
    rw [this]
    simp only [arr, Equiv.symm_apply_apply]
  have hpq := congrFun h ((ordinaryPairs P).equivFin x)
  rw [hsv p, hsv q] at hpq
  exact hpq

theorem card_orderZero_le_motzkin {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    (orderZero P).card ≤ 1 + (ordinaryPairs P).card * ((ordinaryPairs P).card + 1) / 2 := by
  have himg : (fun p => sv (arr P) (ordinaryPairs P).card p) '' ↑(orderZero P)
      ⊆ realized (arr P) (ordinaryPairs P).card := by
    rintro v ⟨p, hp, rfl⟩
    exact ⟨p, offLines_of_mem_orderZero (Finset.mem_coe.1 hp), rfl⟩
  calc (orderZero P).card = (↑(orderZero P) : Set (ℝ × ℝ)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ = ((fun p => sv (arr P) (ordinaryPairs P).card p) '' ↑(orderZero P)).ncard :=
        (Set.InjOn.ncard_image (injOn_sv hP)).symm
    _ ≤ (realized (arr P) (ordinaryPairs P).card).ncard :=
        Set.ncard_le_ncard himg (realized_finite _ _)
    _ ≤ 1 + (ordinaryPairs P).card * ((ordinaryPairs P).card + 1) / 2 :=
        ncard_realized_le (arr P) (fun i => arr_ne i) _ le_rfl

theorem card_le_of_notCollinear_motzkin {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) :
    P.card ≤ 2 * (ordinaryPairs P).card +
      (1 + (ordinaryPairs P).card * ((ordinaryPairs P).card + 1) / 2) := by
  have hsub : orderZero P ⊆ P := fun x hx => (mem_orderZero.1 hx).1
  calc P.card = (P \ orderZero P).card + (orderZero P).card :=
        (Finset.card_sdiff_add_card_eq_card hsub).symm
    _ ≤ 2 * (ordinaryPairs P).card +
          (1 + (ordinaryPairs P).card * ((ordinaryPairs P).card + 1) / 2) :=
        Nat.add_le_add (card_sdiff_orderZero_le P) (card_orderZero_le_motzkin hP)

end Erdos210
