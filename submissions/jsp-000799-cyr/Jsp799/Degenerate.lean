import Jsp799.Defs

/-!
# JSP-000799 / Erdős #960 — degenerate parameter ranges

For `k ≤ 2` (with at least two points) the hypothesis `NoKCollinear A k` is already
contradictory, for `k = 3` every pair of points of `A` spans an ordinary line, and for `r = 2`
a single ordinary line suffices.  In all three ranges the threshold `f_{r,k}(n)` is `O(1)`.
-/

open Finset

namespace Erdos960

/-- With at least two points, `NoKCollinear A k` is impossible for `k ≤ 2`, so `0` forces. -/
private theorem forces_zero_of_k_le_two {r k n : ℕ} (hk : k ≤ 2) (hn : 2 ≤ n) :
    Forces r k n 0 := by
  intro A hA hNo _
  exfalso
  have hcard : 1 < A.card := by rw [hA]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  interval_cases k
  · refine hNo ∅ (Finset.empty_subset _) Finset.card_empty ?_
    rw [Finset.coe_empty]
    exact collinear_empty ℝ Point
  · refine hNo {p} (by simpa using hp) (Finset.card_singleton p) ?_
    rw [Finset.coe_singleton]
    exact collinear_singleton ℝ p
  · refine hNo {p, q} ?_ (Finset.card_pair hpq) ?_
    · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp, hq⟩
    · rw [Finset.coe_insert, Finset.coe_singleton]
      exact collinear_pair ℝ p q

/-- For `k ≤ 2` no configuration with at least two points avoids `k` collinear points
(any two points are collinear; a single point and the empty set are collinear), so the
forcing condition is vacuous and the threshold is `0`. -/
theorem f_eq_zero_of_k_le_two {r k n : ℕ} (hk : k ≤ 2) (hn : 2 ≤ n) : f r k n = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (forces_zero_of_k_le_two hk hn))

/-- With no three collinear points, every pair of distinct points of `A` is ordinary. -/
private theorem ordinaryPair_of_noThreeCollinear {A : Finset Point}
    (hNo : NoKCollinear A 3) {p q : Point} (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) :
    OrdinaryPair A p q := by
  refine ⟨hp, hq, hpq, ?_⟩
  intro x hx hc
  by_contra hcon
  have hxp : x ≠ p := fun h => hcon (Or.inl h)
  have hxq : x ≠ q := fun h => hcon (Or.inr h)
  refine hNo {p, q, x} ?_ ?_ ?_
  · rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hp, hq, hx⟩
  · exact Finset.card_eq_three.mpr
      ⟨p, q, x, hpq, fun h => hxp h.symm, fun h => hxq h.symm, rfl⟩
  · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
    exact hc

/-- For `k = 3` every line is ordinary, so any `r` points form an all-ordinary subset. -/
theorem f_eq_zero_of_k_eq_three {r n : ℕ} (hrn : r ≤ n) : f r 3 n = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  intro A hA hNo _
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (n := r) (by omega)
  exact ⟨B, hBA, hBcard, fun p hp q hq hpq =>
    ordinaryPair_of_noThreeCollinear hNo (hBA hp) (hBA hq) hpq⟩

/-- For `r = 2` a single ordinary line already provides the required pair. -/
theorem f_two_le_one (k n : ℕ) : f 2 k n ≤ 1 := by
  refine Nat.sInf_le ?_
  intro A hA hNo h1
  rw [ordCount] at h1
  obtain ⟨e, he⟩ := Finset.card_pos.mp h1
  have hord : IsOrdinaryLine A e := by
    classical
    exact (Finset.mem_filter.mp he).2
  clear he h1
  induction e using Sym2.ind with
  | _ p q =>
    rw [IsOrdinaryLine, Sym2.lift_mk] at hord
    have hp : p ∈ A := hord.1
    have hq : q ∈ A := hord.2.1
    have hpq : p ≠ q := hord.2.2.1
    refine ⟨{p, q}, ?_, Finset.card_pair hpq, ?_⟩
    · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp, hq⟩
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first
          | exact absurd rfl hab
          | exact (hab rfl).elim
          | exact hord
          | exact (ordinaryPair_comm A _ _).mp hord

end Erdos960

