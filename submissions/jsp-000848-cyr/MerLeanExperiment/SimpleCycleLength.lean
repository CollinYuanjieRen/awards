import MerLeanExperiment.BipartiteWalks
import MerLeanExperiment.Vendor.Schoenflies.Graph.Cycle
import Mathlib.Combinatorics.Graph.Simple

open scoped Graph

namespace Graph

/-- A simple cycle in a simple graph has at least three edges. -/
theorem IsCycleThrough.three_le_length
    {α β : Type*} {G : Graph α β} [G.Simple]
    {e : β} {a b : α} {W : List β} (h : G.IsCycleThrough e a b W) :
    3 ≤ (e :: W).length := by
  by_contra hlt
  have hWlt : W.length < 2 := by simp only [List.length_cons] at hlt; omega
  cases W with
  | nil =>
      exact h.isLink.ne h.isPath.isWalk.eq_of_nil
  | cons f T =>
      cases T with
      | nil =>
          have hlinkf : G.IsLink f a b := by
            cases h.isPath.isWalk with
            | @cons _ w _ _ _ hl htail =>
                have hwb : w = b := htail.eq_of_nil
                subst w
                exact hl
          have hef : e = f := h.isLink.eq hlinkf
          exact h.notMem (by simp [hef])
      | cons g T =>
          simp only [List.length_cons] at hWlt
          omega

/-- A simple cycle in a bipartite simple graph has at least four edges. -/
theorem IsCycleThrough.four_le_length_of_bicoloring
    {α β : Type*} {G : Graph α β} [G.Simple] (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {e : β} {a b : α} {W : List β} (h : G.IsCycleThrough e a b W) :
    4 ≤ (e :: W).length := by
  have hclosed : G.IsWalk a (e :: W.reverse) a :=
    .cons h.isLink h.isPath.reverse.isWalk
  have heven : Even (e :: W).length := by
    simpa using hclosed.even_length_of_bicoloring c hcolor
  have hthree : 3 ≤ (e :: W).length := h.three_le_length
  obtain ⟨k, hk⟩ := heven
  omega

end Graph
