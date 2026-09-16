import MerLeanExperiment.Vendor.Schoenflies.Graph.Walk
import Mathlib.Algebra.Ring.Parity

open scoped Graph

namespace Graph

/-- The parity of a walk length determines the endpoint color. -/
theorem IsWalk.color_val_end
    {α β : Type*} {G : Graph α β} (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {a b : α} {W : List β} (h : G.IsWalk a W b) :
    (c b).val = ((c a).val + W.length) % 2 := by
  induction h with
  | @nil x hx =>
      simp only [List.length_nil, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (c x).isLt).symm
  | @cons u w v e W hl hW ih =>
      have hne : (c u).val ≠ (c w).val := by
        intro heq
        exact hcolor e u w hl (Fin.ext heq)
      have hstep : (c w).val = ((c u).val + 1) % 2 := by
        omega
      simp only [List.length_cons]
      omega

/-- A closed walk in a bipartite graph has even length. -/
theorem IsWalk.even_length_of_bicoloring
    {α β : Type*} {G : Graph α β} (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {a : α} {W : List β} (h : G.IsWalk a W a) : Even W.length := by
  have hend := h.color_val_end c hcolor
  have hmod : W.length % 2 = 0 := by
    omega
  exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hmod)

end Graph
