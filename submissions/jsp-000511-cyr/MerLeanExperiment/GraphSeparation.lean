import MerLeanExperiment.Vendor.Schoenflies.Graph.TwoConnected

open scoped Graph
open Set

namespace Graph

/-- A nonempty disconnected graph splits into two nonempty sets with no edge between them. -/
theorem exists_partition_of_not_connected
    {α β : Type*} (G : Graph α β) (hne : V(G).Nonempty) (hc : ¬ G.Connected) :
    ∃ A B : Set α, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = V(G) ∧
      ∀ (e : β) (x y : α), G.IsLink e x y →
        (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
  obtain ⟨a, ha⟩ := hne
  have hfail : ¬ ∀ x ∈ V(G), G.Reaches a x := by
    intro hall
    exact hc (Connected.of_hub ha hall)
  push Not at hfail
  obtain ⟨b, hb, hab⟩ := hfail
  let A : Set α := {x | G.Reaches a x}
  let B : Set α := V(G) \ A
  refine ⟨A, B, ⟨a, Reaches.refl ha⟩, ⟨b, hb, hab⟩, ?_, ?_, ?_⟩
  · exact disjoint_sdiff_right
  · ext x
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact Reaches.right_mem hx
      · exact hx
    · intro hx
      by_cases hax : G.Reaches a x
      · exact Or.inl hax
      · exact Or.inr ⟨hx, hax⟩
  · intro e x y hxy
    by_cases hx : G.Reaches a x
    · exact Or.inl ⟨hx, Reaches.trans hx (Reaches.of_isLink hxy)⟩
    · refine Or.inr ⟨⟨hxy.left_mem, hx⟩, hxy.right_mem, ?_⟩
      intro hy
      exact hx (Reaches.trans hy (Reaches.of_isLink hxy.symm))

end Graph
