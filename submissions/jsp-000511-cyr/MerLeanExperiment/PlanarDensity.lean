import MerLeanExperiment.TwoConnectedDensity
import MerLeanExperiment.SmallGraphDensity
import MerLeanExperiment.SeparatorCounts

open scoped Graph
open Set Schoenflies

namespace Graph

theorem IsDrawing.nonempty_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (hne : V(G).Nonempty)
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard + 2 ≤ 2 * V(G).ncard := by
  induction hn : V(G).ncard using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hthree : G.HasThreeVertices
      · by_cases htwo : G.IsTwoConnected
        · have hdense := h.twoConnected_density htwo c hcolor
          omega
        · obtain ⟨A, B, S, hA, hB, hAB, hAS, hBS, hcover, hS, hlink⟩ :=
            exists_small_separator G hthree htwo
          obtain ⟨hGA, hGB, hAne, hBne, hAlt, hBlt, hvertices, hedges⟩ :=
            small_separator_counts hA hB hAB hAS hBS hcover hS hlink
          let GA := G.induce (A ∪ S)
          let GB := G.induce (B ∪ S)
          let _ : GA.Finite := Graph.Finite.of_le hGA
          let _ : GB.Finite := Graph.Finite.of_le hGB
          let _ : GA.Simple := Graph.Simple.anti hGA
          let _ : GB.Simple := Graph.Simple.anti hGB
          have hcolorA : ∀ (e : β) (x y : Plane), GA.IsLink e x y → c x ≠ c y :=
            fun e x y hxy ↦ hcolor e x y (hxy.mono hGA)
          have hcolorB : ∀ (e : β) (x y : Plane), GB.IsLink e x y → c x ≠ c y :=
            fun e x y hxy ↦ hcolor e x y (hxy.mono hGB)
          have hAlt' : (A ∪ S).ncard < n := by simpa [← hn] using hAlt
          have hBlt' : (B ∪ S).ncard < n := by simpa [← hn] using hBlt
          have hdenseA : E(GA).ncard + 2 ≤ 2 * (A ∪ S).ncard := by
            simpa [GA] using ih (A ∪ S).ncard hAlt' (h.mono hGA) hAne hcolorA
          have hdenseB : E(GB).ncard + 2 ≤ 2 * (B ∪ S).ncard := by
            simpa [GB] using ih (B ∪ S).ncard hBlt' (h.mono hGB) hBne hcolorB
          change E(GA).ncard + E(GB).ncard = E(G).ncard at hedges
          omega
      · simpa [← hn] using small_graph_density hne hthree

theorem IsDrawing.bipartite_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard ≤ 2 * V(G).ncard := by
  by_cases hne : V(G).Nonempty
  · have hdense := h.nonempty_density hne c hcolor
    omega
  · have hE : E(G) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨e, he⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact hne ⟨x, hxy.left_mem⟩
    rw [hE]
    simp

end Graph
