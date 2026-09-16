import MerLeanExperiment.ArbitraryPalette

open PlanarListColoring
#check planar_bipartite_three_list_colorable
#print axioms PlanarListColoring.planar_bipartite_three_list_colorable
#print axioms Graph.IsDrawing.exists_euler_faceSystem
#print axioms Graph.IsDrawing.twoConnected_density
#print axioms Graph.IsDrawing.nonempty_density
#print axioms PlaneDrawing.hereditary_density
#print axioms three_list_colorable_of_density
#print PlanarListColoring.PlaneDrawing

example {V : Type} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v :=
  planar_bipartite_three_list_colorable G hplanar hbipartite L hL

#check planar_bipartite_three_list_colorable_palette
#print axioms PlanarListColoring.planar_bipartite_three_list_colorable_palette
example {V : Type} {C : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset C) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v :=
  planar_bipartite_three_list_colorable_palette G hplanar hbipartite L hL
