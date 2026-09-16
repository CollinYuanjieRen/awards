import MerLeanExperiment.Vendor.Schoenflies.FaceCyclesLand

open scoped Graph
open Set Schoenflies

namespace Graph

universe u
variable {β : Type u}

/-- A named actual face and an edge list obtained by permuting one of its simple boundaries. -/
def IsBoundaryList (G : Graph Plane β) (drawing : β → ℝ → Plane)
    (U : Set Plane) (W : List β) : Prop :=
  ∃ (z : Plane) (e : β) (a b : Plane) (D : List β),
    z ∈ exterior G drawing ∧ U = face G drawing z ∧
    IsFaceCycle G drawing z e a b D ∧ W.Perm (e :: D)

/-- A finite enumeration of all actual faces with simple boundary edge lists.
This is internal output of ear induction, not a hypothesis defining planarity. -/
structure FaceSystem (G : Graph Plane β) (drawing : β → ℝ → Plane) where
  /-- Each pair contains an actual face and its boundary edge list. -/
  boundaries : Finset (Set Plane × List β)
  /-- Every recorded boundary is a simple cycle of this graph. -/
  valid : ∀ q ∈ boundaries, IsBoundaryList G drawing q.1 q.2
  /-- No actual face is recorded twice. -/
  unique : Set.InjOn Prod.fst (↑boundaries : Set (Set Plane × List β))
  /-- Every component of the graph's complement is recorded. -/
  exhaustive : ∀ z ∈ exterior G drawing, ∃ q ∈ boundaries, q.1 = face G drawing z

/-- The number of faces in the finite enumeration. -/
def FaceSystem.faceCount {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem G drawing) : ℕ := M.boundaries.card

/-- Total original-edge boundary length; geometric segment counts play no role. -/
def FaceSystem.boundaryLength {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem G drawing) : ℕ := ∑ q ∈ M.boundaries, q.2.length

end Graph
