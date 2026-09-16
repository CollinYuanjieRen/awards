import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- Every set of exactly `n` points in general position contains an empty convex `k`-gon. -/
def ForcesEmptyKGon (k n : ℕ) : Prop :=
  ∀ S : Finset Point, S.card = n → GeneralPosition S →
    ∃ V : Finset Point, V.card = k ∧ EmptyConvexPolygon S V

end Horton
