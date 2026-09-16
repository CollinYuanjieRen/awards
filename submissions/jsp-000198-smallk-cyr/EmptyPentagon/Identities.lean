import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- Four-point cofactor identity for planar orientations. -/
theorem orient_four_identity (a b c d : Point) :
    orient b c d - orient a c d + orient a b d - orient a b c = 0 := by
  unfold orient
  ring

/-- Three-term Grassmann–Plücker identity for planar orientations. -/
theorem orient_plucker (a b c d e : Point) :
    orient a b c * orient a d e - orient a b d * orient a c e + orient a b e * orient a c d = 0 := by
  unfold orient
  ring

end Horton
