import Randy1153.DeBoorPinkus.NodeSpace

/-! Full free-node optimization target. Canonical theory is credited to randyxian08. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- Global minimality among every injectively enumerated family of the same size. -/
def IsOptimal {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∀ other : NodeFamily n, lebesgueOn nodes (-1) 1 ≤ lebesgueOn other (-1) 1

/-- All actual internal gap maxima agree, and both exterior endpoint values fit below them. -/
def EquioscillatingWithControlledTails {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  (∀ i j : Fin (d + 1), gapHeight nodes.sorted i = gapHeight nodes.sorted j) ∧
    lebesgueFunction nodes (-1) ≤ gapHeight nodes.sorted (0 : Fin (d + 1)) ∧
    lebesgueFunction nodes 1 ≤ gapHeight nodes.sorted (0 : Fin (d + 1))

end
end Jsp936
