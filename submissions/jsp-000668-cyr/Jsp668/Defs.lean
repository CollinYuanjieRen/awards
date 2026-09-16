import Mathlib

/-!
# Erdős problem #811 (JSP-000668): balanced edge-colourings and rainbow `K₄` — definitions

An edge-colouring of the complete graph on a finite vertex type `V` with six colours is
modelled as a function `c : V → V → Fin 6` that is symmetric (`IsSymm`); the value on the
diagonal is irrelevant.  Following erdosproblems.com/811, the colouring is *balanced* when every
vertex sees exactly `⌊|V| / 6⌋` edges of each colour.  A *rainbow `K₄`* is a set of four distinct
vertices whose six connecting edges receive six distinct colours.
-/

namespace Erdos811

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- symmetric colouring of the ordered pairs (the diagonal is irrelevant) -/
def IsSymm (c : V → V → Fin 6) : Prop := ∀ x y, c x y = c y x

/-- every vertex sees exactly `t` edges of each colour -/
def BalancedWith (c : V → V → Fin 6) (t : ℕ) : Prop :=
  ∀ v : V, ∀ col : Fin 6, (Finset.univ.filter (fun w => w ≠ v ∧ c v w = col)).card = t

/-- the problem's notion of a balanced colouring with `m = 6` colours:
every vertex sees exactly `⌊n / 6⌋` edges of each colour, `n = |V|` -/
def Balanced (c : V → V → Fin 6) : Prop := BalancedWith c (Fintype.card V / 6)

/-- `a, b, d, e` are four distinct vertices whose six connecting edges get six distinct colours -/
def IsRainbowK4 (c : V → V → Fin 6) (a b d e : V) : Prop :=
  a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
    [c a b, c a d, c a e, c b d, c b e, c d e].Nodup

/-- the colouring contains a rainbow copy of `K₄` -/
def HasRainbowK4 (c : V → V → Fin 6) : Prop := ∃ a b d e, IsRainbowK4 c a b d e

end Erdos811
