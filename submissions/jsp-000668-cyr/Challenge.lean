import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions, targets with `sorry`; not
imported by the build) for JSP-000668 / Erdős #811, the `K₄` component (Clemen–Wagner 2023). -/

namespace Challenge811

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

/-- Clemen–Wagner (2023), Theorem 2 -/
theorem exists_balanced_no_rainbowK4 (k : ℕ) :
    ∃ c : Fin (13 ^ k) → Fin (13 ^ k) → Fin 6, IsSymm c ∧ Balanced c ∧ ¬ HasRainbowK4 c := by
  sorry

/-- `K₄` does not have the property asked about on erdosproblems.com/811 (with `m = e(K₄) = 6`) -/
theorem K4_not_forced :
    ¬ ∃ N : ℕ, ∀ n, N ≤ n → n % 6 = 1 →
      ∀ c : Fin n → Fin n → Fin 6, IsSymm c → Balanced c → HasRainbowK4 c := by
  sorry

end Challenge811
