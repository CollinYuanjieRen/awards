import Jsp668.Defs

/-!
# Erdős problem #811 (JSP-000668): the 13-vertex base colouring

This file transcribes Figure 1(a) of Clemen–Wagner, *Balanced edge-colorings avoiding rainbow
cliques of size four*, Electron. J. Combin. 30(3) (2023) #P3.17: a symmetric 6-colouring of the
edges of `K₁₃` in which every vertex sees each colour exactly twice and no four vertices span a
rainbow `K₄`.  All three properties are closed decidable statements over `Fin 13` and are checked
by kernel reduction (`decide +kernel`), so the proofs rely on no evaluation outside the kernel.
-/

namespace Erdos811

/-- Figure 1(a) of Clemen–Wagner (rows; colours 1–6, diagonal 0) -/
def baseTable : List (List ℕ) :=
  [[0, 2, 5, 4, 1, 3, 3, 6, 4, 2, 6, 5, 1],
   [2, 0, 3, 6, 5, 6, 4, 1, 3, 1, 4, 5, 2],
   [5, 3, 0, 5, 4, 2, 6, 3, 1, 6, 2, 1, 4],
   [4, 6, 5, 0, 2, 4, 5, 2, 1, 3, 3, 1, 6],
   [1, 5, 4, 2, 0, 3, 1, 6, 2, 5, 4, 6, 3],
   [3, 6, 2, 4, 3, 0, 1, 4, 5, 6, 5, 2, 1],
   [3, 4, 6, 5, 1, 1, 0, 2, 5, 4, 2, 6, 3],
   [6, 1, 3, 2, 6, 4, 2, 0, 3, 5, 1, 4, 5],
   [4, 3, 1, 1, 2, 5, 5, 3, 0, 4, 6, 2, 6],
   [2, 1, 6, 3, 5, 6, 4, 5, 4, 0, 1, 3, 2],
   [6, 4, 2, 3, 4, 5, 2, 1, 6, 1, 0, 3, 5],
   [5, 5, 1, 1, 6, 2, 6, 4, 2, 3, 3, 0, 4],
   [1, 2, 4, 6, 3, 1, 3, 5, 6, 2, 5, 4, 0]]

/-- the colouring: entry minus one, as an element of `Fin 6` (diagonal entries map to `0`) -/
def base (i j : Fin 13) : Fin 6 :=
  ⟨((baseTable.getD i []).getD j 1 - 1) % 6, Nat.mod_lt _ (by norm_num)⟩

theorem base_symm : IsSymm base := by
  show ∀ x y, base x y = base y x
  decide +kernel

theorem base_balanced : BalancedWith base 2 := by
  show ∀ v : Fin 13, ∀ col : Fin 6,
    (Finset.univ.filter (fun w => w ≠ v ∧ base v w = col)).card = 2
  decide +kernel

theorem base_noRainbow : ¬ HasRainbowK4 base := by
  have h : ∀ a b d e : Fin 13, ¬ (a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
      [base a b, base a d, base a e, base b d, base b e, base d e].Nodup) := by
    decide +kernel
  rintro ⟨a, b, d, e, hr⟩
  exact h a b d e hr

end Erdos811

#print axioms Erdos811.base_symm
#print axioms Erdos811.base_balanced
#print axioms Erdos811.base_noRainbow
