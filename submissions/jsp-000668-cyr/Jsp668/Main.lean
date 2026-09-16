import Jsp668.Base
import Jsp668.Lift

/-!
# Erdős problem #811 (JSP-000668): the tower of colourings

Iterating the Axenovich–Clemen product step (`Erdos811.lift`, `Jsp668/Lift.lean`) on the
thirteen-vertex colouring of Clemen–Wagner (`Erdos811.base`, `Jsp668/Base.lean`) produces, for
every `k`, a symmetric six-colouring of the complete graph on `13 ^ k` vertices which is balanced
and has no rainbow `K₄`.  This is Theorem 2 of

* Clemen, Wagner, *Balanced edge-colorings avoiding rainbow cliques of size four*,
  Electron. J. Combin. **30** (2023), no. 3, #P3.17.

Consequently `K₄` does not have the property asked about on erdosproblems.com/811 for
`m = e(K₄) = 6`: there are arbitrarily large `n ≡ 1 (mod 6)` carrying a balanced six-colouring of
`K_n` with no rainbow `K₄`.  (Everything else about #811 is open and is not claimed here.)
-/

namespace Erdos811

/-- the vertex type of the `k`-th colouring in the tower: `k` nested copies of `Fin 13` -/
@[reducible] def Tower : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin 13 × Tower k

instance instFintypeTower : (k : ℕ) → Fintype (Tower k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => haveI := instFintypeTower k; inferInstanceAs (Fintype (Fin 13 × Tower k))

instance instDecidableEqTower : (k : ℕ) → DecidableEq (Tower k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => haveI := instDecidableEqTower k; inferInstanceAs (DecidableEq (Fin 13 × Tower k))

/-- the `k`-th colouring of the tower: `k` iterated lifts of the base colouring -/
def towerColoring : (k : ℕ) → Tower k → Tower k → Fin 6
  | 0 => fun _ _ => 0
  | k + 1 => lift base (towerColoring k)

theorem card_tower (k : ℕ) : Fintype.card (Tower k) = 13 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      show Fintype.card (Fin 13 × Tower k) = 13 ^ (k + 1)
      rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, Nat.mul_comm]

theorem thirteen_pow_mod_six (k : ℕ) : 13 ^ k % 6 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

theorem tower_symm (k : ℕ) : IsSymm (towerColoring k) := by
  induction k with
  | zero => intro x y; rfl
  | succ k ih => exact lift_symm base_symm ih

theorem tower_balancedWith (k : ℕ) : BalancedWith (towerColoring k) ((13 ^ k - 1) / 6) := by
  induction k with
  | zero =>
      intro v col
      simp [Subsingleton.elim _ v]
  | succ k ih =>
      have h := lift_balancedWith (c₁ := base) (c₂ := towerColoring k) base_balanced ih
      rw [card_tower k] at h
      have harith : 2 * 13 ^ k + (13 ^ k - 1) / 6 = (13 ^ (k + 1) - 1) / 6 := by
        have h1 : (13 : ℕ) ^ (k + 1) = 13 * 13 ^ k := by rw [pow_succ, Nat.mul_comm]
        have h2 := thirteen_pow_mod_six k
        omega
      rw [harith] at h
      exact h

theorem tower_noRainbow (k : ℕ) : ¬ HasRainbowK4 (towerColoring k) := by
  induction k with
  | zero => rintro ⟨a, b, _, _, hab, -⟩; exact hab (Subsingleton.elim a b)
  | succ k ih => exact lift_noRainbow base_symm base_noRainbow ih

/-- Clemen–Wagner (2023), Theorem 2, for every `k` (the case `k = 0` is trivial) -/
theorem exists_balanced_no_rainbowK4 (k : ℕ) :
    ∃ c : Fin (13 ^ k) → Fin (13 ^ k) → Fin 6, IsSymm c ∧ Balanced c ∧ ¬ HasRainbowK4 c := by
  classical
  let e : Tower k ≃ Fin (13 ^ k) := (Fintype.equivFin (Tower k)).trans (finCongr (card_tower k))
  refine ⟨transport e (towerColoring k), transport_symm e (tower_symm k), ?_,
    transport_noRainbow e (tower_noRainbow k)⟩
  show BalancedWith (transport e (towerColoring k)) (Fintype.card (Fin (13 ^ k)) / 6)
  have hdiv : Fintype.card (Fin (13 ^ k)) / 6 = (13 ^ k - 1) / 6 := by
    have h2 := thirteen_pow_mod_six k
    rw [Fintype.card_fin]
    generalize (13 : ℕ) ^ k = m at h2 ⊢
    omega
  rw [hdiv]
  exact transport_balancedWith e (tower_balancedWith k)

/-- `K₄` does not have the property asked about on erdosproblems.com/811 (`m = e(K₄) = 6`) -/
theorem K4_not_forced :
    ¬ ∃ N : ℕ, ∀ n, N ≤ n → n % 6 = 1 →
      ∀ c : Fin n → Fin n → Fin 6, IsSymm c → Balanced c → HasRainbowK4 c := by
  rintro ⟨N, hN⟩
  obtain ⟨c, hsymm, hbal, hrain⟩ := exists_balanced_no_rainbowK4 N
  exact hrain (hN (13 ^ N) (Nat.lt_pow_self (by norm_num)).le (thirteen_pow_mod_six N) c hsymm hbal)

end Erdos811

#print axioms Erdos811.card_tower
#print axioms Erdos811.thirteen_pow_mod_six
#print axioms Erdos811.tower_symm
#print axioms Erdos811.tower_balancedWith
#print axioms Erdos811.tower_noRainbow
#print axioms Erdos811.exists_balanced_no_rainbowK4
#print axioms Erdos811.K4_not_forced
