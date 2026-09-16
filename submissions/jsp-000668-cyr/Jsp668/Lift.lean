import Jsp668.Defs

/-!
# Erdős problem #811 (JSP-000668): the Axenovich–Clemen product step

This file contains the "lifting" construction of Clemen–Wagner, *Balanced edge-colorings avoiding
rainbow cliques of size four*, Lemma 3 (= Axenovich–Clemen, Lemma 2.2):  given a colouring `c₁` of
`K_{|A|}` and a colouring `c₂` of `K_{|V|}`, the blow-up colouring `lift c₁ c₂` of `K_{|A| · |V|}`
colours an edge of `A × V` by `c₁` on the first coordinates when those differ, and by `c₂` on the
second coordinates when the first coordinates agree.  Symmetry, balancedness and the absence of a
rainbow `K₄` all lift.  A transport lemma along an equivalence of vertex types is included so that
the construction can be moved onto `Fin n`.

## A correction to the stated contract

`lift_noRainbow` needs `IsSymm c₁` as a hypothesis; without it the statement is **false**.  See the
private theorem `lift_noRainbow_needs_symm` at the end of this file for an explicit
(kernel-checked) counterexample: with `A := Fin 3` and `V := Fin 2` neither `c₁` nor `c₂` can have a
rainbow `K₄` at all (they have fewer than four vertices), yet a non-symmetric `c₁` produces one in
the lift, because the four vertices `(0,0), (1,0), (2,0), (0,1)` then see the six distinct colours
`c₁ 0 1, c₁ 0 2, c₂ 0 1, c₁ 1 2, c₁ 1 0, c₁ 2 0`.  The extra hypothesis is harmless downstream: the
lift is only ever applied with `c₁ = base`, and `base_symm` is available.
-/

-- The contract fixes the section variables below; several statements do not need all of them.
set_option linter.unusedSectionVars false

namespace Erdos811

variable {A V W : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- colour `{x, y}` by the base colouring of the first coordinates when they differ, else by `c₂` -/
def lift (c₁ : A → A → Fin 6) (c₂ : V → V → Fin 6) : A × V → A × V → Fin 6 :=
  fun x y => if x.1 = y.1 then c₂ x.2 y.2 else c₁ x.1 y.1

theorem lift_symm {c₁ : A → A → Fin 6} {c₂ : V → V → Fin 6} (h₁ : IsSymm c₁) (h₂ : IsSymm c₂) :
    IsSymm (lift c₁ c₂) := by
  intro x y
  by_cases h : x.1 = y.1
  · simp [lift, h, h₂ x.2 y.2]
  · simp [lift, h, Ne.symm h, h₁ x.1 y.1]

theorem lift_balancedWith {c₁ : A → A → Fin 6} {c₂ : V → V → Fin 6} {t₁ t₂ : ℕ}
    (h₁ : BalancedWith c₁ t₁) (h₂ : BalancedWith c₂ t₂) :
    BalancedWith (lift c₁ c₂) (t₁ * Fintype.card V + t₂) := by
  rintro ⟨a, x⟩ col
  classical
  -- the neighbours of `(a, x)` in colour `col` split according to their first coordinate
  have key :
      (Finset.univ.filter fun w : A × V => w ≠ (a, x) ∧ lift c₁ c₂ (a, x) w = col)
        = ((Finset.univ.filter fun b : A => b ≠ a ∧ c₁ a b = col) ×ˢ (Finset.univ : Finset V))
          ∪ (({a} : Finset A) ×ˢ (Finset.univ.filter fun y : V => y ≠ x ∧ c₂ x y = col)) := by
    ext ⟨b, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, Finset.mem_singleton, lift, ne_eq, Prod.mk.injEq, not_and]
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb, Ne.symm hb]
  rw [key, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_univ, h₁ a col, h₂ x col, one_mul]
  refine Finset.disjoint_left.mpr ?_
  rintro ⟨b, y⟩ hb hb'
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_singleton] at hb hb'
  exact hb.1.2.1 hb'.1

/-- The product step for rainbow-`K₄`-freeness.  Note the extra hypothesis `IsSymm c₁`, which the
counterexample `lift_noRainbow_needs_symm` below shows to be necessary. -/
theorem lift_noRainbow {c₁ : A → A → Fin 6} {c₂ : V → V → Fin 6} (hs : IsSymm c₁)
    (h₁ : ¬ HasRainbowK4 c₁) (h₂ : ¬ HasRainbowK4 c₂) : ¬ HasRainbowK4 (lift c₁ c₂) := by
  rintro ⟨⟨a₁, x₁⟩, ⟨a₂, x₂⟩, ⟨a₃, x₃⟩, ⟨a₄, x₄⟩, hv12, hv13, hv14, hv23, hv24, hv34, hnd⟩
  by_cases e12 : a₁ = a₂
  · subst e12
    by_cases e13 : a₁ = a₃
    · subst e13
      by_cases e14 : a₁ = a₄
      · -- all four first coordinates agree: a rainbow `K₄` for `c₂`
        subst e14
        simp only [lift] at hnd
        exact h₂ ⟨x₁, x₂, x₃, x₄,
          fun hx => hv12 (by rw [hx]), fun hx => hv13 (by rw [hx]),
          fun hx => hv14 (by rw [hx]), fun hx => hv23 (by rw [hx]),
          fun hx => hv24 (by rw [hx]), fun hx => hv34 (by rw [hx]), hnd⟩
      · -- the edges `{1,4}` and `{2,4}` both have colour `c₁ a₁ a₄`
        simp only [lift, ite_eq_right e14] at hnd
        simp at hnd
    · -- the edges `{1,3}` and `{2,3}` both have colour `c₁ a₁ a₃`
      simp only [lift, ite_eq_right e13] at hnd
      simp at hnd
  · by_cases e13 : a₁ = a₃
    · -- the edges `{1,2}` and `{2,3}` both have colour `c₁ a₁ a₂`
      subst e13
      have e23 : ¬ a₂ = a₁ := fun hh => e12 hh.symm
      simp only [lift, ite_eq_right e12, ite_eq_right e23] at hnd
      rw [hs a₂ a₁] at hnd
      simp at hnd
    · by_cases e14 : a₁ = a₄
      · -- the edges `{1,2}` and `{2,4}` both have colour `c₁ a₁ a₂`
        subst e14
        have e24 : ¬ a₂ = a₁ := fun hh => e12 hh.symm
        simp only [lift, ite_eq_right e12, ite_eq_right e24] at hnd
        rw [hs a₂ a₁] at hnd
        simp at hnd
      · by_cases e23 : a₂ = a₃
        · -- the edges `{1,2}` and `{1,3}` both have colour `c₁ a₁ a₂`
          subst e23
          simp only [lift, ite_eq_right e12] at hnd
          simp at hnd
        · by_cases e24 : a₂ = a₄
          · -- the edges `{1,2}` and `{1,4}` both have colour `c₁ a₁ a₂`
            subst e24
            simp only [lift, ite_eq_right e12] at hnd
            simp at hnd
          · by_cases e34 : a₃ = a₄
            · -- the edges `{1,3}` and `{1,4}` both have colour `c₁ a₁ a₃`
              subst e34
              simp only [lift, ite_eq_right e13] at hnd
              simp at hnd
            · -- all four first coordinates differ: a rainbow `K₄` for `c₁`
              simp only [lift, ite_eq_right e12, ite_eq_right e13, ite_eq_right e14,
                ite_eq_right e23, ite_eq_right e24, ite_eq_right e34] at hnd
              exact h₁ ⟨a₁, a₂, a₃, a₄, e12, e13, e14, e23, e24, e34, hnd⟩

/-- transport along an equivalence of vertex types -/
def transport (e : V ≃ W) (c : V → V → Fin 6) : W → W → Fin 6 := fun x y => c (e.symm x) (e.symm y)

theorem transport_symm (e : V ≃ W) {c : V → V → Fin 6} (h : IsSymm c) : IsSymm (transport e c) :=
  fun x y => h (e.symm x) (e.symm y)

theorem transport_balancedWith (e : V ≃ W) {c : V → V → Fin 6} {t : ℕ} (h : BalancedWith c t) :
    BalancedWith (transport e c) t := by
  intro w col
  rw [← h (e.symm w) col]
  refine Finset.card_equiv e.symm ?_
  intro u
  rw [Finset.mem_filter_univ, Finset.mem_filter_univ]
  simp [transport]

theorem transport_noRainbow (e : V ≃ W) {c : V → V → Fin 6} (h : ¬ HasRainbowK4 c) :
    ¬ HasRainbowK4 (transport e c) := by
  rintro ⟨a, b, d, f, h1, h2, h3, h4, h5, h6, hnd⟩
  exact h ⟨e.symm a, e.symm b, e.symm d, e.symm f, e.symm.injective.ne h1,
    e.symm.injective.ne h2, e.symm.injective.ne h3, e.symm.injective.ne h4,
    e.symm.injective.ne h5, e.symm.injective.ne h6, hnd⟩

/-! ### Why `lift_noRainbow` needs `IsSymm c₁` -/

/-- a non-symmetric colouring of `K₃` (the diagonal and `c₁ 2 1` are irrelevant) -/
private def cexA : Fin 3 → Fin 3 → Fin 6 := ![![0, 0, 1], ![3, 0, 2], ![4, 0, 0]]

/-- a colouring of `K₂` -/
private def cexV : Fin 2 → Fin 2 → Fin 6 := ![![0, 5], ![5, 0]]

/-- Dropping `IsSymm c₁` from `lift_noRainbow` makes it false: both factors are rainbow-`K₄`-free
(they have fewer than four vertices), but the lift is not. -/
private theorem lift_noRainbow_needs_symm :
    ¬ HasRainbowK4 cexA ∧ ¬ HasRainbowK4 cexV ∧ HasRainbowK4 (lift cexA cexV) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b, d, e, h⟩
    revert h
    revert a b d e
    simp only [IsRainbowK4]
    decide
  · rintro ⟨a, b, d, e, h⟩
    revert h
    revert a b d e
    simp only [IsRainbowK4]
    decide
  · exact ⟨((0 : Fin 3), (0 : Fin 2)), ((1 : Fin 3), (0 : Fin 2)), ((2 : Fin 3), (0 : Fin 2)),
      ((0 : Fin 3), (1 : Fin 2)), by simp only [IsRainbowK4]; decide⟩

end Erdos811

#print axioms Erdos811.lift
#print axioms Erdos811.lift_symm
#print axioms Erdos811.lift_balancedWith
#print axioms Erdos811.lift_noRainbow
#print axioms Erdos811.transport
#print axioms Erdos811.transport_symm
#print axioms Erdos811.transport_balancedWith
#print axioms Erdos811.transport_noRainbow
