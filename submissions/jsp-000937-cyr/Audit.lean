import Jsp937
open Randy1153 Jsp937

#print axioms Jsp937.maximizer_iff_equioscillating_and_large_tails
#print axioms Jsp937.exists_upsilon_maximizer
#print axioms Jsp937.singleton_upsilon_and_maximal
#print axioms Jsp937.pair_upsilon_and_maximal

example (d : ℕ) (nodes : OrderedNodes (d + 2)) :
    IsUpsilonMaximizer nodes ↔ EquioscillatingWithLargeTails nodes :=
  maximizer_iff_equioscillating_and_large_tails d nodes

example (d : ℕ) : ∃ nodes : OrderedNodes (d + 2), IsUpsilonMaximizer nodes :=
  exists_upsilon_maximizer d

example (nodes : OrderedNodes 1) : upsilon nodes = 1 ∧ IsUpsilonMaximizer nodes :=
  singleton_upsilon_and_maximal nodes

example (nodes : OrderedNodes 2) : upsilon nodes = 1 ∧ IsUpsilonMaximizer nodes :=
  pair_upsilon_and_maximal nodes

-- Expand both sides to the actual raw finite-product, augmented-gap formulas.
example (d : ℕ) (nodes : OrderedNodes (d + 2)) :
    (∀ other : OrderedNodes (d + 2), rawUpsilon other.point ≤ rawUpsilon nodes.point) ↔
      (∀ i j : Fin (d + 1),
        rawLocalPeak nodes.point i.castSucc.succ = rawLocalPeak nodes.point j.castSucc.succ) ∧
      rawLocalPeak nodes.point (0 : Fin (d + 1)).castSucc.succ ≤
        rawLebesgueFunction nodes.point (-1) ∧
      rawLocalPeak nodes.point (0 : Fin (d + 1)).castSucc.succ ≤
        rawLebesgueFunction nodes.point 1 := by
  simpa only [IsUpsilonMaximizer, EquioscillatingWithLargeTails, upsilon_eq_raw,
    ← localPeak_succ_eq_gapHeight, localPeak_eq_raw, lebesgueFunction_eq_raw] using
    maximizer_iff_equioscillating_and_large_tails d nodes

-- Exhibit a genuine singleton model and its maximizing property.
example : ∃ nodes : OrderedNodes 1, upsilon nodes = 1 ∧ IsUpsilonMaximizer nodes := by
  let nodes : OrderedNodes 1 := {
    point := fun _ => 0
    injective := fun _ _ _ => Subsingleton.elim _ _
    mem_Icc := fun _ => by norm_num
    strictMono := fun i j hij => by have : i = j := Subsingleton.elim _ _; subst j; exact (lt_irrefl _ hij).elim
  }
  exact ⟨nodes, singleton_upsilon_and_maximal nodes⟩
