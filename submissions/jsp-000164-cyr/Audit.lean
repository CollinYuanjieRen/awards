import Proof

open Erdos167

#print axioms Erdos167.not_exists_coverNumber_gt
#print axioms Erdos167.coverNumber_le_three_mul_packingNumber
#print axioms Erdos167.exists_cover_of_packingNumber_le
#print axioms Erdos167.coverNumber_le_card
#print axioms Erdos167.exists_isCover_card_eq
#print axioms Erdos167.card_le_packingNumber

example : ∀ n : ℕ, ¬ ∃ G : SimpleGraph (Fin n), 3 * packingNumber G < coverNumber G :=
  Erdos167.not_exists_coverNumber_gt
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    coverNumber G ≤ 3 * packingNumber G := by
  intro V _ _ G; exact Erdos167.coverNumber_le_three_mul_packingNumber G
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    packingNumber G ≤ k →
    ∃ D : Finset (Sym2 V), D.card ≤ 3 * k ∧ (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3 := by
  intro V _ _ G k hk; exact Erdos167.exists_cover_of_packingNumber_le G k hk
example : ∀ {V : Type} (G : SimpleGraph V) (D : Finset (Sym2 V)), IsCover G D →
    coverNumber G ≤ D.card := by
  intro V G D h; exact Erdos167.coverNumber_le_card G D h
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = coverNumber G := by
  intro V _ _ G; exact Erdos167.exists_isCover_card_eq G
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (F : Finset (Finset V)),
    IsPacking G F → F.card ≤ packingNumber G := by
  intro V _ _ G F h; exact Erdos167.card_le_packingNumber G F h

#print Erdos167.triangles
#print Erdos167.edgesOf
#print Erdos167.IsPacking
#print Erdos167.packingNumber
#print Erdos167.IsCover
#print Erdos167.coverNumber
