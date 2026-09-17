import Erdos574Cycles.Free

/-! Vertex and edge counts of the doubled incidence graph, and the lower bound on `exOddEven`. -/

namespace Erdos574

open SimpleGraph Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false in
theorem card_vtx : Fintype.card (Vtx F) = 3 * Fintype.card F ^ 3 := by
  simp [Vtx, Fintype.card_sum, Fintype.card_prod]
  ring

/-! ### The neighbours of a vertex of `doubled F` -/

/-- The unique line with first coordinate `x` that is incident to the point `p`. -/
private def lineOf (p : F × F × F) (x : F) : F × F × F :=
  (x, p.2.1 + x * p.1, p.2.2 + (p.2.1 + x * p.1) * p.1)

/-- The unique point with first coordinate `a` that is incident to the line `l`. -/
private def pointOf (l : F × F × F) (a : F) : F × F × F :=
  (a, l.2.1 - l.1 * a, l.2.2 - l.2.1 * a)

omit [Fintype F] [DecidableEq F] in
private lemma incid_iff_exists_lineOf (p l : F × F × F) :
    Incid F p l ↔ ∃ x, lineOf F p x = l := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨l.1, ?_⟩
    obtain ⟨x, y, z⟩ := l
    dsimp only at h1 h2
    subst h1
    subst h2
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨rfl, rfl⟩

omit [Fintype F] [DecidableEq F] in
private lemma incid_iff_exists_pointOf (p l : F × F × F) :
    Incid F p l ↔ ∃ a, pointOf F l a = p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨p.1, ?_⟩
    obtain ⟨a, b, c⟩ := p
    dsimp only at h1 h2 ⊢
    simp only [pointOf, h1, h2]
    ring_nf
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp only [pointOf] <;> ring

omit [Fintype F] [DecidableEq F] in
private lemma lineOf_injective (p : F × F × F) : Function.Injective (lineOf F p) := by
  intro x y h
  simpa [lineOf] using congrArg Prod.fst h

omit [Fintype F] [DecidableEq F] in
private lemma pointOf_injective (l : F × F × F) : Function.Injective (pointOf F l) := by
  intro x y h
  simpa [pointOf] using congrArg Prod.fst h

private lemma neighborFinset_inl (p : F × F × F) :
    (doubled F).neighborFinset (Sum.inl p)
      = (univ.image (fun x : F => (Sum.inr (Sum.inl (lineOf F p x)) : Vtx F)))
        ∪ (univ.image (fun x : F => (Sum.inr (Sum.inr (lineOf F p x)) : Vtx F))) := by
  ext v
  rw [mem_neighborFinset]
  rcases v with p' | l | l
  · show dAdj F (Sum.inl p) (Sum.inl p') ↔ _
    simp [dAdj]
  · show Incid F p l ↔ _
    simp [incid_iff_exists_lineOf]
  · show Incid F p l ↔ _
    simp [incid_iff_exists_lineOf]

private lemma neighborFinset_inr_inl (l : F × F × F) :
    (doubled F).neighborFinset (Sum.inr (Sum.inl l))
      = univ.image (fun a : F => (Sum.inl (pointOf F l a) : Vtx F)) := by
  ext v
  rw [mem_neighborFinset]
  rcases v with p | l' | l'
  · show Incid F p l ↔ _
    simp [incid_iff_exists_pointOf]
  · show dAdj F (Sum.inr (Sum.inl l)) (Sum.inr (Sum.inl l')) ↔ _
    simp [dAdj]
  · show dAdj F (Sum.inr (Sum.inl l)) (Sum.inr (Sum.inr l')) ↔ _
    simp [dAdj]

private lemma neighborFinset_inr_inr (l : F × F × F) :
    (doubled F).neighborFinset (Sum.inr (Sum.inr l))
      = univ.image (fun a : F => (Sum.inl (pointOf F l a) : Vtx F)) := by
  ext v
  rw [mem_neighborFinset]
  rcases v with p | l' | l'
  · show Incid F p l ↔ _
    simp [incid_iff_exists_pointOf]
  · show dAdj F (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inl l')) ↔ _
    simp [dAdj]
  · show dAdj F (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inr l')) ↔ _
    simp [dAdj]

private lemma degree_inl (p : F × F × F) :
    (doubled F).degree (Sum.inl p) = 2 * Fintype.card F := by
  rw [degree, neighborFinset_inl, card_union_of_disjoint, card_image_of_injective,
    card_image_of_injective, card_univ]
  · ring
  · exact fun x y h => lineOf_injective F p (by simpa using h)
  · exact fun x y h => lineOf_injective F p (by simpa using h)
  · simp [Finset.disjoint_left]

private lemma degree_inr_inl (l : F × F × F) :
    (doubled F).degree (Sum.inr (Sum.inl l)) = Fintype.card F := by
  rw [degree, neighborFinset_inr_inl, card_image_of_injective, card_univ]
  exact fun x y h => pointOf_injective F l (by simpa using h)

private lemma degree_inr_inr (l : F × F × F) :
    (doubled F).degree (Sum.inr (Sum.inr l)) = Fintype.card F := by
  rw [degree, neighborFinset_inr_inr, card_image_of_injective, card_univ]
  exact fun x y h => pointOf_injective F l (by simpa using h)

theorem card_edgeFinset_doubled : #(doubled F).edgeFinset = 2 * Fintype.card F ^ 4 := by
  have hd : ∑ v : Vtx F, (doubled F).degree v = 4 * Fintype.card F ^ 4 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [degree_inl, degree_inr_inl, degree_inr_inr, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Fintype.card_prod]
    ring
  have h2 : 2 * #(doubled F).edgeFinset = 2 * (2 * Fintype.card F ^ 4) := by
    rw [← (doubled F).sum_degrees_eq_twice_card_edges, hd]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

open scoped Classical in
/-- A graph on `n` vertices containing neither `C_{2k−1}` nor `C_{2k}` has at most
`exOddEven n k` edges. -/
theorem le_exOddEven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h₁ : (cycleGraph (2 * k - 1)).Free G) (h₂ : (cycleGraph (2 * k)).Free G) :
    #G.edgeFinset ≤ exOddEven (Fintype.card V) k := by
  let e := Fintype.equivFin V
  have h' : G.map e ∈ univ.filter (fun G' : SimpleGraph (Fin (Fintype.card V)) =>
      (cycleGraph (2 * k - 1)).Free G' ∧ (cycleGraph (2 * k)).Free G') := by
    rw [mem_filter]
    exact ⟨mem_univ _, (free_congr_right (Iso.map e G)).1 h₁,
      (free_congr_right (Iso.map e G)).1 h₂⟩
  rw [exOddEven, Iso.card_edgeFinset_eq (Iso.map e G)]
  convert! @le_sup _ _ _ _
    {G' : SimpleGraph (Fin (Fintype.card V)) |
      (cycleGraph (2 * k - 1)).Free G' ∧ (cycleGraph (2 * k)).Free G'}
    (#·.edgeFinset) _ h'

/-- For every prime `q`, `ex(3q³; {C₅, C₆}) ≥ 2q⁴`. -/
theorem exOddEven_lower (q : ℕ) [Fact q.Prime] : 2 * q ^ 4 ≤ exOddEven (3 * q ^ 3) 3 := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h5 : (cycleGraph (2 * 3 - 1)).Free (doubled (ZMod q)) := by
    show (cycleGraph 5).Free (doubled (ZMod q))
    exact doubled_free_five (ZMod q)
  have h6 : (cycleGraph (2 * 3)).Free (doubled (ZMod q)) := by
    show (cycleGraph 6).Free (doubled (ZMod q))
    exact doubled_free_six (ZMod q)
  have h := le_exOddEven (doubled (ZMod q)) 3 h5 h6
  rwa [card_vtx, card_edgeFinset_doubled, ZMod.card] at h

end Erdos574
