import Erdos210Ordinary.Basic

/-!
# Erdős Problem 210 — configuration combinatorics

Elementary facts about `ordinaryPairs`, `orderZero` and the open cell `W`:

* membership characterisations for `ordinaryPairs` and `orderZero`;
* Lemma 1: `|P \ orderZero P| ≤ 2 * |ordinaryPairs P|`;
* the cell `W P p` contains `p`, is convex, is open along every direction, and misses every
  ordinary line;
* Lemma 2: from a non-collinear `P` and two distinct points `p q ∈ P` one obtains a connecting
  line through `q` missing `p`;
* every connecting line through a point of order zero carries a third point of `P`.

-/

namespace Erdos210

/-! ### A uniform version of `sameSide_small` -/

/-- The "open along a direction" property, uniformly over a finite family of oriented lines. -/
private theorem sameSide_small_finset (p w e : ℝ × ℝ) :
    ∀ S : Finset ((ℝ × ℝ) × (ℝ × ℝ)), (∀ ab ∈ S, SameSide ab.1 ab.2 p w) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ ab ∈ S, SameSide ab.1 ab.2 p (w + t • e) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_pos, by simp⟩
  | @insert x S _ ih =>
      intro hall
      obtain ⟨δ₁, hδ₁, h₁⟩ := ih fun ab hab => hall ab (Finset.mem_insert_of_mem hab)
      obtain ⟨δ₂, hδ₂, h₂⟩ := sameSide_small (hall x (Finset.mem_insert_self x S)) e
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht ab hab => ?_⟩
      rcases Finset.mem_insert.1 hab with rfl | hab
      · exact h₂ t (lt_of_lt_of_le ht (min_le_right _ _))
      · exact h₁ t (lt_of_lt_of_le ht (min_le_left _ _)) ab hab

/-! ### Ordinary pairs -/

theorem mem_ordinaryPairs {P : Finset (ℝ × ℝ)} {e : Finset (ℝ × ℝ)} :
    e ∈ ordinaryPairs P ↔ e ⊆ P ∧ e.card = 2 ∧
      ∀ a ∈ e, ∀ b ∈ e, a ≠ b → ∀ c ∈ P, OnLine a b c → c ∈ e := by
  classical
  rw [ordinaryPairs, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

private theorem mem_pair_iff {a b x : ℝ × ℝ} :
    x ∈ ({a, b} : Finset (ℝ × ℝ)) ↔ x = a ∨ x = b := by
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem pair_mem_ordinaryPairs {P : Finset (ℝ × ℝ)} {a b : ℝ × ℝ} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a ≠ b) (h : ∀ c ∈ P, OnLine a b c → c = a ∨ c = b) :
    ({a, b} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P := by
  rw [mem_ordinaryPairs]
  refine ⟨?_, Finset.card_pair hab, ?_⟩
  · intro x hx
    rcases mem_pair_iff.1 hx with rfl | rfl
    · exact ha
    · exact hb
  · intro u hu v hv huv c hc hline
    have hres : c = a ∨ c = b := by
      rcases mem_pair_iff.1 hu with rfl | rfl <;> rcases mem_pair_iff.1 hv with rfl | rfl
      · exact absurd rfl huv
      · exact h c hc hline
      · exact h c hc (onLine_comm.2 hline)
      · exact absurd rfl huv
    exact mem_pair_iff.2 hres

theorem exists_pair_of_mem_ordinaryPairs {P : Finset (ℝ × ℝ)} {e : Finset (ℝ × ℝ)}
    (he : e ∈ ordinaryPairs P) : ∃ a b, a ≠ b ∧ a ∈ P ∧ b ∈ P ∧ e = {a, b} := by
  rw [mem_ordinaryPairs] at he
  obtain ⟨hsub, hcard, -⟩ := he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
  exact ⟨a, b, hab, hsub (mem_pair_iff.2 (Or.inl rfl)), hsub (mem_pair_iff.2 (Or.inr rfl)), rfl⟩

/-! ### Points of order zero -/

theorem mem_orderZero {P : Finset (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ orderZero P ↔ p ∈ P ∧ ∀ e ∈ ordinaryPairs P, p ∉ e := by
  classical
  rw [orderZero, Finset.mem_filter]

/-- Lemma 1. -/
theorem card_sdiff_orderZero_le (P : Finset (ℝ × ℝ)) :
    (P \ orderZero P).card ≤ 2 * (ordinaryPairs P).card := by
  classical
  have hsub : P \ orderZero P ⊆ (ordinaryPairs P).biUnion id := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxP, hxZ⟩ := hx
    have hex : ∃ e ∈ ordinaryPairs P, x ∈ e := by
      by_contra hc
      exact hxZ (mem_orderZero.2 ⟨hxP, fun e he hxe => hc ⟨e, he, hxe⟩⟩)
    obtain ⟨e, he, hxe⟩ := hex
    exact Finset.mem_biUnion.2 ⟨e, he, hxe⟩
  calc (P \ orderZero P).card ≤ ((ordinaryPairs P).biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ ordinaryPairs P, (id e).card := Finset.card_biUnion_le
    _ = ∑ _e ∈ ordinaryPairs P, 2 :=
        Finset.sum_congr rfl fun e he => (mem_ordinaryPairs.1 he).2.1
    _ = 2 * (ordinaryPairs P).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `p ∈ orderZero P` and `p ∈ P` on a connecting line `a b` ⇒ that line has a third point. -/
theorem exists_third_of_orderZero {P : Finset (ℝ × ℝ)} {p a : ℝ × ℝ} (hp : p ∈ orderZero P)
    (ha : a ∈ P) (hpa : p ≠ a) : ∃ c ∈ P, OnLine p a c ∧ c ≠ p ∧ c ≠ a := by
  by_contra hcon
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  have hpair : ({p, a} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P := by
    refine pair_mem_ordinaryPairs hpP ha hpa fun c hc hline => ?_
    by_cases hcp : c = p
    · exact Or.inl hcp
    by_cases hca : c = a
    · exact Or.inr hca
    · exact absurd ⟨c, hc, hline, hcp, hca⟩ hcon
  exact hpe _ hpair (mem_pair_iff.2 (Or.inl rfl))

/-! ### The open cell `W` -/

private theorem mem_W_iff {P : Finset (ℝ × ℝ)} {p z : ℝ × ℝ} :
    z ∈ W P p ↔ ∀ e ∈ ordinaryPairs P, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → SameSide a b p z := Iff.rfl

theorem mem_W_self {P : Finset (ℝ × ℝ)} {p : ℝ × ℝ} (hp : p ∈ orderZero P) : p ∈ W P p := by
  obtain ⟨hpP, hpe⟩ := mem_orderZero.1 hp
  rw [mem_W_iff]
  intro e he a ha b hb hab
  have hne : D a b p ≠ 0 := fun h =>
    hpe e he ((mem_ordinaryPairs.1 he).2.2 a ha b hb hab p hpP h)
  exact mul_self_pos.2 hne

theorem W_segment {P : Finset (ℝ × ℝ)} {p z w : ℝ × ℝ} (hz : z ∈ W P p) (hw : w ∈ W P p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : z + t • (w - z) ∈ W P p := by
  rw [mem_W_iff] at hz hw ⊢
  intro e he a ha b hb hab
  exact sameSide_segment (hz e he a ha b hb hab) (hw e he a ha b hb hab) ht0 ht1

theorem W_small {P : Finset (ℝ × ℝ)} {p w : ℝ × ℝ} (hw : w ∈ W P p) (e : ℝ × ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → w + t • e ∈ W P p := by
  classical
  rw [mem_W_iff] at hw
  have hmemS : ∀ ab : (ℝ × ℝ) × (ℝ × ℝ),
      ab ∈ ((ordinaryPairs P).biUnion fun s => s ×ˢ s).filter (fun ab => ab.1 ≠ ab.2) ↔
        (∃ s ∈ ordinaryPairs P, ab.1 ∈ s ∧ ab.2 ∈ s) ∧ ab.1 ≠ ab.2 := by
    intro ab
    rw [Finset.mem_filter, Finset.mem_biUnion]
    simp only [Finset.mem_product]
  have hS : ∀ ab ∈ ((ordinaryPairs P).biUnion fun s => s ×ˢ s).filter (fun ab => ab.1 ≠ ab.2),
      SameSide ab.1 ab.2 p w := by
    intro ab hab
    obtain ⟨⟨s, hs, h1, h2⟩, hne⟩ := (hmemS ab).1 hab
    exact hw s hs ab.1 h1 ab.2 h2 hne
  obtain ⟨δ, hδ, h⟩ := sameSide_small_finset p w e _ hS
  refine ⟨δ, hδ, fun t ht => ?_⟩
  rw [mem_W_iff]
  intro s hs a ha b hb hab
  exact h t ht (a, b) ((hmemS (a, b)).2 ⟨⟨s, hs, ha, hb⟩, hab⟩)

theorem not_mem_W_of_onLine {P : Finset (ℝ × ℝ)} {p x a b : ℝ × ℝ}
    (he : ({a, b} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P) (hab : a ≠ b) (hx : OnLine a b x) :
    x ∉ W P p := by
  intro hmem
  rw [mem_W_iff] at hmem
  have hpos := hmem _ he a (mem_pair_iff.2 (Or.inl rfl)) b (mem_pair_iff.2 (Or.inr rfl)) hab
  rw [SameSide, show D a b x = 0 from hx, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-! ### Lemma 2 -/

-- The hypothesis `hp : p ∈ P` is part of the frozen statement but is not needed by the proof.
set_option linter.unusedVariables false in
/-- Lemma 2. -/
theorem exists_conn_missing {P : Finset (ℝ × ℝ)} (hP : NotCollinear P) {p q : ℝ × ℝ}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    ∃ c ∈ P, ∃ d ∈ P, c ≠ d ∧ OnLine c d q ∧ ¬ OnLine c d p := by
  have hoff : ∃ r ∈ P, ¬ OnLine p q r := by
    by_contra hcontra
    have hcon : ∀ r ∈ P, OnLine p q r := fun r hr => by
      by_contra h
      exact hcontra ⟨r, hr, h⟩
    obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hP
    by_cases hab : a = b
    · subst hab
      exact habc (D_self_left a c)
    · exact habc ((onLine_iff_of_onLine hpq (hcon a ha) (hcon b hb) hab c).2 (hcon c hc))
  obtain ⟨r, hr, hpqr⟩ := hoff
  have hqr : q ≠ r := by
    rintro rfl
    exact hpqr (D_right _ _)
  refine ⟨q, hq, r, hr, hqr, D_left q r, fun hcontra => ?_⟩
  exact hpqr ((onLine_iff_of_onLine hqr hcontra (D_left q r) hpq r).2 (D_right q r))

end Erdos210
