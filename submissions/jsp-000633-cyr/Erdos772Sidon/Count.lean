import Erdos772Sidon.Definitions

/-! Counting additive quadruples in a set with bounded representation function. -/

namespace Erdos772

private lemma mem_badTuples_iff {S : Finset ℕ} {t : (ℕ × ℕ) × (ℕ × ℕ)} :
    t ∈ badTuples S ↔ ((t.1.1 ∈ S ∧ t.1.2 ∈ S) ∧ (t.2.1 ∈ S ∧ t.2.2 ∈ S)) ∧
      (t.1.1 + t.1.2 = t.2.1 + t.2.2 ∧
        ¬ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1))) := by
  simp only [badTuples, Finset.mem_filter, Finset.mem_product]

theorem card_quad_le (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)).card
      ≤ k * A.card ^ 2 := by
  set Q := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2) with hQ
  have hmem : ∀ t : (ℕ × ℕ) × (ℕ × ℕ), t ∈ Q →
      (t.1 ∈ A ×ˢ A ∧ t.2 ∈ A ×ˢ A) ∧ t.1.1 + t.1.2 = t.2.1 + t.2.2 := by
    intro t ht
    rw [hQ, Finset.mem_filter, Finset.mem_product] at ht
    exact ht
  have hcard : Q.card = ∑ p ∈ A ×ˢ A, (Q.filter (fun t => t.1 = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun t ht => (hmem t ht).1.1)
  have hfib : ∀ p ∈ A ×ˢ A, (Q.filter (fun t => t.1 = p)).card ≤ k := by
    intro p _
    have key : (Q.filter (fun t => t.1 = p)).card
        ≤ ((A ×ˢ A).filter (fun q => q.1 + q.2 = p.1 + p.2)).card := by
      refine Finset.card_le_card_of_injOn (fun t => t.2) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht
        obtain ⟨htQ, htp⟩ := ht
        obtain ⟨⟨-, h2⟩, h3⟩ := hmem t htQ
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨h2, ?_⟩
        show t.2.1 + t.2.2 = p.1 + p.2
        rw [← htp]
        omega
      · intro s hs t ht hst
        rw [Finset.mem_coe, Finset.mem_filter] at hs ht
        exact Prod.ext (hs.2.trans ht.2.symm) hst
    exact key.trans (hA (p.1 + p.2))
  calc Q.card = ∑ p ∈ A ×ˢ A, (Q.filter (fun t => t.1 = p)).card := hcard
    _ ≤ (A ×ˢ A).card • k := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = k * A.card ^ 2 := by rw [Finset.card_product, smul_eq_mul]; ring

theorem card_badTuples_le (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) :
    (badTuples A).card ≤ k * A.card ^ 2 := by
  refine le_trans (Finset.card_le_card ?_) (card_quad_le k A hA)
  intro t ht
  rw [mem_badTuples_iff] at ht
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product]
  exact ⟨⟨ht.1.1, ht.1.2⟩, ht.2.1⟩

/-- The auxiliary set of solutions of `a + b = 2 * c` with `a, b, c ∈ A`. -/
private def T3 (A : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((A ×ˢ A) ×ˢ A).filter (fun q => q.1.1 + q.1.2 = 2 * q.2)

private lemma mem_T3_iff {A : Finset ℕ} {q : (ℕ × ℕ) × ℕ} :
    q ∈ T3 A ↔ ((q.1.1 ∈ A ∧ q.1.2 ∈ A) ∧ q.2 ∈ A) ∧ q.1.1 + q.1.2 = 2 * q.2 := by
  simp only [T3, Finset.mem_filter, Finset.mem_product]

private lemma card_T3_le (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) :
    (T3 A).card ≤ k * A.card := by
  have hcard : (T3 A).card = ∑ c ∈ A, ((T3 A).filter (fun q => q.2 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun q hq => (mem_T3_iff.1 hq).1.2)
  have hfib : ∀ c ∈ A, ((T3 A).filter (fun q => q.2 = c)).card ≤ k := by
    intro c _
    have key : ((T3 A).filter (fun q => q.2 = c)).card
        ≤ ((A ×ˢ A).filter (fun p => p.1 + p.2 = 2 * c)).card := by
      refine Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_
      · intro q hq
        rw [Finset.mem_coe, Finset.mem_filter] at hq
        obtain ⟨hqT, hqc⟩ := hq
        obtain ⟨⟨h1, -⟩, h3⟩ := mem_T3_iff.1 hqT
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        refine ⟨h1, ?_⟩
        show q.1.1 + q.1.2 = 2 * c
        rw [← hqc]
        omega
      · intro s hs t ht hst
        rw [Finset.mem_coe, Finset.mem_filter] at hs ht
        exact Prod.ext hst (hs.2.trans ht.2.symm)
    exact key.trans (hA (2 * c))
  calc (T3 A).card = ∑ c ∈ A, ((T3 A).filter (fun q => q.2 = c)).card := hcard
    _ ≤ A.card • k := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = k * A.card := by rw [smul_eq_mul]; ring

theorem card_badTuples_repeat_le (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) :
    ((badTuples A).filter HasRepeat).card ≤ 2 * (k * A.card) := by
  have hsplit : (badTuples A).filter HasRepeat
      = (badTuples A).filter (fun t => t.1.1 = t.1.2) ∪
        (badTuples A).filter (fun t => t.2.1 = t.2.2) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro t _
    simp [HasRepeat]
  have h1 : ((badTuples A).filter (fun t => t.1.1 = t.1.2)).card ≤ (T3 A).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.2, t.1.1)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter] at ht
      obtain ⟨htb, hrep⟩ := ht
      rw [mem_badTuples_iff] at htb
      rw [Finset.mem_coe, mem_T3_iff]
      refine ⟨⟨htb.1.2, htb.1.1.1⟩, ?_⟩
      have := htb.2.1
      simp only
      omega
    · intro s hs t ht hst
      rw [Finset.mem_coe, Finset.mem_filter] at hs ht
      simp only [Prod.mk.injEq] at hst
      obtain ⟨hs2, h11⟩ := hst
      exact Prod.ext (Prod.ext h11 (by rw [← hs.2, h11, ht.2])) hs2
  have h2 : ((badTuples A).filter (fun t => t.2.1 = t.2.2)).card ≤ (T3 A).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter] at ht
      obtain ⟨htb, hrep⟩ := ht
      rw [mem_badTuples_iff] at htb
      rw [Finset.mem_coe, mem_T3_iff]
      refine ⟨⟨htb.1.1, htb.1.2.1⟩, ?_⟩
      have := htb.2.1
      simp only
      omega
    · intro s hs t ht hst
      rw [Finset.mem_coe, Finset.mem_filter] at hs ht
      simp only [Prod.mk.injEq] at hst
      obtain ⟨hs1, h21⟩ := hst
      exact Prod.ext hs1 (Prod.ext h21 (by rw [← hs.2, h21, ht.2]))
  have hT3 := card_T3_le k A hA
  calc ((badTuples A).filter HasRepeat).card
      ≤ ((badTuples A).filter (fun t => t.1.1 = t.1.2)).card +
        ((badTuples A).filter (fun t => t.2.1 = t.2.2)).card := by
        rw [hsplit]; exact Finset.card_union_le _ _
    _ ≤ 2 * (k * A.card) := by omega

theorem card_elems_of_repeat (t : (ℕ × ℕ) × (ℕ × ℕ)) (S : Finset ℕ) (ht : t ∈ badTuples S)
    (hr : HasRepeat t) : (elems t).card = 3 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := t
  rw [mem_badTuples_iff] at ht
  obtain ⟨-, heq, hnt⟩ := ht
  simp only at heq hnt
  rw [not_or] at hnt
  obtain ⟨hnt1, hnt2⟩ := hnt
  rw [not_and_or] at hnt1 hnt2
  rcases hr with hab | hcd
  · simp only at hab
    subst hab
    have hac : a ≠ c := by rintro rfl; omega
    have had : a ≠ d := by rintro rfl; omega
    have hcd : c ≠ d := by
      rintro rfl
      have : a = c := by omega
      subst this
      tauto
    rw [Finset.card_eq_three]
    exact ⟨a, c, d, hac, had, hcd, by simp [elems]⟩
  · simp only at hcd
    subst hcd
    have hac : a ≠ c := by rintro rfl; omega
    have hbc : b ≠ c := by rintro rfl; omega
    have hab : a ≠ b := by
      rintro rfl
      have : a = c := by omega
      subst this
      tauto
    rw [Finset.card_eq_three]
    exact ⟨a, b, c, hab, hac, hbc, by simp [elems]⟩

theorem card_elems_of_not_repeat (t : (ℕ × ℕ) × (ℕ × ℕ)) (S : Finset ℕ) (ht : t ∈ badTuples S)
    (hr : ¬ HasRepeat t) : (elems t).card = 4 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := t
  rw [mem_badTuples_iff] at ht
  obtain ⟨-, heq, hnt⟩ := ht
  simp only at heq hnt
  rw [HasRepeat, not_or] at hr
  obtain ⟨hab, hcd⟩ := hr
  simp only at hab hcd
  rw [not_or, not_and_or, not_and_or] at hnt
  obtain ⟨hnt1, hnt2⟩ := hnt
  have hac : a ≠ c := by
    rintro rfl
    have : b = d := by omega
    tauto
  have had : a ≠ d := by
    rintro rfl
    have : b = c := by omega
    tauto
  have hbd : b ≠ d := by
    rintro rfl
    have : a = c := by omega
    tauto
  have hbc : b ≠ c := by
    rintro rfl
    have : a = d := by omega
    tauto
  rw [Finset.card_eq_four]
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, by simp [elems]⟩

theorem badTuples_eq_filter (A S : Finset ℕ) (hS : S ⊆ A) :
    badTuples S = (badTuples A).filter (fun t => elems t ⊆ S) := by
  ext t
  rw [Finset.mem_filter, mem_badTuples_iff, mem_badTuples_iff]
  simp only [elems, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact ⟨⟨⟨⟨hS h1, hS h2⟩, hS h3, hS h4⟩, h5⟩, h1, h2, h3, h4⟩
  · rintro ⟨⟨-, h5⟩, h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩

theorem isSidon_iff (S : Finset ℕ) : IsSidon S ↔ badTuples S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h t htm
    rw [mem_badTuples_iff] at htm
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, heq, hnt⟩ := htm
    exact hnt (h _ ha _ hb _ hc _ hd heq)
  · intro h a ha b hb c hc d hd heq
    by_contra hnt
    exact h ((a, b), (c, d)) (mem_badTuples_iff.2 ⟨⟨⟨ha, hb⟩, hc, hd⟩, heq, hnt⟩)

end Erdos772
