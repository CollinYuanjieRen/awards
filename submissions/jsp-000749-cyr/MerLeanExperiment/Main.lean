import MerLeanExperiment.Defs

/-!
# Erdős problem #901 — Erdős's lower bound `2^{n−1} ≤ m(n)` and `m(2) = 3`

The problem page records "Erdős proved `2^n ≪ m(n) ≪ n² 2^n`" and "it is known that `m(2) = 3`".
This file proves the lower bound in its standard explicit form and the value `m(2) = 3`: the
counting core (T3, every `n`-uniform hypergraph with fewer than `2^{n−1}` edges is `2`-colourable),
finiteness of `m(n)` (T4, so the infimum is honest), the bound `2^{n−1} ≤ m(n)` (T1, the audited
root), and `m(2) = 3` from the triangle (T5) and the two-edge lemma (T6).

Not claimed here: Erdős's upper bound `m(n) ≪ n² 2^n` (the scope of upstream PR #392 by another
contributor), the values `m(3) = 7` and `m(4) = 23`, the improvements of the lower bound by Beck,
Radhakrishnan–Srinivasan and Pluhár, and the conjectured order `n 2^n`.
-/

namespace Erdos901

/-! ### Auxiliary counting lemmas for Erdős's argument -/

/-- The colourings that are constant equal to `b` on `e`. -/
private def badOn {N : ℕ} (e : Finset (Fin N)) (b : Bool) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun c : Fin N → Bool => ∀ u ∈ e, c u = b)

/-- The colourings that are monochromatic on `e`. -/
private def badAll {N : ℕ} (e : Finset (Fin N)) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun c : Fin N → Bool => ∀ u ∈ e, ∀ v ∈ e, c u = c v)

private lemma mem_badOn {N : ℕ} {e : Finset (Fin N)} {b : Bool} {c : Fin N → Bool} :
    c ∈ badOn e b ↔ ∀ u ∈ e, c u = b := by
  simp [badOn]

private lemma mem_badAll {N : ℕ} {e : Finset (Fin N)} {c : Fin N → Bool} :
    c ∈ badAll e ↔ ∀ u ∈ e, ∀ v ∈ e, c u = c v := by
  simp [badAll]

private lemma card_badOn_le {N : ℕ} (e : Finset (Fin N)) (b : Bool) :
    (badOn e b).card ≤ 2 ^ (N - e.card) := by
  classical
  have hcard : (Finset.univ : Finset ({v : Fin N // v ∉ e} → Bool)).card = 2 ^ (N - e.card) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype_compl (p := fun v : Fin N => v ∈ e)]
    simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun c => fun v : {v : Fin N // v ∉ e} => c v.1)
    (fun c _ => Finset.mem_univ _) ?_
  intro c₁ h₁ c₂ h₂ heq
  simp only [Finset.mem_coe, mem_badOn] at h₁ h₂
  funext v
  by_cases hv : v ∈ e
  · rw [h₁ v hv, h₂ v hv]
  · exact congrFun heq ⟨v, hv⟩

private lemma card_badAll_le {N : ℕ} (e : Finset (Fin N)) (he : e.Nonempty) :
    (badAll e).card ≤ 2 * 2 ^ (N - e.card) := by
  classical
  obtain ⟨u₀, hu₀⟩ := he
  have hsub : badAll e ⊆ badOn e true ∪ badOn e false := by
    intro c hc
    rw [mem_badAll] at hc
    rw [Finset.mem_union, mem_badOn, mem_badOn]
    cases hb : c u₀ with
    | true => exact Or.inl fun u hu => (hc u hu u₀ hu₀).trans hb
    | false => exact Or.inr fun u hu => (hc u hu u₀ hu₀).trans hb
  calc (badAll e).card ≤ (badOn e true ∪ badOn e false).card := Finset.card_le_card hsub
    _ ≤ (badOn e true).card + (badOn e false).card := Finset.card_union_le _ _
    _ ≤ 2 ^ (N - e.card) + 2 ^ (N - e.card) :=
        Nat.add_le_add (card_badOn_le e true) (card_badOn_le e false)
    _ = 2 * 2 ^ (N - e.card) := by ring

/-- (T3) Erdős's counting argument: an `n`-uniform hypergraph with fewer than `2^{n−1}` edges is
`2`-colourable, because each edge is monochromatic under only `2^{N−n+1}` of the `2^N` colourings. -/
theorem twoColorable_of_card_lt {N : ℕ} (n : ℕ) (E : Finset (Finset (Fin N))) (hU : IsUniform n E) (hE : E.card < 2 ^ (n - 1)) : TwoColorable E := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hEne
  · exact ⟨fun _ => true, by simp⟩
  obtain ⟨e₀, he₀⟩ := hEne
  have hpos : 0 < E.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [Nat.zero_sub, pow_zero, Nat.lt_one_iff] at hE
    omega
  have hnN : n ≤ N := by
    have h1 : e₀.card ≤ Fintype.card (Fin N) := Finset.card_le_univ e₀
    rw [hU e₀ he₀, Fintype.card_fin] at h1
    exact h1
  have hbadcard : ∀ e ∈ E, (badAll e).card ≤ 2 * 2 ^ (N - n) := by
    intro e he
    have hc : e.card = n := hU e he
    have hne : e.Nonempty := by
      rw [← Finset.card_pos, hc]; omega
    have h := card_badAll_le e hne
    rwa [hc] at h
  have hunion : (E.biUnion badAll).card ≤ E.card * (2 * 2 ^ (N - n)) :=
    Finset.card_biUnion_le_card_mul E badAll _ hbadcard
  have hp : 0 < 2 * 2 ^ (N - n) := by positivity
  have h2 : E.card * (2 * 2 ^ (N - n)) < 2 ^ (n - 1) * (2 * 2 ^ (N - n)) :=
    Nat.mul_lt_mul_of_lt_of_le hE (le_refl _) hp
  have h3 : 2 ^ (n - 1) * (2 * 2 ^ (N - n)) = 2 ^ N := by
    have hexp : (n - 1) + (1 + (N - n)) = N := by omega
    calc 2 ^ (n - 1) * (2 * 2 ^ (N - n)) = 2 ^ (n - 1) * (2 ^ 1 * 2 ^ (N - n)) := by norm_num
      _ = 2 ^ ((n - 1) + (1 + (N - n))) := by rw [← pow_add, ← pow_add]
      _ = 2 ^ N := by rw [hexp]
  have hlt : (E.biUnion badAll).card < (Finset.univ : Finset (Fin N → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, fun e he => ?_⟩
  have hce : c ∉ badAll e := fun h => hc (Finset.mem_biUnion.mpr ⟨e, he, h⟩)
  by_contra hcon
  refine hce (mem_badAll.mpr fun u hu v hv => ?_)
  by_contra hne
  exact hcon ⟨u, hu, v, hv, hne⟩

/-- (T4) `m(n)` is finite: the `n`-subsets of a `(2n − 1)`-element set form an `n`-uniform hypergraph
without Property B (for `n = 0`, the single empty edge). -/
theorem exists_not_twoColorable (n : ℕ) : ∃ (N : ℕ) (E : Finset (Finset (Fin N))), IsUniform n E ∧ ¬ TwoColorable E := by
  classical
  match n with
  | 0 =>
    refine ⟨0, {∅}, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      simp
    · rintro ⟨c, hc⟩
      obtain ⟨u, hu, -⟩ := hc ∅ (Finset.mem_singleton_self _)
      exact absurd hu (Finset.notMem_empty u)
  | (k + 1) =>
    refine ⟨2 * k + 1, Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin (2 * k + 1))), ?_, ?_⟩
    · intro e he
      exact (Finset.mem_powersetCard.mp he).2
    · rintro ⟨c, hc⟩
      have key : ∀ b : Bool,
          k + 1 ≤ (Finset.univ.filter (fun v : Fin (2 * k + 1) => c v = b)).card → False := by
        intro b hb
        obtain ⟨e, hsub, hcard⟩ := Finset.exists_subset_card_eq hb
        obtain ⟨u, hu, v, hv, huv⟩ :=
          hc e (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hcard⟩)
        have h1 := Finset.mem_filter.mp (hsub hu)
        have h2 := Finset.mem_filter.mp (hsub hv)
        exact huv (h1.2.trans h2.2.symm)
      have hne : (Finset.univ.filter (fun v : Fin (2 * k + 1) => ¬ (c v = true)))
          = Finset.univ.filter (fun v : Fin (2 * k + 1) => c v = false) := by
        ext v; simp
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (2 * k + 1)))) (p := fun v => c v = true)
      rw [hne, Finset.card_univ, Fintype.card_fin] at hsum
      rcases (by omega :
          k + 1 ≤ (Finset.univ.filter (fun v : Fin (2 * k + 1) => c v = true)).card ∨
          k + 1 ≤ (Finset.univ.filter (fun v : Fin (2 * k + 1) => c v = false)).card) with h | h
      · exact key true h
      · exact key false h

/-- (T1) Audited root: Erdős's lower bound `2^{n−1} ≤ m(n)`. -/
theorem two_pow_le_m (n : ℕ) : 2 ^ (n - 1) ≤ m n := by
  apply le_csInf
  · obtain ⟨N, E, hU, hnc⟩ := exists_not_twoColorable n
    exact ⟨E.card, N, E, hU, hnc, rfl⟩
  · rintro k ⟨N, E, hU, hnc, rfl⟩
    by_contra hcon
    exact hnc (twoColorable_of_card_lt n E hU (by omega))

/-- (T5) The triangle is a `2`-uniform hypergraph with three edges and no Property B. -/
theorem triangle_not_twoColorable : IsUniform 2 ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) ∧ ¬ TwoColorable ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) := by
  constructor
  · unfold IsUniform
    decide
  · unfold TwoColorable
    decide

/-- Given two pairs `{a,b}` and `{x,y}` of distinct vertices, some `2`-colouring separates both. -/
private lemma exists_color {N : ℕ} (a b x y : Fin N) (hab : a ≠ b) (hxy : x ≠ y) :
    ∃ c : Fin N → Bool, c a ≠ c b ∧ c x ≠ c y := by
  classical
  have hba : b ≠ a := Ne.symm hab
  have hyx : y ≠ x := Ne.symm hxy
  by_cases h1 : b = x
  · refine ⟨fun v => decide (v = a ∨ v = y), ?_, ?_⟩ <;>
      simp only [ne_eq, decide_eq_decide] <;> subst h1 <;> tauto
  · by_cases h2 : y = a
    · refine ⟨fun v => decide (v = a ∨ v = y), ?_, ?_⟩ <;>
        simp only [ne_eq, decide_eq_decide] <;> subst h2 <;> tauto
    · refine ⟨fun v => decide (v = a ∨ v = x), ?_, ?_⟩ <;>
        simp only [ne_eq, decide_eq_decide] <;> tauto

/-- (T6) Every `2`-uniform hypergraph with at most two edges is `2`-colourable. -/
theorem twoColorable_of_card_le_two {N : ℕ} (E : Finset (Finset (Fin N))) (hU : IsUniform 2 E) (hE : E.card ≤ 2) : TwoColorable E := by
  classical
  have hcases : E.card = 0 ∨ E.card = 1 ∨ E.card = 2 := by omega
  rcases hcases with h | h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    exact ⟨fun _ => true, by simp⟩
  · rw [Finset.card_eq_one] at h
    obtain ⟨e, rfl⟩ := h
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hU e (Finset.mem_singleton_self _))
    obtain ⟨c, hc, -⟩ := exists_color a b a b hab hab
    refine ⟨c, fun f hf => ?_⟩
    rw [Finset.mem_singleton] at hf
    subst hf
    exact ⟨a, by simp, b, by simp, hc⟩
  · rw [Finset.card_eq_two] at h
    obtain ⟨e₁, e₂, -, rfl⟩ := h
    obtain ⟨a, b, hab, he₁⟩ :=
      Finset.card_eq_two.mp (hU e₁ (Finset.mem_insert_self _ _))
    obtain ⟨x, y, hxy, he₂⟩ :=
      Finset.card_eq_two.mp (hU e₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    obtain ⟨c, hc₁, hc₂⟩ := exists_color a b x y hab hxy
    refine ⟨c, fun f hf => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact ⟨a, by rw [he₁]; simp, b, by rw [he₁]; simp, hc₁⟩
    · exact ⟨x, by rw [he₂]; simp, y, by rw [he₂]; simp, hc₂⟩

/-- (T2) The page's value `m(2) = 3`. -/
theorem m_two : m 2 = 3 := by
  refine le_antisymm ?_ ?_
  · refine Nat.sInf_le ⟨3, {{0, 1}, {1, 2}, {0, 2}}, triangle_not_twoColorable.1,
      triangle_not_twoColorable.2, ?_⟩
    decide
  · apply le_csInf
    · obtain ⟨N, E, hU, hnc⟩ := exists_not_twoColorable 2
      exact ⟨E.card, N, E, hU, hnc, rfl⟩
    · rintro k ⟨N, E, hU, hnc, rfl⟩
      by_contra hcon
      exact hnc (twoColorable_of_card_le_two E hU (by omega))

end Erdos901
