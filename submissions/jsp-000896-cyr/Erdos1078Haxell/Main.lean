import Erdos1078Haxell.Degree

/-! # Erdős Problem 1078 -/

namespace Erdos1078

open Finset

/-- The cross-part complement of `G`: two vertices are adjacent exactly when they lie in
different classes and are **not** adjacent in `G`. An independent transversal of this graph is
a transversal clique of `G`. -/
private def crossCompl {V ι : Type*} (G : SimpleGraph V) (part : V → ι) : SimpleGraph V where
  Adj v w := part v ≠ part w ∧ ¬ G.Adj v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hg => h.2 hg.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance crossCompl_decidableRel {V ι : Type*} [DecidableEq ι] (G : SimpleGraph V)
    [DecidableRel G.Adj] (part : V → ι) : DecidableRel (crossCompl G part).Adj :=
  fun v w => inferInstanceAs (Decidable (part v ≠ part w ∧ ¬ G.Adj v w))

private lemma crossCompl_adj {V ι : Type*} (G : SimpleGraph V) (part : V → ι) (v w : V) :
    (crossCompl G part).Adj v w ↔ part v ≠ part w ∧ ¬ G.Adj v w := Iff.rfl

/-- Erdős Problem 1078 (Bollobás–Erdős–Szemerédi conjecture, Haxell's theorem): an `r`-partite
graph with `n ≥ 1` vertices in each part (parts indexed by `Fin r`, no edges inside a part) and
minimum degree at least `(r − 3/2) n` contains a `K_r`. -/
theorem erdos_1078 (r n : ℕ) (hn : 1 ≤ n) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin r)
    (hsize : ∀ i : Fin r, (univ.filter (fun v => part v = i)).card = n)
    (hcross : ∀ v w, G.Adj v w → part v ≠ part w)
    (hdeg : ∀ v, ((r : ℝ) - 3 / 2) * n ≤ G.degree v) :
    ∃ S : Finset V, G.IsNClique r S := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨∅, SimpleGraph.isNClique_empty.2 rfl⟩
  -- Work in the cross-part complement `H`.
  set H : SimpleGraph V := crossCompl G part with hH
  have hcardV : Fintype.card V = r * n := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := part) (t := univ) (fun x _ => mem_univ _)]
    simp [hsize]
  -- The vertices outside the class of `v` number `(r − 1) n`.
  have hcompl : ∀ v : V, (univ.filter (fun w => part w ≠ part v)).card + n = r * n := by
    intro v
    have h1 : (univ.filter (fun w => part w ≠ part v))
        = univ \ univ.filter (fun w => part w = part v) := by
      rw [← Finset.filter_not]
    have hn' : n ≤ r * n := by
      calc n = 1 * n := (one_mul n).symm
        _ ≤ r * n := Nat.mul_le_mul_right n hr
    rw [h1, card_sdiff_of_subset (filter_subset _ _), hsize (part v), Finset.card_univ, hcardV]
    omega
  have hsub : ∀ v : V, G.neighborFinset v ⊆ univ.filter (fun w => part w ≠ part v) := by
    intro v w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact mem_filter.2 ⟨mem_univ _, fun h => hcross v w hw h.symm⟩
  have hnb : ∀ v : V, H.neighborFinset v
      = (univ.filter (fun w => part w ≠ part v)) \ G.neighborFinset v := by
    intro v
    ext w
    simp only [hH, SimpleGraph.mem_neighborFinset, crossCompl_adj, mem_sdiff, mem_filter,
      mem_univ, true_and, ne_eq]
    exact and_congr_left' ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  -- The minimum degree hypothesis bounds the maximum degree of `H` by `n / 2`.
  have hdeg2 : ∀ v : V, 2 * H.degree v ≤ n := by
    intro v
    have hle : G.degree v ≤ (univ.filter (fun w => part w ≠ part v)).card :=
      card_le_card (hsub v)
    have hHd : H.degree v + G.degree v = (univ.filter (fun w => part w ≠ part v)).card := by
      have h1 : H.degree v = (H.neighborFinset v).card := rfl
      have h2 : G.degree v = (G.neighborFinset v).card := rfl
      have h3 : H.degree v = (univ.filter (fun w => part w ≠ part v)).card - G.degree v := by
        rw [h1, h2, hnb v, card_sdiff_of_subset (hsub v)]
      omega
    have hreal : 2 * (r * n) ≤ 2 * G.degree v + 3 * n := by
      have h := hdeg v
      have h2 : (2 * (r * n) : ℝ) ≤ 2 * (G.degree v : ℝ) + 3 * n := by nlinarith [h]
      exact_mod_cast h2
    have hc := hcompl v
    obtain ⟨T, hT⟩ : ∃ T, r * n = T := ⟨_, rfl⟩
    rw [hT] at hc hreal
    omega
  have hne : ∀ i : Fin r, ∃ v, part v = i := by
    intro i
    have hpos : 0 < (univ.filter (fun v => part v = i)).card := by rw [hsize i]; omega
    obtain ⟨v, hv⟩ := card_pos.1 hpos
    exact ⟨v, (mem_filter.1 hv).2⟩
  have hHd2 : ∀ v : V, H.degree v ≤ n / 2 := by
    intro v
    have := hdeg2 v
    omega
  have hcls : ∀ i : Fin r, 2 * (n / 2) ≤ (univ.filter (fun v => part v = i)).card := by
    intro i
    rw [hsize i]
    omega
  -- Haxell's theorem supplies an independent transversal of `H`, i.e. a transversal `K_r` of `G`.
  obtain ⟨M, hM⟩ : ∃ M : Finset V, IsIT H part M := haxell H part (n / 2) hHd2 hcls hne
  refine ⟨M, ?_⟩
  rw [SimpleGraph.isNClique_iff]
  obtain ⟨⟨hind, hinj⟩, hsurj⟩ := hM
  constructor
  · intro v hv w hw hvw
    have h1 : ¬ H.Adj v w := hind v hv w hw
    have h2 : part v ≠ part w := fun h => hvw (hinj hv hw h)
    rw [hH, crossCompl_adj, not_and] at h1
    exact not_not.1 (h1 h2)
  · have himg : M.image part = univ := by
      apply Finset.eq_univ_iff_forall.2
      intro i
      obtain ⟨v, hv, hvi⟩ := hsurj i
      exact mem_image.2 ⟨v, hv, hvi⟩
    have hci := Finset.card_image_of_injOn hinj
    rw [himg, Finset.card_univ, Fintype.card_fin] at hci
    exact hci.symm

/-- The closed form: no such graph is `K_r`-free. -/
theorem erdos_1078_closed :
    ¬ ∃ (r n : ℕ), 1 ≤ n ∧ ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj) (part : V → Fin r),
      (∀ i : Fin r, (univ.filter (fun v => part v = i)).card = n) ∧
      (∀ v w, G.Adj v w → part v ≠ part w) ∧
      (∀ v, ((r : ℝ) - 3 / 2) * n ≤ G.degree v) ∧ G.CliqueFree r := by
  rintro ⟨r, n, hn, V, _, _, G, _, part, hsize, hcross, hdeg, hfree⟩
  obtain ⟨S, hS⟩ := erdos_1078 r n hn G part hsize hcross hdeg
  exact hfree S hS

end Erdos1078
