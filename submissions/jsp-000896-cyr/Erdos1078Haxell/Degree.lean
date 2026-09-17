import Erdos1078Haxell.Augment

/-! Haxell's theorem in degree form: classes of size at least `2Δ` (and nonempty). -/

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

open Finset

set_option linter.unusedSectionVars false in
/-- If every vertex has degree at most `s / 2` (i.e. `2 · deg ≤ s`) and every class has at least
`s` vertices and is nonempty, then the non-domination hypothesis holds. -/
theorem nonDom_of_degree (s : ℕ) (hdeg : ∀ v, 2 * G.degree v ≤ s)
    (hcls : ∀ i : ι, s ≤ (univ.filter (fun v => part v = i)).card)
    (hne : ∀ i : ι, ∃ v, part v = i) : NonDom G part := by
  classical
  intro B hB D hD hcard
  set VB : Finset V := univ.filter (fun v => part v ∈ B) with hVBdef
  set Dom : Finset V := VB.filter (fun w => ∃ u ∈ D, G.Adj u w) with hDomdef
  -- The dominated set is covered by the neighbourhoods of `D`.
  have hsub : Dom ⊆ D.biUnion (fun u => G.neighborFinset u) := by
    intro w hw
    rw [hDomdef, mem_filter] at hw
    obtain ⟨-, u, hu, hadj⟩ := hw
    exact mem_biUnion.2 ⟨u, hu, by simpa [SimpleGraph.mem_neighborFinset] using hadj⟩
  have hDomcard : Dom.card ≤ ∑ u ∈ D, G.degree u := by
    calc Dom.card ≤ (D.biUnion (fun u => G.neighborFinset u)).card := card_le_card hsub
      _ ≤ ∑ u ∈ D, (G.neighborFinset u).card := card_biUnion_le
      _ = ∑ u ∈ D, G.degree u := by
          exact sum_congr rfl fun u _ => SimpleGraph.card_neighborFinset_eq_degree G u
  have hsum : 2 * ∑ u ∈ D, G.degree u ≤ D.card * s := by
    rw [Finset.mul_sum]
    calc ∑ u ∈ D, 2 * G.degree u ≤ ∑ _u ∈ D, s := sum_le_sum fun u _ => hdeg u
      _ = D.card * s := by simp [sum_const, smul_eq_mul]
  have hDom2 : 2 * Dom.card ≤ D.card * s :=
    le_trans (Nat.mul_le_mul_left 2 hDomcard) hsum
  -- The union of the classes in `B` has at least `|B| * s` vertices.
  have hVBcard : B.card * s ≤ VB.card := by
    have h1 : VB.card = ∑ i ∈ B, (VB.filter (fun v => part v = i)).card :=
      card_eq_sum_card_fiberwise (f := part) (s := VB) (t := B)
        (fun v hv => by
          have : v ∈ VB := hv
          rw [hVBdef, mem_filter] at this
          exact this.2)
    have h2 : ∀ i ∈ B, VB.filter (fun v => part v = i) = univ.filter (fun v => part v = i) := by
      intro i hi
      ext v
      rw [hVBdef]
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨h ▸ hi, h⟩
    rw [h1]
    calc B.card * s = ∑ _i ∈ B, s := by simp [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ B, (VB.filter (fun v => part v = i)).card :=
          sum_le_sum fun i hi => by rw [h2 i hi]; exact hcls i
  -- Hence the dominated set is a proper subset of that union.
  have hlt : Dom.card < VB.card := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      obtain ⟨i, hi⟩ := hB
      obtain ⟨v, hv⟩ := hne i
      have hvVB : v ∈ VB := by rw [hVBdef, mem_filter]; exact ⟨mem_univ v, hv ▸ hi⟩
      have hpos : 0 < VB.card := card_pos.2 ⟨v, hvVB⟩
      omega
    · obtain ⟨m, hm⟩ : ∃ m, B.card = m + 1 := by
        obtain ⟨i, hi⟩ := hB
        have : 0 < B.card := card_pos.2 ⟨i, hi⟩
        exact ⟨B.card - 1, by omega⟩
      have h3 : D.card * s ≤ 2 * (m * s) := by
        have h := Nat.mul_le_mul hcard (le_refl s)
        rw [hm] at h
        calc D.card * s ≤ 2 * (m + 1 - 1) * s := h
          _ = 2 * (m * s) := by rw [Nat.add_sub_cancel, Nat.mul_assoc]
      have h4 : m * s + s ≤ VB.card := by
        have h := hVBcard
        rw [hm, add_mul, one_mul] at h
        exact h
      linarith
  have hss : Dom ⊂ VB :=
    ssubset_of_subset_of_ne (hDomdef ▸ filter_subset _ _) (fun h => by
      rw [h] at hlt; exact lt_irrefl _ hlt)
  obtain ⟨w, hwVB, hwDom⟩ := exists_of_ssubset hss
  refine ⟨w, ?_, ?_⟩
  · have : w ∈ VB := hwVB
    rw [hVBdef, mem_filter] at this
    exact this.2
  · intro u hu hadj
    exact hwDom (by rw [hDomdef, mem_filter]; exact ⟨hwVB, u, hu, hadj⟩)

/-- Haxell's theorem: maximum degree at most `Δ` and all classes of size at least `2Δ` and
nonempty give an independent transversal. -/
theorem haxell (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hcls : ∀ i : ι, 2 * Δ ≤ (univ.filter (fun v => part v = i)).card)
    (hne : ∀ i : ι, ∃ v, part v = i) : ∃ M : Finset V, IsIT G part M :=
  exists_IT G part (nonDom_of_degree G part (2 * Δ) (fun v => by have := hdeg v; omega) hcls hne)

end Erdos1078
