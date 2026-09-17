import Erdos574Cycles.Girth

/-! The doubled incidence graph contains neither `C₅` nor `C₆`. -/

namespace Erdos574

open SimpleGraph

variable (F : Type*) [Field F]

omit [Field F] in
/-- Every vertex of the doubled graph is either a point or a (copy of a) line. -/
private lemma vtx_cases (u : Vtx F) : (∃ p, u = Sum.inl p) ∨ (∃ m, u = Sum.inr m) := by
  cases u with
  | inl p => exact Or.inl ⟨p, rfl⟩
  | inr m => exact Or.inr ⟨m, rfl⟩

/-- Two points are never adjacent. -/
private lemma not_dAdj_inl_inl {p q : F × F × F} (h : dAdj F (Sum.inl p) (Sum.inl q)) : False := by
  simp [dAdj] at h

/-- Two line-vertices are never adjacent. -/
private lemma not_dAdj_inr_inr {m m' : (F × F × F) ⊕ (F × F × F)}
    (h : dAdj F (Sum.inr m) (Sum.inr m')) : False := by
  cases m <;> cases m' <;> simp [dAdj] at h

/-- A neighbour of a point is a line-vertex. -/
private lemma exists_inr_of_dAdj_inl {p : F × F × F} {u : Vtx F}
    (h : dAdj F (Sum.inl p) u) : ∃ m, u = Sum.inr m := by
  rcases vtx_cases F u with ⟨q, rfl⟩ | ⟨m, rfl⟩
  · exact (not_dAdj_inl_inl F h).elim
  · exact ⟨m, rfl⟩

/-- A neighbour of a line-vertex is a point. -/
private lemma exists_inl_of_dAdj_inr {m : (F × F × F) ⊕ (F × F × F)} {u : Vtx F}
    (h : dAdj F (Sum.inr m) u) : ∃ p, u = Sum.inl p := by
  rcases vtx_cases F u with ⟨p, rfl⟩ | ⟨m', rfl⟩
  · exact ⟨p, rfl⟩
  · exact (not_dAdj_inr_inr F h).elim

/-- The line underlying a line-vertex, forgetting which of the two copies it belongs to. -/
private def lineOf (m : (F × F × F) ⊕ (F × F × F)) : F × F × F := Sum.elim id id m

private lemma incid_of_dAdj {p : F × F × F} {m : (F × F × F) ⊕ (F × F × F)}
    (h : dAdj F (Sum.inl p) (Sum.inr m)) : Incid F p (lineOf F m) := by
  cases m <;> exact h

omit [Field F] in
/-- Three pairwise distinct line-vertices cannot all lie over the same line: there are only two
copies of each line. -/
private lemma not_three_copies {m₁ m₂ m₃ : (F × F × F) ⊕ (F × F × F)}
    (d12 : m₁ ≠ m₂) (d23 : m₂ ≠ m₃) (d13 : m₁ ≠ m₃)
    (e12 : lineOf F m₁ = lineOf F m₂) (e23 : lineOf F m₂ = lineOf F m₃) : False := by
  cases m₁ <;> cases m₂ <;> cases m₃ <;> simp_all [lineOf]

/-- A hexagon of incidences whose three lines are not all equal is impossible. -/
private lemma hex_core {p₁ p₂ p₃ L₁ L₂ L₃ : F × F × F}
    (hp12 : p₁ ≠ p₂) (hp23 : p₂ ≠ p₃) (hp13 : p₁ ≠ p₃)
    (h11 : Incid F p₁ L₁) (h21 : Incid F p₂ L₁) (h22 : Incid F p₂ L₂)
    (h32 : Incid F p₃ L₂) (h33 : Incid F p₃ L₃) (h13 : Incid F p₁ L₃)
    (hne : ¬ (L₁ = L₂ ∧ L₂ = L₃)) : False := by
  by_cases e12 : L₁ = L₂
  · subst e12
    have e13 : L₁ ≠ L₃ := fun h => hne ⟨rfl, h⟩
    exact no_C4 hp13 e13 h11 h32 h13 h33
  · by_cases e23 : L₂ = L₃
    · subst e23
      exact no_C4 hp12 e12 h11 h21 h13 h22
    · by_cases e13 : L₁ = L₃
      · subst e13
        exact no_C4 hp23 e12 h21 h33 h22 h32
      · exact no_C6 hp12 hp23 hp13 e12 e23 e13 h11 h21 h22 h32 h33 h13

/-- A hexagon in the doubled graph, given as three points and three line-vertices, is impossible. -/
private lemma hex_false {p₁ p₂ p₃ : F × F × F} {m₁ m₂ m₃ : (F × F × F) ⊕ (F × F × F)}
    (hp12 : p₁ ≠ p₂) (hp23 : p₂ ≠ p₃) (hp13 : p₁ ≠ p₃)
    (hm12 : m₁ ≠ m₂) (hm23 : m₂ ≠ m₃) (hm13 : m₁ ≠ m₃)
    (a11 : dAdj F (Sum.inl p₁) (Sum.inr m₁)) (a21 : dAdj F (Sum.inl p₂) (Sum.inr m₁))
    (a22 : dAdj F (Sum.inl p₂) (Sum.inr m₂)) (a32 : dAdj F (Sum.inl p₃) (Sum.inr m₂))
    (a33 : dAdj F (Sum.inl p₃) (Sum.inr m₃)) (a13 : dAdj F (Sum.inl p₁) (Sum.inr m₃)) :
    False :=
  hex_core F hp12 hp23 hp13 (incid_of_dAdj F a11) (incid_of_dAdj F a21) (incid_of_dAdj F a22)
    (incid_of_dAdj F a32) (incid_of_dAdj F a33) (incid_of_dAdj F a13)
    (fun h => not_three_copies F hm12 hm23 hm13 h.1 h.2)

/-- A closed walk of length 5 starting at a point is impossible: the graph is bipartite. -/
private lemma pent_false {u₀ u₁ u₂ u₃ u₄ : Vtx F} {p₀ : F × F × F} (hu₀ : u₀ = Sum.inl p₀)
    (h01 : dAdj F u₀ u₁) (h12 : dAdj F u₁ u₂) (h23 : dAdj F u₂ u₃)
    (h34 : dAdj F u₃ u₄) (h40 : dAdj F u₄ u₀) : False := by
  subst hu₀
  obtain ⟨m₁, rfl⟩ := exists_inr_of_dAdj_inl F h01
  obtain ⟨q₂, rfl⟩ := exists_inl_of_dAdj_inr F h12
  obtain ⟨m₂, rfl⟩ := exists_inr_of_dAdj_inl F h23
  obtain ⟨q₃, rfl⟩ := exists_inl_of_dAdj_inr F h34
  exact not_dAdj_inl_inl F h40

/-- A 6-cycle starting at a point is impossible. -/
private lemma hex_cycle_false {u₀ u₁ u₂ u₃ u₄ u₅ : Vtx F} {p₀ : F × F × F}
    (hu₀ : u₀ = Sum.inl p₀)
    (h01 : dAdj F u₀ u₁) (h12 : dAdj F u₁ u₂) (h23 : dAdj F u₂ u₃)
    (h34 : dAdj F u₃ u₄) (h45 : dAdj F u₄ u₅) (h50 : dAdj F u₅ u₀)
    (d02 : u₀ ≠ u₂) (d24 : u₂ ≠ u₄) (d04 : u₀ ≠ u₄)
    (d13 : u₁ ≠ u₃) (d35 : u₃ ≠ u₅) (d15 : u₁ ≠ u₅) : False := by
  subst hu₀
  obtain ⟨m₁, rfl⟩ := exists_inr_of_dAdj_inl F h01
  obtain ⟨q₂, rfl⟩ := exists_inl_of_dAdj_inr F h12
  obtain ⟨m₂, rfl⟩ := exists_inr_of_dAdj_inl F h23
  obtain ⟨q₃, rfl⟩ := exists_inl_of_dAdj_inr F h34
  obtain ⟨m₃, rfl⟩ := exists_inr_of_dAdj_inl F h45
  exact hex_false F (fun h => d02 (congrArg Sum.inl h)) (fun h => d24 (congrArg Sum.inl h))
    (fun h => d04 (congrArg Sum.inl h)) (fun h => d13 (congrArg Sum.inr h))
    (fun h => d35 (congrArg Sum.inr h)) (fun h => d15 (congrArg Sum.inr h))
    h01 (dAdj_symm F _ _ h12) h23 (dAdj_symm F _ _ h34) h45 (dAdj_symm F _ _ h50)

theorem doubled_free_five : (cycleGraph 5).Free (doubled F) := by
  rintro ⟨f⟩
  have a01 : dAdj F (f 0) (f 1) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a12 : dAdj F (f 1) (f 2) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a23 : dAdj F (f 2) (f 3) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a34 : dAdj F (f 3) (f 4) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a40 : dAdj F (f 4) (f 0) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  rcases vtx_cases F (f 0) with ⟨p, hp⟩ | ⟨m, hm⟩
  · exact pent_false F hp a01 a12 a23 a34 a40
  · have hpt : ∃ p, f 1 = Sum.inl p := by
      rw [hm] at a01
      exact exists_inl_of_dAdj_inr F a01
    obtain ⟨p, hp⟩ := hpt
    exact pent_false F hp a12 a23 a34 a40 a01

theorem doubled_free_six : (cycleGraph 6).Free (doubled F) := by
  rintro ⟨f⟩
  have a01 : dAdj F (f 0) (f 1) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a12 : dAdj F (f 1) (f 2) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a23 : dAdj F (f 2) (f 3) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a34 : dAdj F (f 3) (f 4) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a45 : dAdj F (f 4) (f 5) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have a50 : dAdj F (f 5) (f 0) := f.toHom.map_adj (by rw [cycleGraph_adj]; exact Or.inr rfl)
  have hne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j hij h => hij (f.injective h)
  rcases vtx_cases F (f 0) with ⟨p, hp⟩ | ⟨m, hm⟩
  · exact hex_cycle_false F hp a01 a12 a23 a34 a45 a50
      (hne 0 2 (by simp)) (hne 2 4 (by simp)) (hne 0 4 (by simp))
      (hne 1 3 (by simp)) (hne 3 5 (by simp)) (hne 1 5 (by simp))
  · have hpt : ∃ p, f 1 = Sum.inl p := by
      rw [hm] at a01
      exact exists_inl_of_dAdj_inr F a01
    obtain ⟨p, hp⟩ := hpt
    exact hex_cycle_false F hp a12 a23 a34 a45 a50 a01
      (hne 1 3 (by simp)) (hne 3 5 (by simp)) (hne 1 5 (by simp))
      (hne 2 4 (by simp)) (hne 4 0 (by simp)) (hne 2 0 (by simp))

end Erdos574
