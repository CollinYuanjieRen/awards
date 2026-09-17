import Erdos926Furedi.Definitions

/-! Turán's bound in the form used here: a `K_k`-free graph on `m` vertices has at most
`(1 - 1/(k-1)) m² / 2` edges; applied to the rich graph on the neighbourhood of `x` this bounds the
number of ordered poor pairs from below. -/

namespace Erdos926

open SimpleGraph Finset

/-- Turán's bound for `K_k`-free graphs, `k ≥ 2`. -/
theorem turan_bound {W : Type*} [Fintype W] [DecidableEq W] (R : SimpleGraph W)
    [DecidableRel R.Adj] (k : ℕ) (hk : 2 ≤ k) (hfree : R.CliqueFree k) :
    (R.edgeFinset.card : ℝ) ≤ (1 - 1 / ((k : ℝ) - 1)) * (Fintype.card W : ℝ) ^ 2 / 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  have h1 : R.edgeFinset.card ≤ turanNumber (Fintype.card W) r := hfree.card_edgeFinset_le
  have h2 : 2 * r * turanNumber (Fintype.card W) r ≤ (r - 1) * (Fintype.card W) ^ 2 :=
    mul_turanNumber_le
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr, Nat.cast_one]
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have h2' : 2 * (r : ℝ) * (turanNumber (Fintype.card W) r : ℝ)
      ≤ ((r : ℝ) - 1) * (Fintype.card W : ℝ) ^ 2 := by
    rw [← hcast]; exact_mod_cast h2
  have h1' : (R.edgeFinset.card : ℝ) ≤ (turanNumber (Fintype.card W) r : ℝ) := by
    exact_mod_cast h1
  have hk1 : ((r + 1 : ℕ) : ℝ) - 1 = (r : ℝ) := by push_cast; ring
  rw [hk1]
  have key : (turanNumber (Fintype.card W) r : ℝ)
      ≤ (1 - 1 / (r : ℝ)) * (Fintype.card W : ℝ) ^ 2 / 2 := by
    rw [show (1 - 1 / (r : ℝ)) = ((r : ℝ) - 1) / (r : ℝ) by field_simp]
    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
    calc (turanNumber (Fintype.card W) r : ℝ) * ((r : ℝ) * 2)
        = 2 * (r : ℝ) * (turanNumber (Fintype.card W) r : ℝ) := by ring
      _ ≤ ((r : ℝ) - 1) * (Fintype.card W : ℝ) ^ 2 := h2'
  linarith

/-- Lower bound for the number of ordered poor pairs at `x` when the rich graph at `x` is
`K_k`-free. -/
theorem poorOrd_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k T : ℕ) (hk : 2 ≤ k) (x : V)
    (hfree : (richGraph G T x).CliqueFree k) :
    (G.degree x : ℝ) ^ 2 / ((k : ℝ) - 1) - G.degree x ≤ poorOrd G T x := by
  classical
  set N := G.neighborFinset x with hN
  set R := richGraph G T x with hR
  -- The rich graph restricted to the neighbourhood of `x`, as a graph on the subtype `↥N`.
  let f : {v // v ∈ N} ↪ V := Function.Embedding.subtype _
  let R' : SimpleGraph {v // v ∈ N} := R.comap f
  have hR'free : R'.CliqueFree k :=
    hfree.comap (SimpleGraph.isContained_iff_exists_le_comap.mpr ⟨f, le_refl _⟩)
  let _instR' : DecidableRel R'.Adj := fun a b => by show Decidable (R.Adj _ _); infer_instance
  have hd : #N = G.degree x := by rw [hN, card_neighborFinset_eq_degree]
  have hcardN : Fintype.card {v // v ∈ N} = G.degree x := by rw [Fintype.card_coe, hd]
  -- Ordered rich pairs of neighbours of `x` are counted twice by the edges of `R'`.
  have hpairs : 2 * #R'.edgeFinset = #(N.offDiag.filter fun uv => T ≤ codeg G uv.1 uv.2) := by
    rw [SimpleGraph.two_mul_card_edgeFinset]
    refine Finset.card_bij (fun p _ => ((p.1 : V), (p.2 : V))) ?_ ?_ ?_
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hne, hxu, hxv, hc⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨hu, hv, hne⟩, hc⟩
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ _ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ _ h
      simp_all
    · rintro ⟨u, v⟩ hq
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hq
      obtain ⟨⟨hu, hv, hne⟩, hc⟩ := hq
      refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hN, SimpleGraph.mem_neighborFinset] at hu hv
      exact ⟨hne, hu, hv, hc⟩
  -- Poor pairs are the complement of the rich pairs inside `N.offDiag`.
  have hsplit : poorOrd G T x + #(N.offDiag.filter fun uv => T ≤ codeg G uv.1 uv.2)
      = #N.offDiag := by
    have h := Finset.card_filter_add_card_filter_not (s := N.offDiag)
      (fun uv : V × V => codeg G uv.1 uv.2 < T)
    simpa [poorOrd, ← hN, not_lt, Finset.filter_congr_decidable] using h
  have hoff : #N.offDiag = G.degree x * G.degree x - G.degree x := by
    rw [Finset.offDiag_card, hd]
  have hdd : G.degree x ≤ G.degree x * G.degree x := by
    rcases Nat.eq_zero_or_pos (G.degree x) with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  have hnat : poorOrd G T x + 2 * #R'.edgeFinset + G.degree x
      = G.degree x * G.degree x := by
    rw [hpairs]
    have := hsplit
    rw [hoff] at this
    omega
  -- Turán's bound applied to `R'`, which lives on `#N = G.degree x` vertices.
  have hturan := turan_bound R' k hk hR'free
  rw [hcardN] at hturan
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hnat' : (poorOrd G T x : ℝ) + 2 * (#R'.edgeFinset : ℝ) + (G.degree x : ℝ)
      = (G.degree x : ℝ) ^ 2 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this
    linarith [this]
  have hexp : (1 - 1 / ((k : ℝ) - 1)) * (G.degree x : ℝ) ^ 2 / 2
      = ((G.degree x : ℝ) ^ 2 - (G.degree x : ℝ) ^ 2 / ((k : ℝ) - 1)) / 2 := by
    ring
  rw [hexp] at hturan
  linarith

end Erdos926
