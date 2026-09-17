import Erdos210Ordinary.Bridge

/-!
# Erdős Problem 210 — a witness configuration, and attainment of `f`

For every `n ≥ 3` the `n` points `(0, 0), (1, 0), …, (n - 2, 0)` together with `(0, 1)` are not
collinear, so the set of numbers of ordinary lines determined by `n` non-collinear points is
nonempty and its infimum `f n` is attained (`Nat.sInf_mem`).
-/

namespace Erdos210

/-- The witness configuration: `n - 1` points on the `x`-axis together with `(0, 1)`. -/
private noncomputable def witness (n : ℕ) : Finset (ℝ × ℝ) :=
  ((Finset.range (n - 1)).image fun i : ℕ => ((i : ℝ), (0 : ℝ))) ∪ {((0 : ℝ), (1 : ℝ))}

private lemma injective_witness_map :
    Function.Injective fun i : ℕ => ((i : ℝ), (0 : ℝ)) := by
  intro i j h
  simpa using congrArg Prod.fst h

private lemma card_witness {n : ℕ} (hn : 3 ≤ n) : (witness n).card = n := by
  have hdisj : Disjoint ((Finset.range (n - 1)).image fun i : ℕ => ((i : ℝ), (0 : ℝ)))
      ({((0 : ℝ), (1 : ℝ))} : Finset (ℝ × ℝ)) := by
    rw [Finset.disjoint_right]
    intro x hx hx'
    rw [Finset.mem_singleton] at hx
    subst hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hx'
    simpa using congrArg Prod.snd hi
  have h1 : 1 ≤ n := le_trans (by norm_num) hn
  rw [witness, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ injective_witness_map, Finset.card_range,
    Finset.card_singleton]
  omega

private lemma notCollinear_witness {n : ℕ} (hn : 3 ≤ n) : NotCollinear (witness n) := by
  have h0 : 0 ∈ Finset.range (n - 1) := Finset.mem_range.2 (by omega)
  have h1 : 1 ∈ Finset.range (n - 1) := Finset.mem_range.2 (by omega)
  refine ⟨((0 : ℝ), (0 : ℝ)), ?_, ((1 : ℝ), (0 : ℝ)), ?_, ((0 : ℝ), (1 : ℝ)), ?_, ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, h0, by norm_num⟩)
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, h1, by norm_num⟩)
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · simp [OnLine, D]

theorem exists_config (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) :=
  ⟨witness n, card_witness hn, (notCollinear_iff _).1 (notCollinear_witness hn)⟩

/-- `f n` is attained for `n ≥ 3`. -/
theorem f_mem (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) ∧
      (ordinaryLines P).ncard = f n := by
  have hne : {m : ℕ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) ∧
      (ordinaryLines P).ncard = m}.Nonempty := by
    obtain ⟨P, hcard, hcol⟩ := exists_config n hn
    exact ⟨(ordinaryLines P).ncard, P, hcard, hcol, rfl⟩
  simpa only [f, Set.mem_ofPred_eq] using Nat.sInf_mem hne

end Erdos210
