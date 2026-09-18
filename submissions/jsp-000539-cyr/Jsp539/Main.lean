import Jsp539.Events
import Jsp539.Asymptotics

/-!
# JSP-000539 / Erdős #664 — the negative answer

Erdős asked (for a constant `c < 1`) whether every family `A_1, …, A_m ⊆ {1, …, n}` with
`|A_i| > c √n` and `|A_i ∩ A_j| ≤ 1` for `i ≠ j` has a set `B` meeting every `A_i` in at least
one and at most `≪_c 1` points.  The answer is **no**: Alon's random construction on an affine
plane produces, for every `c < 1` and every bound `K`, a linear family with parts of size
`> c √n` such that every set meeting all parts meets one of them in more than `K` points.

* `counterexample` : the family, for a given `c < 1` and a given bound `K`.
* `erdos_664` : there is no uniform transversal bound, for any `c < 1`.
* `not_erdos_664` : the special case `c = 2/5` recorded on the problem page.
-/

open Finset

namespace Erdos664

/-- **Alon's counterexample family.**  For every `c < 1` and every bound `K` there is a family of
subsets of an `n`-element set, all of size `> c √n`, with pairwise intersections of size at most
one, such that every set meeting all of them meets one of them in more than `K` points. -/
theorem counterexample (c : ℝ) (hc : c < 1) (K : ℕ) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, c * Real.sqrt n < #(A i)) ∧ LinearFamily A ∧
        ∀ B, HitsAll A B → ∃ i, K < #(B ∩ A i) := by
  -- the parameters
  have h0 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  have hlt1 : max c 0 < 1 := max_lt hc zero_lt_one
  have hcle : c ≤ max c 0 := le_max_left _ _
  obtain ⟨M, hM5, hM⟩ := exists_M (max c 0) hlt1
  have : NeZero M := ⟨by omega⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨p₀, hp₀⟩ := eventually_sum_lt_one (max c 0) h0 hlt1 M hM5 hM K
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max p₀ 2)
  have := Fact.mk hprime
  have hpp₀ : p₀ ≤ p := le_trans (le_max_left _ _) hp
  have hp2 : 2 ≤ p := le_trans (le_max_right _ _) hp
  -- a sample avoiding the three bad events
  obtain ⟨ω, h1, h2, h3⟩ :=
    exists_good (p := p) (M := M) hM1 ⌊max c 0 * (p : ℝ)⌋₊ (p / 2) K (hp₀ p hpp₀)
  -- transport the construction to `Fin n`
  have eP : Pt p ≃ Fin (Fintype.card (Pt p)) := Fintype.equivFin _
  have eL : Line p ≃ Fin (Fintype.card (Line p)) := Fintype.equivFin _
  have hsqrt : Real.sqrt (Fintype.card (Pt p) : ℝ) = (p : ℝ) := by
    rw [card_Pt]
    push_cast
    exact Real.sqrt_sq (by positivity)
  refine ⟨Fintype.card (Pt p), Fintype.card (Line p),
    fun i => (kept ω (eL.symm i)).map eP.toEmbedding, fun i => ?_, fun i j hij => ?_,
    fun B hB => ?_⟩
  · -- the parts are large
    rw [Finset.card_map, hsqrt]
    have hk : ⌊max c 0 * (p : ℝ)⌋₊ < #(kept ω (eL.symm i)) := h1 _
    have hkR : max c 0 * (p : ℝ) < (#(kept ω (eL.symm i)) : ℝ) := by
      calc max c 0 * (p : ℝ) < (⌊max c 0 * (p : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ (#(kept ω (eL.symm i)) : ℝ) := by exact_mod_cast hk
    have hple : c * (p : ℝ) ≤ max c 0 * (p : ℝ) :=
      mul_le_mul_of_nonneg_right hcle (by positivity)
    linarith
  · -- the family is linear
    have hne : eL.symm i ≠ eL.symm j := fun h => hij (eL.symm.injective h)
    rw [← Finset.map_inter, Finset.card_map]
    exact kept_inter_card_le_one hne
  · -- every transversal is large on some part
    obtain ⟨B', hB'⟩ : ∃ B' : Finset (Pt p), B = B'.map eP.toEmbedding :=
      ⟨B.map eP.symm.toEmbedding, by rw [Finset.map_map]; simp⟩
    subst hB'
    have hhit : ∀ ℓ : Line p, (B' ∩ kept ω ℓ).Nonempty := by
      intro ℓ
      obtain ⟨y, hy⟩ := hB (eL ℓ)
      simp only [Equiv.symm_apply_apply] at hy
      rw [← Finset.map_inter] at hy
      obtain ⟨x, hx, -⟩ := Finset.mem_map.1 hy
      exact ⟨x, hx⟩
    have hbig := h3 B' hhit
    by_contra hcon
    push Not at hcon
    have hle : ∀ ℓ : Line p, #(B' ∩ kept ω ℓ) ≤ K := by
      intro ℓ
      have h := hcon (eL ℓ)
      simp only [Equiv.symm_apply_apply] at h
      rwa [← Finset.map_inter, Finset.card_map] at h
    have hupper : ∑ ℓ : Line p, #(B' ∩ kept ω ℓ) ≤ p ^ 2 * K := by
      have h := Finset.sum_le_card_nsmul (univ : Finset (Line p))
        (fun ℓ => #(B' ∩ kept ω ℓ)) K fun ℓ _ => hle ℓ
      rwa [Finset.card_univ, card_Line, smul_eq_mul] at h
    have hlower : #B' * (p / 2 + 1) ≤ ∑ ℓ : Line p, #(B' ∩ kept ω ℓ) := by
      rw [sum_card_inter_kept]
      have h := Finset.card_nsmul_le_sum B' (fun z => deg ω z) (p / 2 + 1) fun z _ => h2 z
      rwa [smul_eq_mul] at h
    have hBig : p ^ 2 * (K + 1) + p * (K + 1) ≤ #B' * (p / 2 + 1) := by
      calc p ^ 2 * (K + 1) + p * (K + 1) = p * (K + 1) * (p + 1) := by ring
        _ ≤ p * (K + 1) * (2 * (p / 2) + 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * p * (K + 1) * (p / 2 + 1) := by ring
        _ ≤ #B' * (p / 2 + 1) := Nat.mul_le_mul_right _ (le_of_lt hbig)
    have hfin : p ^ 2 * (K + 1) + p * (K + 1) ≤ p ^ 2 * K :=
      le_trans hBig (le_trans hlower hupper)
    have hexp : p ^ 2 * (K + 1) = p ^ 2 * K + p ^ 2 := by ring
    rw [hexp, add_assoc] at hfin
    have hp0 : p = 0 := by simpa using hfin
    omega

/-- **Erdős #664 has a negative answer**: for every `c < 1` there is no bound `K` such that every
linear family with parts of size `> c √n` has a transversal meeting every part in at most `K`
points. -/
theorem erdos_664 (c : ℝ) (hc : c < 1) : ¬ ∃ K : ℕ, HasUniformTransversalBound c K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hs, hl, hu⟩ := counterexample c hc K
  obtain ⟨B, hB, hb⟩ := hK n m A hs hl
  obtain ⟨i, hi⟩ := hu B hB
  exact absurd (hb i) (not_le.2 hi)

/-- The case `c = 2/5` recorded on the problem page. -/
theorem not_erdos_664 : ¬ ∃ K : ℕ, HasUniformTransversalBound (2 / 5 : ℝ) K :=
  erdos_664 _ (by norm_num)

end Erdos664
