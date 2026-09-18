import CameronErdos.Counting.Basic

/-!
# `Lem_Cor13_EvenCase` — Green's Corollary 13, alternative (ii)

Green, *The Cameron–Erdős conjecture* (2004), p. 10, proof of Corollary 13.

In the second alternative of Proposition 7 one knows that a sum-free `A ⊆ [1, N]` has at
most `54 ε^{1/8} N` even elements.  If `A` has **no** even element it is one of the
`2 ^ ⌈N/2⌉` all-odd sets (`Lem_OddCount`).  Otherwise pick an even `t ∈ A`.  Green's
observation is that the odd part of `A` must then avoid a large matching:

* if `t` is small, the pairs `{x, x + t}` with `x` odd;
* if `t` is large, the pairs `{x, t - x}` with `x` odd and `2x < t`;

in either case `⌊N/8⌋` **pairwise disjoint** such pairs of odd numbers of `[1, N]` are
available.  `card_avoiding_matching` then bounds the number of admissible odd parts by
`3 ^ ⌊N/8⌋ · 2 ^ (⌈N/2⌉ - 2⌊N/8⌋)`, and the even part is one of at most
`∑_{j ≤ k} C(⌊N/2⌋, j)` sets.

The main result is `CameronErdos.card_evenPoorNotOdd_le`.
-/

open Finset

namespace CameronErdos

/-! ## The block function used for the small-`t` matching -/

/-- `blockPoint s i` enumerates the odd numbers in the blocks
`[4sb + 1, 4sb + 2s - 1]`, `b = 0, 1, 2, …`: writing `i = s * b + a` with `a < s`,
`blockPoint s i = 4 s b + 2 a + 1`.  Consecutive values inside a block differ by less
than `2s`, and values in different blocks differ by more than `2s`; hence no two of them
differ by exactly `2s`. -/
def blockPoint (s i : ℕ) : ℕ := 2 * (i % s) + 4 * s * (i / s) + 1

lemma blockPoint_odd (s i : ℕ) : Odd (blockPoint s i) :=
  ⟨(i % s) + 2 * s * (i / s), by unfold blockPoint; ring⟩

lemma blockPoint_le (s i : ℕ) : blockPoint s i ≤ 4 * i + 1 := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp only [blockPoint, Nat.mod_zero, Nat.div_zero, Nat.mul_zero,
      Nat.add_zero]; omega
  · have h := Nat.div_add_mod i s
    obtain ⟨u, hu⟩ : ∃ u, s * (i / s) = u := ⟨_, rfl⟩
    have h4 : 4 * s * (i / s) = 4 * u := by rw [← hu]; ring
    rw [hu] at h
    unfold blockPoint
    rw [h4]
    omega

/-- The key gap property: two distinct `blockPoint`s are distinct and never differ by
exactly `2 s`. -/
lemma blockPoint_gap (s : ℕ) (hs : 0 < s) (i j : ℕ) (hij : i ≠ j) :
    blockPoint s i ≠ blockPoint s j ∧
      blockPoint s i + 2 * s ≠ blockPoint s j ∧
      blockPoint s j + 2 * s ≠ blockPoint s i := by
  have hi := Nat.div_add_mod i s
  have hj := Nat.div_add_mod j s
  have hai : i % s < s := Nat.mod_lt _ hs
  have haj : j % s < s := Nat.mod_lt _ hs
  have key : s * (i / s) = s * (j / s) ∨ s * (i / s) + s ≤ s * (j / s) ∨
      s * (j / s) + s ≤ s * (i / s) := by
    rcases lt_trichotomy (i / s) (j / s) with h | h | h
    · refine Or.inr (Or.inl ?_)
      have : s * (i / s) + s = s * (i / s + 1) := by ring
      rw [this]
      exact Nat.mul_le_mul_left s (by omega)
    · exact Or.inl (by rw [h])
    · refine Or.inr (Or.inr ?_)
      have : s * (j / s) + s = s * (j / s + 1) := by ring
      rw [this]
      exact Nat.mul_le_mul_left s (by omega)
  obtain ⟨u, hu⟩ : ∃ u, s * (i / s) = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, s * (j / s) = v := ⟨_, rfl⟩
  have h4i : 4 * s * (i / s) = 4 * u := by rw [← hu]; ring
  have h4j : 4 * s * (j / s) = 4 * v := by rw [← hv]; ring
  unfold blockPoint
  rw [h4i, h4j]
  rw [hu] at hi key
  rw [hv] at hj key
  omega

/-! ## The matching of `⌊N/8⌋` disjoint pairs avoided by the odd part -/

/-- **Green's matching.**  For every even `t` with `2 ≤ t ≤ N` there are `⌊N/8⌋` pairwise
disjoint two-element sets of odd numbers of `[1, N]`, none of which can be contained in a
sum-free set containing `t`.

For `t ≤ 4⌊N/8⌋ - 2` (in particular for all small `t`) the pairs are `{x, x + t}` with
`x = blockPoint (t/2) i`; for larger `t` they are `{2i + 1, t - (2i + 1)}`. -/
theorem exists_avoided_matching (N t : ℕ) (ht2 : 2 ≤ t) (htN : t ≤ N) (hte : Even t) :
    ∃ P : Fin (N / 8) → Finset ℕ,
      (∀ i, P i ⊆ {x ∈ Finset.Icc 1 N | Odd x}) ∧
      (∀ i, #(P i) = 2) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ i, ∀ A : Finset ℕ, IsSumFree A → t ∈ A → ¬ P i ⊆ A) := by
  classical
  set q : ℕ := N / 8 with hq
  have hq8 : 8 * q ≤ N := by omega
  obtain ⟨s, hs⟩ : ∃ s, t = 2 * s := by
    obtain ⟨r, hr⟩ := hte; exact ⟨r, by omega⟩
  have hs1 : 1 ≤ s := by omega
  by_cases hbig : 4 * q < t + 2
  · -- Large `t`: the pairs `{2i+1, t - (2i+1)}`.
    refine ⟨fun i => ({2 * (i : ℕ) + 1, t - (2 * (i : ℕ) + 1)} : Finset ℕ), ?_, ?_, ?_, ?_⟩
    · intro i x hx
      have hi : (i : ℕ) < q := i.isLt
      have hlt : 2 * (2 * (i : ℕ) + 1) < t := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl
      · exact ⟨⟨by omega, by omega⟩, ⟨(i : ℕ), by ring⟩⟩
      · refine ⟨⟨by omega, by omega⟩, ⟨s - (i : ℕ) - 1, by omega⟩⟩
    · intro i
      have hi : (i : ℕ) < q := i.isLt
      have hlt : 2 * (2 * (i : ℕ) + 1) < t := by omega
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    · intro i j hij
      have hi : (i : ℕ) < q := i.isLt
      have hj : (j : ℕ) < q := j.isLt
      have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      have hlti : 2 * (2 * (i : ℕ) + 1) < t := by omega
      have hltj : 2 * (2 * (j : ℕ) + 1) < t := by omega
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, not_or]
      rintro x (rfl | rfl) <;> exact ⟨by omega, by omega⟩
    · intro i A hA ht hsub
      have hi : (i : ℕ) < q := i.isLt
      have hlt : 2 * (2 * (i : ℕ) + 1) < t := by omega
      have h1 : 2 * (i : ℕ) + 1 ∈ A := hsub (by simp)
      have h2 : t - (2 * (i : ℕ) + 1) ∈ A := hsub (by simp)
      have := hA _ h1 _ h2
      rw [show 2 * (i : ℕ) + 1 + (t - (2 * (i : ℕ) + 1)) = t by omega] at this
      exact this ht
  · -- Small `t`: the pairs `{x, x + t}` with `x = blockPoint s i`.
    have hbig : t + 2 ≤ 4 * q := by omega
    refine ⟨fun i => ({blockPoint s (i : ℕ), blockPoint s (i : ℕ) + t} : Finset ℕ), ?_, ?_, ?_, ?_⟩
    · intro i x hx
      have hi : (i : ℕ) < q := i.isLt
      have hb := blockPoint_le s (i : ℕ)
      have hbN : blockPoint s (i : ℕ) + t ≤ N := by omega
      have hodd := blockPoint_odd s (i : ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      obtain ⟨c, hc⟩ := hodd
      rcases hx with rfl | rfl
      · exact ⟨⟨by omega, by omega⟩, ⟨c, hc⟩⟩
      · exact ⟨⟨by omega, by omega⟩, ⟨c + s, by omega⟩⟩
    · intro i
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    · intro i j hij
      have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      obtain ⟨g1, g2, g3⟩ := blockPoint_gap s hs1 (i : ℕ) (j : ℕ) hij'
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, not_or]
      rintro x (rfl | rfl) <;> exact ⟨by omega, by omega⟩
    · intro i A hA ht hsub
      have h1 : blockPoint s (i : ℕ) ∈ A := hsub (by simp)
      have h2 : blockPoint s (i : ℕ) + t ∈ A := hsub (by simp)
      exact hA _ h1 _ ht h2

/-! ## The family being counted -/

/-- The sum-free subsets of `[1, N]` with at most `k` even elements and at least one even
element (Green's alternative (ii), minus the all-odd sets). -/
noncomputable def EvenPoorNotOdd (N : ℕ) (k : ℝ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 N).powerset.filter
    (fun A => IsSumFree A ∧ ((A.filter Even).card : ℝ) ≤ k ∧ (A.filter Even).Nonempty))

/-- For a fixed even part `E` (nonempty, inside the evens of `[1, N]`) the number of
members of `EvenPoorNotOdd N k` with that even part is at most
`3 ^ ⌊N/8⌋ · 2 ^ (⌈N/2⌉ - 2⌊N/8⌋)`: the odd part avoids Green's matching for `t = min E`. -/
theorem card_fiber_le (N : ℕ) (k : ℝ) (E : Finset ℕ)
    (hE : E ⊆ {x ∈ Finset.Icc 1 N | Even x}) (hne : E.Nonempty) :
    #((EvenPoorNotOdd N k).filter (fun A => A.filter Even = E))
      ≤ 3 ^ (N / 8) * 2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
  classical
  set W : Finset ℕ := {x ∈ Finset.Icc 1 N | Odd x} with hW
  set t : ℕ := E.min' hne with htdef
  have htE : t ∈ E := E.min'_mem hne
  have htmem := hE htE
  simp only [Finset.mem_filter, Finset.mem_Icc] at htmem
  obtain ⟨⟨ht1, htN⟩, hte⟩ := htmem
  have ht2 : 2 ≤ t := by
    obtain ⟨r, hr⟩ := hte; omega
  obtain ⟨P, hPW, hPcard, hPdisj, hPavoid⟩ := exists_avoided_matching N t ht2 htN hte
  have hcount := card_avoiding_matching_fin W P hPW hPcard hPdisj
  rw [hW, card_filter_odd_Icc] at hcount
  rw [← hcount]
  refine Finset.card_le_card_of_injOn (fun A => A.filter (fun x => ¬ Even x)) ?_ ?_
  · intro A hA
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, EvenPoorNotOdd, Finset.mem_filter,
      Finset.mem_powerset] at hA
    obtain ⟨⟨hAsub, hAsf, _, _⟩, hAE⟩ := hA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx
      simp only [Finset.mem_filter]
      exact ⟨hAsub hx.1, Nat.not_even_iff_odd.1 hx.2⟩
    · intro i hsub
      refine hPavoid i A hAsf ?_ (hsub.trans (Finset.filter_subset _ _))
      have : t ∈ A.filter Even := by rw [hAE]; exact htE
      exact (Finset.mem_filter.1 this).1
  · intro A hA B hB hAB
    have hAB : A.filter (fun x => ¬ Even x) = B.filter (fun x => ¬ Even x) := hAB
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hA hB
    have hAE := hA.2
    have hBE := hB.2
    ext x
    by_cases hx : Even x
    · constructor
      · intro h
        have : x ∈ A.filter Even := Finset.mem_filter.2 ⟨h, hx⟩
        rw [hAE, ← hBE] at this
        exact (Finset.mem_filter.1 this).1
      · intro h
        have : x ∈ B.filter Even := Finset.mem_filter.2 ⟨h, hx⟩
        rw [hBE, ← hAE] at this
        exact (Finset.mem_filter.1 this).1
    · constructor
      · intro h
        have : x ∈ A.filter (fun x => ¬ Even x) := Finset.mem_filter.2 ⟨h, hx⟩
        rw [hAB] at this
        exact (Finset.mem_filter.1 this).1
      · intro h
        have : x ∈ B.filter (fun x => ¬ Even x) := Finset.mem_filter.2 ⟨h, hx⟩
        rw [← hAB] at this
        exact (Finset.mem_filter.1 this).1

/-- The number of subsets of a finite set `W` of size at most `m` is
`∑_{j ≤ m} C(|W|, j)`. -/
lemma card_powerset_card_le (W : Finset ℕ) (m : ℕ) :
    #{E ∈ W.powerset | #E ≤ m} ≤ ∑ j ∈ Finset.range (m + 1), (#W).choose j := by
  classical
  have hmaps : ((({E ∈ W.powerset | #E ≤ m} : Finset (Finset ℕ)) : Set (Finset ℕ))).MapsTo
      Finset.card (Finset.range (m + 1)) := by
    intro E hE
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powerset] at hE
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum ?_
  intro j _
  have hsub : {E ∈ {E ∈ W.powerset | #E ≤ m} | #E = j} ⊆ W.powersetCard j := by
    intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE
    exact Finset.mem_powersetCard.2 ⟨hE.1.1, hE.2⟩
  calc #{E ∈ {E ∈ W.powerset | #E ≤ m} | #E = j} ≤ #(W.powersetCard j) :=
        Finset.card_le_card hsub
    _ = (#W).choose j := Finset.card_powersetCard j W

/-! ## `Lem_Cor13_EvenCase` -/

/-- **`Lem_Cor13_EvenCase`** (Green 2004, Cor. 13, alternative (ii)).

The sum-free subsets `A ⊆ [1, N]` having at most `k` even elements and at least one even
element number at most
`(∑_{j ≤ ⌊k⌋} C(⌊N/2⌋, j)) · ⌊N/2⌋ · 3 ^ ⌊N/8⌋ · 2 ^ (⌈N/2⌉ - 2⌊N/8⌋)`.

Here `⌊N/2⌋ = N / 2` is the number of even elements of `[1, N]` and `⌈N/2⌉ = (N+1)/2` the
number of odd ones; all divisions are natural-number divisions.  No lower bound on `N` is
needed. -/
theorem card_evenPoorNotOdd_le (N : ℕ) (k : ℝ) (hk : 0 ≤ k) :
    #(EvenPoorNotOdd N k) ≤
      (∑ j ∈ Finset.range (⌊k⌋₊ + 1), (N / 2).choose j) * (N / 2) * 3 ^ (N / 8) *
        2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
  classical
  have _ : (0 : ℝ) ≤ k := hk
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- `[1, N]` has no even element, so the family is empty.
    have : EvenPoorNotOdd N k = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro A hA
      simp only [EvenPoorNotOdd, Finset.mem_filter, Finset.mem_powerset] at hA
      obtain ⟨hAsub, _, _, x, hx⟩ := hA
      simp only [Finset.mem_filter] at hx
      have := hAsub hx.1
      simp only [Finset.mem_Icc] at this
      obtain ⟨r, hr⟩ := hx.2
      omega
    simp [this]
  · set m : ℕ := ⌊k⌋₊ with hm
    set Ev : Finset ℕ := {x ∈ Finset.Icc 1 N | Even x} with hEv
    set T : Finset (Finset ℕ) := {E ∈ Ev.powerset | #E ≤ m ∧ E.Nonempty} with hT
    have hmaps : ((EvenPoorNotOdd N k : Finset (Finset ℕ)) : Set (Finset ℕ)).MapsTo
        (fun A => A.filter Even) T := by
      intro A hA
      simp only [Finset.mem_coe, EvenPoorNotOdd, Finset.mem_filter, Finset.mem_powerset] at hA
      obtain ⟨hAsub, _, hcard, hnon⟩ := hA
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_, hnon⟩
      · intro x hx
        simp only [Finset.mem_filter] at hx
        simp only [hEv, Finset.mem_filter]
        exact ⟨hAsub hx.1, hx.2⟩
      · exact Nat.le_floor hcard
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hstep : ∀ E ∈ T, #{A ∈ EvenPoorNotOdd N k | A.filter Even = E}
        ≤ 3 ^ (N / 8) * 2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
      intro E hE
      simp only [hT, Finset.mem_filter, Finset.mem_powerset] at hE
      exact card_fiber_le N k E hE.1 hE.2.2
    calc ∑ E ∈ T, #{A ∈ EvenPoorNotOdd N k | A.filter Even = E}
        ≤ ∑ _E ∈ T, 3 ^ (N / 8) * 2 ^ ((N + 1) / 2 - 2 * (N / 8)) :=
          Finset.sum_le_sum hstep
      _ = #T * (3 ^ (N / 8) * 2 ^ ((N + 1) / 2 - 2 * (N / 8))) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (∑ j ∈ Finset.range (m + 1), (N / 2).choose j) *
            (3 ^ (N / 8) * 2 ^ ((N + 1) / 2 - 2 * (N / 8))) := by
          refine Nat.mul_le_mul_right _ ?_
          have h1 : T ⊆ {E ∈ Ev.powerset | #E ≤ m} := by
            intro E hE
            simp only [hT, Finset.mem_filter, Finset.mem_powerset] at hE ⊢
            exact ⟨hE.1, hE.2.1⟩
          have h2 := card_powerset_card_le Ev m
          have h3 : #Ev = N / 2 := by rw [hEv]; exact card_filter_even_Icc N
          rw [h3] at h2
          exact le_trans (Finset.card_le_card h1) h2
      _ ≤ (∑ j ∈ Finset.range (m + 1), (N / 2).choose j) * (N / 2) * 3 ^ (N / 8) *
            2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
          have hN2 : 1 ≤ N / 2 := by omega
          have : (∑ j ∈ Finset.range (m + 1), (N / 2).choose j) * 1 * 3 ^ (N / 8) *
              2 ^ ((N + 1) / 2 - 2 * (N / 8))
              ≤ (∑ j ∈ Finset.range (m + 1), (N / 2).choose j) * (N / 2) * 3 ^ (N / 8) *
                2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
            gcongr
          simpa [mul_assoc] using this

/-- The form in which the plan node `Lem_Cor13_EvenCase` states the bound (weaker than
`card_evenPoorNotOdd_le`, which has `C(⌊N/2⌋, j)` and `⌊N/2⌋` in place of `C(N, j)` and `N`):
such sets number at most `(∑_{j ≤ k} C(N, j)) · N · 3 ^ ⌊N/8⌋ · 2 ^ (⌈N/2⌉ - 2⌊N/8⌋)`. -/
theorem card_evenPoorNotOdd_le' (N : ℕ) (k : ℝ) (hk : 0 ≤ k) :
    #(EvenPoorNotOdd N k) ≤
      (∑ j ∈ Finset.range (⌊k⌋₊ + 1), N.choose j) * N * 3 ^ (N / 8) *
        2 ^ ((N + 1) / 2 - 2 * (N / 8)) := by
  refine le_trans (card_evenPoorNotOdd_le N k hk) ?_
  have h1 : ∑ j ∈ Finset.range (⌊k⌋₊ + 1), (N / 2).choose j
      ≤ ∑ j ∈ Finset.range (⌊k⌋₊ + 1), N.choose j :=
    Finset.sum_le_sum fun j _ => Nat.choose_le_choose j (Nat.div_le_self N 2)
  have h2 : N / 2 ≤ N := Nat.div_le_self N 2
  gcongr

#print axioms blockPoint_odd
#print axioms blockPoint_le
#print axioms blockPoint_gap
#print axioms exists_avoided_matching
#print axioms card_fiber_le
#print axioms card_powerset_card_le
#print axioms card_evenPoorNotOdd_le
#print axioms card_evenPoorNotOdd_le'

end CameronErdos
