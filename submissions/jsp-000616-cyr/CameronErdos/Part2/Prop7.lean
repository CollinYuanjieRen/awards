import CameronErdos.Part2.Ineq16
import CameronErdos.Part2.LLS
import CameronErdos.Kneser.Kneser

/-!
# `Prop7_Stability`: Green's Proposition 7

This file formalises Proposition 7 of Green, *The Cameron–Erdős conjecture* (2004), pp. 8–10:
a set `A ⊆ [1, N]` of size roughly `N/2` with few additive triples is either almost contained
in a short interval, or almost entirely odd.

Writing `ρ = ε^{1/8}`, the precise statement (`CameronErdos.prop7`) is: if `A ⊆ [1, N]`,
`0 < ε ≤ 10^{-32}`, `ρN ≥ 1000`, `|A| ≥ (1/2 − 1/120)N` and `A` has at most `εN²` additive
triples, then either

* (i) there is an interval `[u, u + len)` with `len ≤ 2N(1 + 30ρ) − 3|A|` containing all but
  at most `32ρN` elements of `A`, or
* (ii) `A` has at most `54ρN` even elements.

Two corrections to Green's write-up are incorporated (see the plan node `Prop7_Stability`):
the first case of the argument is `2|X| > t` (at `2|X| = t` the set `X − X` need not be the
whole group), and the hypothesis is `|A| ≥ (1/2 − 1/120)N` with `ε ≤ 10^{-32}`, which is what
the downstream consumer needs and leaves a positive margin in the even subcase.

## Proof outline

`lem16` supplies `m < M` in `A` with `t := M − m > N/4`, few elements of `A` outside
`(m, M)`, and inequality (16) for `D := D(π(A), 8√ε N)`, where `π : ℤ → ZMod t`.  Lemma 10
(`lls_prop1_real`) then produces `X ⊆ π(A)` with `|X| ≥ |A| − 54ρN` and `X − X ⊆ D`.

* If `2|X| > t` then `X − X` is all of `ZMod t`, so `t ≤ |D|` and alternative (i) holds with
  the interval `(m, M]`.
* If `|X − X| ≥ 2|X| − t/3` then (16) forces `|A| < (1/2 − 1/120)N`, a contradiction.
* Otherwise Kneser's theorem (`Finset.add_kneser`) applied to `X` and `−X` shows that the
  stabiliser `H` of `X − X` has `|H| > t/3`; since `|H| ∣ t`, either `H` is everything
  (excluded by `2|X| ≤ t`) or `t = 2|H|`.  In the latter case `X` lies in a single coset of
  `H`, and `H`, having index `2`, contains every double, hence is exactly the set of even
  residues.  So all elements of `A` lying above `X` share a parity: if it is odd we get
  alternative (ii), and if it is even then `A` contains at least `12N/25` even numbers of
  `[1, N]`, so `lem_evenSetTriples` gives `N²/100 ≤ εN²`, a contradiction.
-/

open Finset
open scoped Pointwise

namespace CameronErdos

section Helpers

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The stabilizer finset is closed under negation. -/
lemma neg_mem_addStab {s : Finset G} (hs : s.Nonempty) {a : G} (ha : a ∈ s.addStab) :
    -a ∈ s.addStab := by
  rw [Finset.mem_addStab hs] at ha ⊢
  have h : -a +ᵥ (a +ᵥ s) = s := by rw [vadd_vadd, neg_add_cancel, zero_vadd]
  rwa [ha] at h

/-- The stabilizer finset is closed under addition. -/
lemma add_mem_addStab {s : Finset G} {a b : G} (ha : a ∈ s.addStab) (hb : b ∈ s.addStab) :
    a + b ∈ s.addStab := by
  have h : a + b ∈ s.addStab + s.addStab := Finset.mem_add.2 ⟨a, ha, b, hb, rfl⟩
  rwa [Finset.addStab_add_addStab] at h

variable [Fintype G]

/-- A subgroup-like finset of index `2` contains every double. -/
lemma double_mem_of_two_mul_card {H : Finset G}
    (hadd : ∀ ⦃x⦄, x ∈ H → ∀ ⦃y⦄, y ∈ H → x + y ∈ H) (hneg : ∀ ⦃x⦄, x ∈ H → -x ∈ H)
    (hcard : 2 * #H = Fintype.card G) (g : G) : g + g ∈ H := by
  classical
  by_cases hg : g ∈ H
  · exact hadd hg hg
  · set T : Finset G := H.image (fun h => g + h) with hT
    have hTcard : #T = #H := Finset.card_image_of_injective _ (add_right_injective g)
    have hdisj : Disjoint H T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      rw [hT, Finset.mem_image] at hxT
      obtain ⟨h, hh, rfl⟩ := hxT
      exact hg (by simpa using hadd hx (hneg hh))
    have hunion : H ∪ T = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, hTcard, ← two_mul, hcard]
    have hmem : g + g ∈ H ∪ T := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.1 hmem with h | h
    · exact h
    · exfalso
      rw [hT, Finset.mem_image] at h
      obtain ⟨h', hh', he⟩ := h
      have : g = h' := (add_left_cancel he).symm
      exact hg (this ▸ hh')

/-- If `2|X| > |G|` then `X - X = G`. -/
lemma sub_eq_univ_of_card_lt {X : Finset G} (h : Fintype.card G < 2 * #X) :
    X - X = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro g
  set T : Finset G := X.image (fun x => g + x) with hT
  have hTcard : #T = #X := Finset.card_image_of_injective _ (add_right_injective g)
  have hne : (X ∩ T).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : #(X ∪ T) ≤ Fintype.card G := Finset.card_le_univ _
    have h2 := Finset.card_union_add_card_inter X T
    omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter, hT, Finset.mem_image] at hx
  obtain ⟨hxX, y, hy, hxy⟩ := hx
  exact Finset.mem_sub.2 ⟨x, hxX, y, hy, by rw [← hxy]; abel⟩

end Helpers

/-- `addTriples` is monotone in the set. -/
lemma addTriples_mono {G : Type*} [Add G] [DecidableEq G] {A B : Finset G} (h : A ⊆ B) :
    addTriples A ≤ addTriples B := by
  refine Finset.card_le_card ?_
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
  exact ⟨⟨h hq.1.1, h hq.1.2.1, h hq.1.2.2⟩, hq.2⟩

section Prop7

variable {N : ℕ} {A : Finset ℤ}

/-- **Green's Proposition 7** (`Prop7_Stability`).  A set `A ⊆ [1, N]` with
`|A| ≥ (1/2 − 1/120)N` and at most `εN²` additive triples either lies, up to `32ε^{1/8}N`
exceptions, in an interval of length at most `2N(1 + 30ε^{1/8}) − 3|A|`, or has at most
`54ε^{1/8}N` even elements. -/
theorem prop7 (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (hε0 : ε ≤ 1 / 10 ^ 32)
    (hN : (1000 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ))
    (hAcard : (1 / 2 - 1 / 120 : ℝ) * (N : ℝ) ≤ (#A : ℝ))
    (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    (∃ u : ℤ, ∃ len : ℕ,
        (len : ℝ) ≤ 2 * (N : ℝ) * (1 + 30 * Real.sqrt (Real.sqrt (Real.sqrt ε)))
          - 3 * (#A : ℝ) ∧
        (#{a ∈ A | a ∉ Finset.Ico u (u + len)} : ℝ)
          ≤ 32 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) ∨
      (#{a ∈ A | Even a} : ℝ) ≤ 54 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ) := by
  classical
  set ρ : ℝ := Real.sqrt (Real.sqrt (Real.sqrt ε)) with hρdef
  -- ### numerics
  have hρpos : 0 < ρ := Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hε))
  have hρ2 : ρ ^ 2 = Real.sqrt (Real.sqrt ε) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hρ4 : ρ ^ 4 = Real.sqrt ε := by
    have : (ρ ^ 2) ^ 2 = Real.sqrt ε := by rw [hρ2]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
    rw [← this]; ring
  have hρ8 : ρ ^ 8 = ε := by
    have : (ρ ^ 4) ^ 2 = ε := by rw [hρ4]; exact Real.sq_sqrt hε.le
    rw [← this]; ring
  have hρsmall : ρ ≤ 1 / 10 ^ 4 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (1 / 10 ^ 4 : ℝ) ^ 8 < ρ ^ 8 :=
      pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    rw [hρ8] at h1
    norm_num at h1
    linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNbig : (10 : ℝ) ^ 7 ≤ (N : ℝ) := by nlinarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith
  have hρN : ρ * (N : ℝ) ≤ (1 / 10 ^ 4) * (N : ℝ) := by nlinarith
  have hρ2N : ρ ^ 2 * (N : ℝ) ≤ (1 / 10 ^ 8) * (N : ℝ) := by nlinarith
  have hρsq : ρ ^ 2 * (N : ℝ) ≤ ρ * (N : ℝ) := by nlinarith
  -- ### Lemma 16
  obtain ⟨m, M, hm, hM, hmM, hgap, hleft, hright, hScard, h16⟩ :=
    lem16 hA hε (by linarith) hN (by nlinarith) htr
  set t : ℕ := (M - m).toNat with htdef
  have hmA := Finset.mem_Icc.1 (hA hm)
  have hMA := Finset.mem_Icc.1 (hA hM)
  have htZ : (t : ℤ) = M - m := by rw [htdef]; omega
  have htpos : 0 < t := by omega
  have : NeZero t := ⟨by omega⟩
  have htR : (t : ℝ) = (M : ℝ) - (m : ℝ) := by exact_mod_cast htZ
  have htN : (t : ℝ) ≤ (N : ℝ) := by
    have : (t : ℤ) ≤ (N : ℤ) := by omega
    exact_mod_cast this
  have htgap : (N : ℝ) / 4 < (t : ℝ) := by rw [htR]; exact hgap
  set S : Finset (ZMod t) := projImage t A with hSdef
  set K : ℝ := 8 * Real.sqrt ε * (N : ℝ) with hKdef
  set D : Finset (ZMod t) := popularDiff S K with hDdef
  have hcardZMod : Fintype.card (ZMod t) = t := ZMod.card t
  have hSS : (#(S - S) : ℝ) ≤ (N : ℝ) := by
    have h1 : #(S - S) ≤ Fintype.card (ZMod t) := Finset.card_le_univ _
    rw [hcardZMod] at h1
    have : ((#(S - S) : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
    linarith
  -- ### Lemma 10 : the almost-translate `X`
  obtain ⟨X, hXS, hXcard, hXD⟩ :
      ∃ X ⊆ S, (#A : ℝ) - 54 * ρ * (N : ℝ) ≤ (#X : ℝ) ∧ X - X ⊆ D := by
    by_cases hK1 : (1 : ℝ) ≤ K
    · have hsqrt : Real.sqrt (2 * K * (#(S - S) : ℝ)) ≤ 4 * ρ ^ 2 * (N : ℝ) := by
        have hsq : 2 * K * (#(S - S) : ℝ) ≤ (4 * ρ ^ 2 * (N : ℝ)) ^ 2 := by
          have h0 : (0 : ℝ) ≤ (#(S - S) : ℝ) := Nat.cast_nonneg _
          rw [hKdef, ← hρ4]
          nlinarith [sq_nonneg ρ, pow_pos hρpos 2]
        calc Real.sqrt (2 * K * (#(S - S) : ℝ))
            ≤ Real.sqrt ((4 * ρ ^ 2 * (N : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = 4 * ρ ^ 2 * (N : ℝ) := Real.sqrt_sq (by positivity)
      have hDb : (#D : ℝ) ≤ 2 * (#S : ℝ) - 5 * Real.sqrt (2 * K * (#(S - S) : ℝ)) := by
        by_contra hcon
        rw [not_le] at hcon
        linarith only [hcon, hsqrt, h16, hScard, hAcard, hρN, hρ2N]
      obtain ⟨X, hXS, hXc, hXD⟩ := lls_prop1_real S hK1 hDb
      refine ⟨X, hXS, ?_, hXD⟩
      have hsplit : #(S \ X) + #X = #S := Finset.card_sdiff_add_card_eq_card hXS
      have hsplitR : ((#(S \ X) : ℕ) : ℝ) + (#X : ℝ) = (#S : ℝ) := by exact_mod_cast hsplit
      have hle := le_trans hXc hsqrt
      linarith only [hle, hsplitR, hScard, hρsq]
    · rw [not_le] at hK1
      refine ⟨S, Finset.Subset.refl _, by linarith [hScard], ?_⟩
      intro d hd
      rw [hDdef, popularDiff_eq, Finset.mem_filter]
      refine ⟨hd, ?_⟩
      have h1 : 0 < diffReps S d := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.1 hd
        rw [diffReps, Finset.card_pos]
        exact ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩⟩
      have : (1 : ℝ) ≤ (diffReps S d : ℝ) := by exact_mod_cast h1
      linarith
  have hρNpos : (0 : ℝ) < ρ * (N : ℝ) := by positivity
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (0 : ℝ) < (#X : ℝ) := by linarith only [hXcard, hAcard, hρN, hNpos]
    exact_mod_cast h1
  -- ### Case 1 : `2|X| > t`
  by_cases hcase1 : t < 2 * #X
  · left
    have hXX : X - X = Finset.univ :=
      sub_eq_univ_of_card_lt (by rw [hcardZMod]; exact hcase1)
    have hDcard : t ≤ #D := by
      have h1 : #(X - X) ≤ #D := Finset.card_le_card hXD
      rwa [hXX, Finset.card_univ, hcardZMod] at h1
    have hDcardR : (t : ℝ) ≤ (#D : ℝ) := by exact_mod_cast hDcard
    refine ⟨m + 1, t, by linarith only [hDcardR, h16], ?_⟩
    have hsub : {a ∈ A | a ∉ Finset.Ico (m + 1) (m + 1 + (t : ℤ))} ⊆
        {a ∈ A | a ≤ m} ∪ {a ∈ A | M ≤ a} := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have h2 : ¬ (m + 1 ≤ a ∧ a < m + 1 + (t : ℤ)) := fun h => ha.2 (Finset.mem_Ico.2 h)
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hle : a ≤ m
      · exact Or.inl ⟨ha.1, hle⟩
      · exact Or.inr ⟨ha.1, by omega⟩
    have hc1 : #{a ∈ A | a ∉ Finset.Ico (m + 1) (m + 1 + (t : ℤ))}
        ≤ #{a ∈ A | a ≤ m} + #{a ∈ A | M ≤ a} :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hc1R : (#{a ∈ A | a ∉ Finset.Ico (m + 1) (m + 1 + (t : ℤ))} : ℝ)
        ≤ (#{a ∈ A | a ≤ m} : ℝ) + (#{a ∈ A | M ≤ a} : ℝ) := by exact_mod_cast hc1
    linarith only [hc1R, hleft, hright, hρNpos]
  · rw [not_lt] at hcase1
    have hcase1R : 2 * (#X : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcase1
    have hXDR : (#(X - X) : ℝ) ≤ (#D : ℝ) := by
      exact_mod_cast Finset.card_le_card hXD
    by_cases hcase2 : 2 * (#X : ℝ) - (t : ℝ) / 3 ≤ (#(X - X) : ℝ)
    · -- ### Case 2 : impossible
      exact absurd hAcard (by
        rw [not_le]
        linarith only [hcase2, hXDR, h16, hXcard, htN, hρN, hNpos])
    · -- ### Case 3
      rw [not_le] at hcase2
      have hXXne : (X - X).Nonempty := by
        obtain ⟨x, hx⟩ := hXne
        exact ⟨x - x, Finset.mem_sub.2 ⟨x, hx, x, hx, rfl⟩⟩
      have hXsub : X + (-X) = X - X := (sub_eq_add_neg X X).symm
      set H : Finset (ZMod t) := (X - X).addStab with hHdef
      have h0H : (0 : ZMod t) ∈ H := hXXne.zero_mem_addStab
      have hkn : #(X + H) + #(-X + H) ≤ #(X - X) + #H := by
        have h := Finset.add_kneser X (-X)
        rwa [hXsub] at h
      have hXHcard : #X ≤ #(X + H) :=
        Finset.card_le_card (fun x hx => Finset.mem_add.2 ⟨x, hx, 0, h0H, add_zero x⟩)
      have hnXHcard : #X ≤ #(-X + H) := by
        have h1 : #(-X) ≤ #(-X + H) :=
          Finset.card_le_card (fun x hx => Finset.mem_add.2 ⟨x, hx, 0, h0H, add_zero x⟩)
        rwa [Finset.card_neg] at h1
      have hHpos : 0 < #H := Finset.card_pos.2 ⟨0, h0H⟩
      have hknN : 2 * #X ≤ #(X - X) + #H := by omega
      have hknR : 2 * (#X : ℝ) ≤ (#(X - X) : ℝ) + (#H : ℝ) := by exact_mod_cast hknN
      have hHbig : (t : ℝ) / 3 < (#H : ℝ) := by linarith only [hknR, hcase2]
      have hHdvd : #H ∣ t := by
        have h1 : #H ∣ #((Finset.univ : Finset (ZMod t)) + H) :=
          Finset.card_addStab_dvd_card_add_addStab Finset.univ (X - X)
        have h2 : (Finset.univ : Finset (ZMod t)) + H = Finset.univ :=
          Finset.eq_univ_of_forall fun g =>
            Finset.mem_add.2 ⟨g, Finset.mem_univ g, 0, h0H, add_zero g⟩
        rwa [h2, Finset.card_univ, hcardZMod] at h1
      obtain ⟨k, hk⟩ := hHdvd
      have htlt : t < 3 * #H := by
        have h1 : (t : ℝ) < 3 * (#H : ℝ) := by linarith only [hHbig]
        exact_mod_cast h1
      have hklt : k < 3 := by
        by_contra hcon
        rw [not_lt] at hcon
        have : #H * 3 ≤ #H * k := Nat.mul_le_mul_left _ hcon
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exfalso; rw [h, Nat.mul_zero] at hk; omega
        · exact h
      have hk2 : k = 2 := by
        interval_cases k
        · -- `k = 1`, i.e. `H = univ`, is impossible
          exfalso
          have hHuniv : H = Finset.univ :=
            Finset.eq_univ_of_card _ (by rw [hcardZMod]; omega)
          have hXXuniv : X - X = Finset.univ := by
            refine Finset.eq_univ_of_forall fun g => ?_
            obtain ⟨x, hx⟩ := hXXne
            have h1 : (X - X) + H = X - X := Finset.add_addStab (X - X)
            have h2 : g ∈ (X - X) + H :=
              Finset.mem_add.2 ⟨x, hx, g - x, by rw [hHuniv]; exact Finset.mem_univ _, by abel⟩
            rwa [h1] at h2
          have h3 : (#(X - X) : ℝ) = (t : ℝ) := by
            rw [hXXuniv, Finset.card_univ, hcardZMod]
          have h4 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
          linarith only [h3, hcase2, hcase1R, h4]
        · rfl
      subst hk2
      -- `X` lies in a single coset of `H`
      have hXHle : #(X + H) ≤ t := by
        have h1 := Finset.card_le_univ (X + H)
        rwa [hcardZMod] at h1
      have hXpos : 0 < #X := Finset.card_pos.2 hXne
      obtain ⟨j, hj⟩ := Finset.card_addStab_dvd_card_add_addStab X (X - X)
      rw [← hHdef] at hj
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · exfalso; rw [h, Nat.mul_zero] at hj; omega
        · exact h
      have hjle : j ≤ 2 := by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : #H * 3 ≤ #H * j := Nat.mul_le_mul_left _ hcon
        omega
      have hHR : (t : ℝ) = (#H : ℝ) * 2 := by exact_mod_cast hk
      have hjeq : j = 1 := by
        by_contra hcon
        have hj2 : j = 2 := by omega
        exfalso
        rw [hj2] at hj
        have h1 : (t : ℝ) + (#X : ℝ) ≤ (#(X - X) : ℝ) + (#H : ℝ) := by
          have h2 : t + #X ≤ #(X - X) + #H := by omega
          exact_mod_cast h2
        have h4 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
        linarith only [h1, hcase2, hcase1R, h4, hHR]
      rw [hjeq, Nat.mul_one] at hj
      have hXXH : X - X ⊆ H := by
        intro d hd
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.1 hd
        have hyH : H.image (fun h => y + h) ⊆ X + H := by
          intro z hz
          rw [Finset.mem_image] at hz
          obtain ⟨h, hh, rfl⟩ := hz
          exact Finset.mem_add.2 ⟨y, hy, h, hh, rfl⟩
        have hcardim : #(H.image (fun h => y + h)) = #H :=
          Finset.card_image_of_injective _ (add_right_injective y)
        have heq : H.image (fun h => y + h) = X + H :=
          Finset.eq_of_subset_of_card_le hyH (by omega)
        have hxmem : x ∈ X + H := Finset.mem_add.2 ⟨x, hx, 0, h0H, add_zero x⟩
        rw [← heq, Finset.mem_image] at hxmem
        obtain ⟨h, hh, hxh⟩ := hxmem
        have hxy : x - y = h := by rw [← hxh]; abel
        rwa [hxy]
      -- `H` is the set of even residues
      have hHadd : ∀ ⦃x⦄, x ∈ H → ∀ ⦃y⦄, y ∈ H → x + y ∈ H := by
        intro x hx y hy
        rw [hHdef] at hx hy ⊢
        exact add_mem_addStab hx hy
      have hHneg : ∀ ⦃x⦄, x ∈ H → -x ∈ H := by
        intro x hx
        rw [hHdef] at hx ⊢
        exact neg_mem_addStab hXXne hx
      have hdouble : ∀ g : ZMod t, g + g ∈ H := by
        refine double_mem_of_two_mul_card hHadd hHneg ?_
        rw [hcardZMod]; omega
      have hone : (1 : ZMod t) ∉ H := by
        intro h1
        have hall : ∀ n : ℕ, ((n : ℕ) : ZMod t) ∈ H := by
          intro n
          induction n with
          | zero => simpa using h0H
          | succ k ih =>
              have h2 : ((k : ℕ) : ZMod t) + 1 ∈ H := hHadd ih h1
              have h3 : ((k : ℕ) : ZMod t) + 1 = ((k + 1 : ℕ) : ZMod t) := by push_cast; ring
              rwa [h3] at h2
        have hHuniv : H = Finset.univ := by
          refine Finset.eq_univ_of_forall fun g => ?_
          have h2 := hall g.val
          rwa [ZMod.natCast_zmod_val] at h2
        have h3 : #H = t := by rw [hHuniv, Finset.card_univ, hcardZMod]
        omega
      have hHeven : ∀ c : ZMod t, c ∈ H → Even c.val := by
        intro c hc
        rcases Nat.even_or_odd c.val with he | ho
        · exact he
        · exfalso
          obtain ⟨i, hi⟩ := ho
          have hcv : c = ((c.val : ℕ) : ZMod t) := (ZMod.natCast_zmod_val c).symm
          have hc2 : c = ((i : ℕ) : ZMod t) + ((i : ℕ) : ZMod t) + 1 := by
            rw [hcv, hi]; push_cast; ring
          have h2 : c + -(((i : ℕ) : ZMod t) + ((i : ℕ) : ZMod t)) ∈ H :=
            hHadd hc (hHneg (hdouble _))
          have h3 : c + -(((i : ℕ) : ZMod t) + ((i : ℕ) : ZMod t)) = 1 := by rw [hc2]; ring
          rw [h3] at h2
          exact hone h2
      have hparity : ∀ d : ℤ, ((d : ZMod t) ∈ H) → Even d := by
        intro d hd
        obtain ⟨i, hi⟩ := hHeven _ hd
        have hveq : ((((d : ZMod t).val : ℕ) : ℤ) : ZMod t) = ((d : ℤ) : ZMod t) := by
          push_cast
          exact ZMod.natCast_zmod_val _
        obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ t).1 hveq
        have htH : (t : ℤ) = (#H : ℤ) * 2 := by exact_mod_cast hk
        have hvalcast : (((d : ZMod t).val : ℕ) : ℤ) = (i : ℤ) + (i : ℤ) := by
          rw [hi]; push_cast; ring
        rw [hvalcast, htH] at hc
        exact ⟨(i : ℤ) + (#H : ℤ) * c, by linarith only [hc]⟩
      -- the elements of `A` above `X` all have the same parity
      set AX : Finset ℤ := {a ∈ A | ((a : ℤ) : ZMod t) ∈ X} with hAXdef
      have hAXcard : #X ≤ #AX := by
        have hsub : X ⊆ AX.image (fun a : ℤ => ((a : ℤ) : ZMod t)) := by
          intro x hx
          obtain ⟨a, ha, hax⟩ := mem_projImage.1 (hXS hx)
          exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, by rw [hax]; exact hx⟩, hax⟩
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hAXne : AX.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨a₀, ha₀⟩ := hAXne
      have hsame : ∀ a ∈ AX, Even (a - a₀) := by
        intro a ha
        refine hparity _ ?_
        have hcast : (((a - a₀ : ℤ)) : ZMod t) = ((a : ℤ) : ZMod t) - ((a₀ : ℤ) : ZMod t) := by
          push_cast; ring
        rw [hcast]
        exact hXXH (Finset.mem_sub.2 ⟨_, (Finset.mem_filter.1 ha).2, _,
          (Finset.mem_filter.1 ha₀).2, rfl⟩)
      have hEA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ) := fun a ha => Finset.mem_Icc.1 (hA ha)
      rcases Int.even_or_odd a₀ with heven | hodd
      · -- all of `A` above `X` is even: too many even elements, contradicting the triple count
        exfalso
        have hAXE : AX ⊆ {a ∈ A | Even a} := by
          intro a ha
          refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 ha).1, ?_⟩
          have h1 := hsame a ha
          rw [Int.even_iff] at h1 heven ⊢
          omega
        set E : Finset ℤ := {a ∈ A | Even a} with hEdef
        have hEcard : 12 * (N : ℝ) / 25 ≤ (#E : ℝ) := by
          have h1 : (#X : ℝ) ≤ (#E : ℝ) := by
            exact_mod_cast le_trans hAXcard (Finset.card_le_card hAXE)
          linarith only [h1, hXcard, hAcard, hρN]
        have hEA' : ∀ a ∈ E, 1 ≤ a ∧ a ≤ (N : ℤ) := fun a ha => hEA a (Finset.mem_filter.1 ha).1
        set E' : Finset ℕ := E.image Int.toNat with hE'def
        have hinj : Set.InjOn Int.toNat (E : Set ℤ) := by
          intro a ha b hb hab
          have h1 := hEA' a (by simpa using ha)
          have h2 := hEA' b (by simpa using hb)
          omega
        have hE'card : #E' = #E := Finset.card_image_of_injOn hinj
        have hE'mem : ∀ x ∈ E', ((x : ℕ) : ℤ) ∈ E := by
          intro x hx
          rw [hE'def, Finset.mem_image] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          have h1 := hEA' a ha
          have h2 : ((a.toNat : ℕ) : ℤ) = a := by omega
          rw [h2]; exact ha
        have hE'sub : E' ⊆ {x ∈ Finset.Icc 1 N | Even x} := by
          intro x hx
          have h1 := hE'mem x hx
          have h2 := hEA' _ h1
          have h3 : Even (((x : ℕ) : ℤ)) := (Finset.mem_filter.1 h1).2
          rw [Int.even_iff] at h3
          refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
          rw [Nat.even_iff]; omega
        have hN100 : 100 ≤ N := by
          have h1 : (100 : ℝ) ≤ (N : ℝ) := by linarith only [hNbig]
          exact_mod_cast h1
        have hlem := lem_evenSetTriples hN100 hE'sub (by rw [hE'card]; linarith only [hEcard])
        rw [schurTriples_eq_addTriples] at hlem
        have hmono : addTriples E' ≤ addTriples A := by
          simp only [addTriples]
          refine Finset.card_le_card_of_injOn
            (fun q : ℕ × ℕ × ℕ => ((q.1 : ℤ), ((q.2.1 : ℤ), (q.2.2 : ℤ)))) ?_ ?_
          · intro q hq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hq
            obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hq
            refine Finset.mem_coe.2 (Finset.mem_filter.2
              ⟨Finset.mem_product.2 ⟨(Finset.mem_filter.1 (hE'mem _ h1)).1,
                Finset.mem_product.2 ⟨(Finset.mem_filter.1 (hE'mem _ h2)).1,
                  (Finset.mem_filter.1 (hE'mem _ h3)).1⟩⟩, ?_⟩)
            show ((q.1 : ℤ)) + ((q.2.1 : ℤ)) = ((q.2.2 : ℤ))
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h4
          · intro q _ q' _ hqq
            have h1 : (q.1 : ℤ) = (q'.1 : ℤ) := congrArg Prod.fst hqq
            have h2 : (q.2.1 : ℤ) = (q'.2.1 : ℤ) := congrArg (fun p => p.2.1) hqq
            have h3 : (q.2.2 : ℤ) = (q'.2.2 : ℤ) := congrArg (fun p => p.2.2) hqq
            exact Prod.ext (by exact_mod_cast h1)
              (Prod.ext (by exact_mod_cast h2) (by exact_mod_cast h3))
        have h5 : (addTriples E' : ℝ) ≤ (addTriples A : ℝ) := by exact_mod_cast hmono
        have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
        have h6 : ε * (N : ℝ) ^ 2 ≤ (1 / 10 ^ 32) * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hε0 hN2.le
        linarith only [hlem, h5, htr, h6, hN2]
      · -- all of `A` above `X` is odd: few even elements
        right
        have hdisj : Disjoint {a ∈ A | Even a} AX := by
          rw [Finset.disjoint_left]
          intro a ha haX
          have h1 := hsame a haX
          have h2 : Even a := (Finset.mem_filter.1 ha).2
          rw [Int.even_iff] at h1 h2
          rw [Int.odd_iff] at hodd
          omega
        have hunion : {a ∈ A | Even a} ∪ AX ⊆ A := by
          intro a ha
          rcases Finset.mem_union.1 ha with h | h
          · exact (Finset.mem_filter.1 h).1
          · exact (Finset.mem_filter.1 h).1
        have hsum : #{a ∈ A | Even a} + #AX ≤ #A := by
          have h1 := Finset.card_union_of_disjoint hdisj
          have h2 := Finset.card_le_card hunion
          omega
        have hsumR : (#{a ∈ A | Even a} : ℝ) + (#X : ℝ) ≤ (#A : ℝ) := by
          have h1 : #{a ∈ A | Even a} + #X ≤ #A := by omega
          exact_mod_cast h1
        linarith only [hsumR, hXcard]

end Prop7

/-! ## Axiom audit -/

#print axioms CameronErdos.neg_mem_addStab
#print axioms CameronErdos.add_mem_addStab
#print axioms CameronErdos.double_mem_of_two_mul_card
#print axioms CameronErdos.sub_eq_univ_of_card_lt
#print axioms CameronErdos.addTriples_mono
#print axioms CameronErdos.prop7

end CameronErdos
