import Mathlib
import JSP573.External.Erdos703

/-!
# Frankl–Füredi 1984: basic definitions and the disjointness count

Setting (Frankl–Füredi, *On hypergraphs without two edges intersecting in a given number of
vertices*, JCTA 36 (1984) 230–236): `X = range n`, `t ≥ 1`, and a family `𝓕` of subsets of `X`
with `#(A ∩ B) ≠ t` for all `A, B ∈ 𝓕` (`Erdos703.AvoidsRIntersection t 𝓕`, which also excludes
members of size `t` because `A = B` is allowed).

* `level 𝓕 i` — members of size `i` (`𝓕_i` in the paper), `f_i = #(level 𝓕 i)`.
* `shadow g 𝓕` — all `g`-element subsets of members (`∂_g 𝓕`).
* `complFamily n 𝓕` — complements `range n \ A` of members.
* `inclVec n g A` — the row of the containment matrix `M(𝓕, g)` belonging to `A`.
* `lcmUpTo t = lcm (1, …, t)` and `qBound t = t + 1 + lcmUpTo t` (the paper's `q(t)`).
-/

open Finset

namespace FranklFuredi

/-- The members of `𝓕` of size `i`. -/
def level (𝓕 : Finset (Finset ℕ)) (i : ℕ) : Finset (Finset ℕ) := 𝓕.filter fun A ↦ #A = i

/-- The `g`-shadow of `𝓕`: all `g`-element subsets of members of `𝓕`. -/
def shadow (g : ℕ) (𝓕 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝓕.biUnion fun A ↦ A.powersetCard g

/-- The family of complements `range n \ A`, `A ∈ 𝓕`. -/
def complFamily (n : ℕ) (𝓕 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝓕.image fun A ↦ range n \ A

/-- `lcm (1, …, t)`. -/
def lcmUpTo (t : ℕ) : ℕ := (Finset.Icc 1 t).lcm id

/-- The paper's threshold `q(t) = 1 + t + lcm (1, …, t)`. -/
def qBound (t : ℕ) : ℕ := t + 1 + lcmUpTo t

/-- `𝓕` is a family of `h`-element subsets of `range n`. -/
def IsUniformOn (n h : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop := ∀ A ∈ 𝓕, A ⊆ range n ∧ #A = h

/-- The containment row of `A`: the indicator, on the `g`-subsets of `range n`, of `S ⊆ A`. -/
def inclVec (n g : ℕ) (A : Finset ℕ) : (range n).powersetCard g → ℚ :=
  fun S ↦ if (S : Finset ℕ) ⊆ A then 1 else 0

lemma mem_level {𝓕 : Finset (Finset ℕ)} {i : ℕ} {A : Finset ℕ} :
    A ∈ level 𝓕 i ↔ A ∈ 𝓕 ∧ #A = i := by
  simp [level]

lemma mem_shadow {g : ℕ} {𝓕 : Finset (Finset ℕ)} {G : Finset ℕ} :
    G ∈ shadow g 𝓕 ↔ ∃ A ∈ 𝓕, G ⊆ A ∧ #G = g := by
  simp [shadow, mem_powersetCard]

/-- Members of size `t` are excluded, since `#(A ∩ A) = #A`. -/
theorem level_eq_empty_of_avoids {t : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hav : Erdos703.AvoidsRIntersection t 𝓕) : level 𝓕 t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro A hA
  rw [mem_level] at hA
  exact hav A hA.1 A hA.1 (by rw [Finset.inter_self, hA.2])

/-- Trivial bound `f_i ≤ C(n, i)` for a family of subsets of `range n`. -/
theorem level_card_le_choose (n i : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) : #(level 𝓕 i) ≤ n.choose i := by
  have hsub : level 𝓕 i ⊆ (range n).powersetCard i := by
    intro A hA
    rw [mem_level] at hA
    exact Finset.mem_powersetCard.mpr ⟨h𝓕 A hA.1, hA.2⟩
  calc #(level 𝓕 i) ≤ #((range n).powersetCard i) := Finset.card_le_card hsub
    _ = n.choose i := by rw [Finset.card_powersetCard, Finset.card_range]

/-- Proposition 3.1 of Frankl–Füredi together with its counting consequence: for `t < i ≤ n + t`,
the `(i - t)`-shadow of `𝓕_i` and the complements of `𝓕_{n + t - i}` are disjoint families of
`(i - t)`-subsets of `range n`, hence `#∂_{i-t} 𝓕_i + f_{n+t-i} ≤ C(n, i - t)`. (The bound
`i ≤ n + t` is needed because of truncated subtraction; it is automatic for member sizes.) -/
theorem shadow_card_add_level_card_le (n t i : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (hti : t < i)
    (hin : i ≤ n + t) :
    #(shadow (i - t) (level 𝓕 i)) + #(level 𝓕 (n + t - i)) ≤ n.choose (i - t) := by
  classical
  set S₁ : Finset (Finset ℕ) := shadow (i - t) (level 𝓕 i) with hS₁
  set S₂ : Finset (Finset ℕ) := complFamily n (level 𝓕 (n + t - i)) with hS₂
  have hcompl : ∀ B ∈ level 𝓕 (n + t - i), B ⊆ range n ∧ #B = n + t - i := by
    intro B hB
    rw [mem_level] at hB
    exact ⟨h𝓕 B hB.1, hB.2⟩
  have hcard₂ : #S₂ = #(level 𝓕 (n + t - i)) := by
    rw [hS₂, complFamily]
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB hAB
    have hA' : A ⊆ range n := (hcompl A hA).1
    have hB' : B ⊆ range n := (hcompl B hB).1
    have hAB' : range n \ A = range n \ B := hAB
    calc A = range n \ (range n \ A) := (Finset.sdiff_sdiff_eq_self hA').symm
      _ = range n \ (range n \ B) := by rw [hAB']
      _ = B := Finset.sdiff_sdiff_eq_self hB'
  have hsub₁ : S₁ ⊆ (range n).powersetCard (i - t) := by
    intro G hG
    rw [hS₁, mem_shadow] at hG
    obtain ⟨A, hA, hGA, hGcard⟩ := hG
    rw [mem_level] at hA
    exact Finset.mem_powersetCard.mpr ⟨hGA.trans (h𝓕 A hA.1), hGcard⟩
  have hsub₂ : S₂ ⊆ (range n).powersetCard (i - t) := by
    intro G hG
    rw [hS₂, complFamily, Finset.mem_image] at hG
    obtain ⟨B, hB, rfl⟩ := hG
    obtain ⟨hBsub, hBcard⟩ := hcompl B hB
    refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hBsub, Finset.card_range, hBcard]
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro G hG₁ hG₂
    rw [hS₁, mem_shadow] at hG₁
    obtain ⟨A, hA, hGA, hGcard⟩ := hG₁
    rw [mem_level] at hA
    obtain ⟨hA𝓕, hAcard⟩ := hA
    rw [hS₂, complFamily, Finset.mem_image] at hG₂
    obtain ⟨B, hB, hGB⟩ := hG₂
    have hB𝓕 : B ∈ 𝓕 := (mem_level.mp hB).1
    have hAsub : A ⊆ range n := h𝓕 A hA𝓕
    have hBA : B ∩ A = A \ G := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxB, hxA⟩
        refine ⟨hxA, ?_⟩
        rw [← hGB]
        simp only [Finset.mem_sdiff, not_and, not_not]
        exact fun _ ↦ hxB
      · rintro ⟨hxA, hxG⟩
        refine ⟨?_, hxA⟩
        rw [← hGB] at hxG
        simp only [Finset.mem_sdiff, not_and, not_not] at hxG
        exact hxG (hAsub hxA)
    refine hav B hB𝓕 A hA𝓕 ?_
    rw [hBA, Finset.card_sdiff_of_subset hGA, hAcard, hGcard]
    omega
  calc #S₁ + #(level 𝓕 (n + t - i)) = #S₁ + #S₂ := by rw [hcard₂]
    _ = #(S₁ ∪ S₂) := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #((range n).powersetCard (i - t)) :=
        Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
    _ = n.choose (i - t) := by rw [Finset.card_powersetCard, Finset.card_range]

/-- Every `m > lcm (1, …, t)` has a prime-power divisor exceeding `t`
(otherwise every prime-power part of `m` divides the lcm, so `m` does). -/
private lemma lcmUpTo_ne_zero (t : ℕ) : lcmUpTo t ≠ 0 := by
  rw [lcmUpTo, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, hx0⟩
  rw [Finset.mem_Icc] at hx
  simp only [id_eq] at hx0
  omega

theorem exists_primePow_dvd_of_lcmUpTo_lt (t m : ℕ) (hm : lcmUpTo t < m) :
    ∃ p s : ℕ, p.Prime ∧ 0 < s ∧ p ^ s ∣ m ∧ t < p ^ s := by
  by_contra hcon
  have hcon' : ∀ p s : ℕ, p.Prime → 0 < s → p ^ s ∣ m → p ^ s ≤ t := by
    intro p s hp hs hps
    by_contra hlt
    exact hcon ⟨p, s, hp, hs, hps, Nat.lt_of_not_le hlt⟩
  have hL0 : lcmUpTo t ≠ 0 := lcmUpTo_ne_zero t
  have hm0 : m ≠ 0 := by omega
  have hdvd : m ∣ lcmUpTo t := by
    rw [← Nat.factorization_le_iff_dvd hm0 hL0, Finsupp.le_iff]
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hepos : 0 < m.factorization p :=
      hpp.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
    have hpe : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    have hmem : p ^ m.factorization p ∈ Finset.Icc 1 t :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos, hcon' p _ hpp hepos hpe⟩
    have hdd : p ^ m.factorization p ∣ lcmUpTo t := Finset.dvd_lcm hmem
    exact (hpp.pow_dvd_iff_le_factorization hL0).mp hdd
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hdvd
  omega

end FranklFuredi
