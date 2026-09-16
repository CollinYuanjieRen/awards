import Mathlib
import JSP573.FF.Basic
import JSP573.FF.FranklSinghi
import JSP573.FF.Shadow

/-!
# Frankl–Füredi 1984, Section 3: the level inequalities

For a family `𝓕` of subsets of `range n` with `#(A ∩ B) ≠ t` for all `A, B ∈ 𝓕` (`t ≥ 1`),
write `f_i = #(level 𝓕 i)`.

* `level_inequality` (inequality (3) of the paper, integer form): for `qBound t ≤ i` and
  `2 i ≤ n + t`, `f_i · i + f_{n+t-i} · (i - t) ≤ C(n, i - t) · (i - t)`. It combines the
  disjointness count (`shadow_card_add_level_card_le`), the Frankl–Singhi rank theorem (applied to
  `level 𝓕 i`, which is `i`-uniform; `i - t > lcm(1..t)` supplies the prime-power divisor) and
  the shadow inequality with `g = i - t`, using `C(2i-t-1, i-t) · (i-t) = C(2i-t-1, i) · i`.
* `ffBound n t` is the closed form of `#𝓕*(n, t)`.
* `card_le_ffBound_add_middle`: `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} f_i` once
  `qBound t ≤ (n + t) / 2` (sum the level inequalities over the pairs `(i, n + t - i)`, use
  `f_i ≤ C(n, i)` for `i < t`, `f_t = 0`, the self-paired middle level for `n + t` even, and the
  trivial bound on the top levels).
* `card_forbidden_level`: if `A₀ ∈ 𝓕` with `t < #A₀`, then level `b` omits all the
  `C(#A₀, t) · C(n - #A₀, b - t)` sets `B` of size `b` with `#(B ∩ A₀) = t`.
-/

open Finset

namespace FranklFuredi

/-- The closed form of `#𝓕*(n, t)`: sets of size `< t`, sets of size `> (n + t) / 2`, and, when
`n + t` is even, the sets of size `(n + t) / 2` avoiding the fixed element `0`. -/
def ffBound (n t : ℕ) : ℕ :=
  (∑ i ∈ Finset.range t, n.choose i) + (∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i) +
    (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0)

/-- Counting the subsets of `range n` selected by a predicate that depends only on the
cardinality: the answer is the sum of the binomial coefficients over the admissible sizes. -/
private lemma card_powerset_filter_card (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    #((range n).powerset.filter fun A ↦ Q #A) = ∑ i ∈ (range (n + 1)).filter Q, n.choose i := by
  classical
  have hmem : ∀ A ∈ (range n).powerset.filter fun A ↦ Q #A, #A ∈ range (n + 1) := by
    intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    have h := Finset.card_le_card hA.1
    rw [Finset.card_range] at h
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmem, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hQ : Q i
  · rw [ite_eq_left hQ]
    have h : (((range n).powerset.filter fun A ↦ Q #A).filter fun A ↦ #A = i)
        = (range n).powersetCard i := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ hQ⟩, h.2⟩⟩
    rw [h, Finset.card_powersetCard, Finset.card_range]
  · rw [ite_eq_right hQ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro A hA h
    rw [Finset.mem_filter] at hA
    exact hQ (h ▸ hA.2)

/-- Binomial coefficients above `n` vanish, so `∑_{i < t} C(n, i)` only sees indices `≤ n`. -/
private lemma sum_filter_lt_choose (n t : ℕ) :
    ∑ i ∈ (range (n + 1)).filter (fun i ↦ i < t), n.choose i = ∑ i ∈ range t, n.choose i := by
  refine Finset.sum_subset (fun x hx ↦ ?_) (fun x hx hx' ↦ ?_)
  · rw [Finset.mem_filter] at hx
    exact Finset.mem_range.mpr hx.2
  · rw [Finset.mem_range] at hx
    have hxn : n < x := by
      by_contra hc
      exact hx' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hx⟩)
    exact Nat.choose_eq_zero_of_lt hxn

/-- The indices `i ≤ n` with `m < i` form `Ioc m n`. -/
private lemma filter_lt_range_eq_Ioc (n m : ℕ) :
    (range (n + 1)).filter (fun i ↦ m < i) = Finset.Ioc m n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  omega

/-- The subsets of `range n` of size `> (n + t) / 2` or `< t` are counted by the first two
summands of `ffBound n t`. -/
private lemma card_filter_big_or_small (n t : ℕ) :
    #((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t) =
      (∑ i ∈ range t, n.choose i) + ∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i := by
  classical
  have hdisj : Disjoint ((range (n + 1)).filter fun i ↦ (n + t) / 2 < i)
      ((range (n + 1)).filter fun i ↦ i < t) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter, Finset.mem_range] at hi hi'
    omega
  rw [card_powerset_filter_card n fun i ↦ (n + t) / 2 < i ∨ i < t, Finset.filter_or,
    Finset.sum_union hdisj, filter_lt_range_eq_Ioc, sum_filter_lt_choose]
  omega

/-- The subsets of `range n` of a given size avoiding `0` number `C(n - 1, m)`. -/
private lemma card_filter_notMem_zero (n m : ℕ) (hn : 1 ≤ n) :
    #((range n).powerset.filter fun A ↦ #A = m ∧ 0 ∉ A) = (n - 1).choose m := by
  classical
  have h : ((range n).powerset.filter fun A ↦ #A = m ∧ 0 ∉ A)
      = ((range n).erase 0).powersetCard m := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
      Finset.subset_erase]
    tauto
  rw [h, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_range.mpr hn),
    Finset.card_range]

/-- `#(franklFurediOdd n t) = ffBound n t` when `n + t` is odd. -/
theorem card_franklFurediOdd (n t : ℕ) (hodd : (n + t) % 2 = 1) :
    #(Erdos703.franklFurediOdd n t) = ffBound n t := by
  rw [Erdos703.franklFurediOdd, card_filter_big_or_small, ffBound,
    ite_eq_right (show ¬(n + t) % 2 = 0 by omega), Nat.add_zero]

/-- `#(franklFurediEven n t) = ffBound n t` when `n + t` is even and `1 ≤ n`. -/
theorem card_franklFurediEven (n t : ℕ) (hn : 1 ≤ n) (heven : (n + t) % 2 = 0) :
    #(Erdos703.franklFurediEven n t) = ffBound n t := by
  classical
  have hsplit : Erdos703.franklFurediEven n t =
      ((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t) ∪
        ((range n).powerset.filter fun A ↦ #A = (n + t) / 2 ∧ 0 ∉ A) := by
    rw [Erdos703.franklFurediEven, ← Finset.filter_or]
    refine Finset.filter_congr fun A hA ↦ ?_
    rw [Finset.mem_powerset] at hA
    have hAn : #A ≤ n := by
      have h := Finset.card_le_card hA
      rwa [Finset.card_range] at h
    rw [Finset.filter_ne']
    by_cases h0 : 0 ∈ A
    · have h1 : 1 ≤ #A := Finset.card_pos.mpr ⟨0, h0⟩
      rw [Finset.card_erase_of_mem h0]
      simp only [h0, not_true_eq_false, and_false, or_false]
      omega
    · rw [Finset.erase_eq_of_notMem h0]
      simp only [h0, not_false_eq_true, and_true]
      omega
  have hdisj : Disjoint ((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t)
      ((range n).powerset.filter fun A ↦ #A = (n + t) / 2 ∧ 0 ∉ A) := by
    rw [Finset.disjoint_left]
    intro A hA hA'
    rw [Finset.mem_filter, Finset.mem_powerset] at hA hA'
    have hAn : #A ≤ n := by
      have h := Finset.card_le_card hA.1
      rwa [Finset.card_range] at h
    obtain ⟨hA2, -⟩ := hA'.2
    have hA1 := hA.2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_filter_big_or_small,
    card_filter_notMem_zero n _ hn, ffBound, ite_eq_left heven]

/-- The binomial identity `C(2i - t - 1, i - t) · (i - t) = C(2i - t - 1, i) · i` for `t < i`. -/
private lemma choose_mul_sub (t i : ℕ) (hti : t < i) :
    (2 * i - t - 1).choose (i - t) * (i - t) = (2 * i - t - 1).choose i * i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = t + (k + 1) := ⟨i - t - 1, by omega⟩
  have h1 : 2 * (t + (k + 1)) - t - 1 = t + 2 * k + 1 := by omega
  have h2 : t + (k + 1) - t = k + 1 := by omega
  have h3 : t + (k + 1) = t + k + 1 := by omega
  have e1 : (t + 2 * k + 1) * (t + 2 * k).choose k = (t + 2 * k + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (t + 2 * k) k
  have e2 : (t + 2 * k + 1) * (t + 2 * k).choose (t + k)
      = (t + 2 * k + 1).choose (t + k + 1) * (t + k + 1) :=
    Nat.add_one_mul_choose_eq (t + 2 * k) (t + k)
  have e3 : (t + 2 * k).choose k = (t + 2 * k).choose (t + k) := by
    rw [← Nat.choose_symm (show k ≤ t + 2 * k by omega)]
    congr 1
    omega
  rw [h1, h2, h3, ← e1, ← e2, e3]

/-- Inequality (3): `f_i · i + f_{n+t-i} · (i - t) ≤ C(n, i - t) · (i - t)`. -/
theorem level_inequality (n t i : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hqi : qBound t ≤ i)
    (hi : 2 * i ≤ n + t) :
    #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) ≤ n.choose (i - t) * (i - t) := by
  have _ht : 0 < t := ht
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hti : t < i := by omega
  have hlt : lcmUpTo t < i - t := by omega
  obtain ⟨p, s, hp, hs, hdvd, hpt⟩ := exists_primePow_dvd_of_lcmUpTo_lt t (i - t) hlt
  have hU : IsUniformOn n i (level 𝓕 i) := by
    intro A hA
    rw [mem_level] at hA
    exact ⟨h𝓕 A hA.1, hA.2⟩
  have hav' : ∀ A ∈ level 𝓕 i, ∀ B ∈ level 𝓕 i, A ≠ B → #(A ∩ B) ≠ t := by
    intro A hA B hB _
    exact hav A (mem_level.mp hA).1 B (mem_level.mp hB).1
  have hli := frankl_singhi n i t p s hp hs hdvd hpt hti (level 𝓕 i) hU hav'
  have hshadow := shadow_card_mul_choose_ge n i t (i - t) (level 𝓕 i) hU hli (by omega)
    (by omega) (by omega)
  have hNpos : 0 < (2 * i - t - 1).choose i := Nat.choose_pos (by omega)
  have hitpos : (0 : ℚ) < ((i - t : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < i - t by omega)
  have hcast : ((2 * i - t - 1).choose (i - t) : ℚ) * ((i - t : ℕ) : ℚ)
      = ((2 * i - t - 1).choose i : ℚ) * (i : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℚ)) (choose_mul_sub t i hti)
  have step := mul_le_mul_of_nonneg_right hshadow hitpos.le
  rw [mul_assoc, hcast] at step
  have hQ : ((#(level 𝓕 i) * i : ℕ) : ℚ) * ((2 * i - t - 1).choose i : ℚ)
      ≤ ((#(shadow (i - t) (level 𝓕 i)) * (i - t) : ℕ) : ℚ)
        * ((2 * i - t - 1).choose i : ℚ) := by
    push_cast
    nlinarith [step]
  have hN : #(level 𝓕 i) * i * (2 * i - t - 1).choose i
      ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) * (2 * i - t - 1).choose i := by
    exact_mod_cast hQ
  have key : #(level 𝓕 i) * i ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) :=
    Nat.le_of_mul_le_mul_right hN hNpos
  have hdisjc := shadow_card_add_level_card_le n t i h𝓕 hav hti (by omega)
  calc #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t)
      ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) + #(level 𝓕 (n + t - i)) * (i - t) := by omega
    _ = (#(shadow (i - t) (level 𝓕 i)) + #(level 𝓕 (n + t - i))) * (i - t) := by ring
    _ ≤ n.choose (i - t) * (i - t) := Nat.mul_le_mul_right _ hdisjc

/-- The paired form of inequality (3): `f_i + f_{n+t-i} ≤ C(n, n + t - i)`. -/
private lemma level_add_level_le (n t i : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hqi : qBound t ≤ i)
    (hi : 2 * i ≤ n + t) :
    #(level 𝓕 i) + #(level 𝓕 (n + t - i)) ≤ n.choose (n + t - i) := by
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hti : t < i := by omega
  have h3 := level_inequality n t i h𝓕 hav ht hqi hi
  have hle : (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t) ≤ n.choose (i - t) * (i - t) := by
    have hstep : (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t)
        ≤ #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) := by
      have : #(level 𝓕 i) * (i - t) ≤ #(level 𝓕 i) * i :=
        Nat.mul_le_mul_left _ (by omega)
      calc (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t)
          = #(level 𝓕 i) * (i - t) + #(level 𝓕 (n + t - i)) * (i - t) := by ring
        _ ≤ #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) := by omega
    omega
  have hfin := Nat.le_of_mul_le_mul_right hle (show 0 < i - t by omega)
  have hch : n.choose (n + t - i) = n.choose (i - t) := by
    rw [show n + t - i = n - (i - t) by omega]
    exact Nat.choose_symm (by omega)
  rw [hch]
  exact hfin

/-- The self-paired middle level when `n + t` is even: `f_{(n+t)/2} ≤ C(n - 1, (n+t)/2)`. -/
private lemma level_middle_le (n t : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hq : qBound t ≤ (n + t) / 2)
    (heven : (n + t) % 2 = 0) :
    #(level 𝓕 ((n + t) / 2)) ≤ (n - 1).choose ((n + t) / 2) := by
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  set m := (n + t) / 2 with hmdef
  have hqm : t + 1 ≤ m := by omega
  have hnm : n + t - m = m := by omega
  have hn : 1 ≤ n := by omega
  have h3 := level_inequality n t m h𝓕 hav ht hq (by omega)
  rw [hnm] at h3
  have hkey : #(level 𝓕 m) * n ≤ n.choose (m - t) * (m - t) := by
    have hcomb : #(level 𝓕 m) * m + #(level 𝓕 m) * (m - t) = #(level 𝓕 m) * n := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  have hid : n.choose (m - t) * (m - t) = n * (n - 1).choose m := by
    obtain ⟨k, hk⟩ : ∃ k, m - t = k + 1 := ⟨m - t - 1, by omega⟩
    have hn1 : n - 1 + 1 = n := by omega
    have e : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
      have h := Nat.add_one_mul_choose_eq (n - 1) k
      rw [hn1] at h
      exact h
    have hsym : (n - 1).choose k = (n - 1).choose m := by
      rw [← Nat.choose_symm (show k ≤ n - 1 by omega)]
      congr 1
      omega
    rw [hk, ← e, hsym]
  rw [hid, Nat.mul_comm] at hkey
  exact Nat.le_of_mul_le_mul_left hkey hn

/-- `Ico a (b + 1) = Icc a b`. -/
private lemma Ico_succ_eq_Icc (a b : ℕ) : Finset.Ico a (b + 1) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- `Icc (a + 1) b = Ioc a b`. -/
private lemma Icc_succ_eq_Ioc (a b : ℕ) : Finset.Icc (a + 1) b = Finset.Ioc a b := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- `Ico (a + 1) b = Ioo a b`. -/
private lemma Ico_succ_eq_Ioo (a b : ℕ) : Finset.Ico (a + 1) b = Finset.Ioo a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Ioo]
  omega

/-- Reflecting an index range in `N`: `i ↦ N - i` is a bijection `Icc a b → Icc (N - b) (N - a)`. -/
private lemma sum_Icc_reflect (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.Icc (N - b) (N - a), g j = ∑ i ∈ Finset.Icc a b, g (N - i) := by
  classical
  have hinj : ∀ x ∈ Finset.Icc a b, ∀ y ∈ Finset.Icc a b, N - x = N - y → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    omega
  rw [← Finset.sum_image hinj]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro hx
    refine ⟨N - x, ?_, ?_⟩ <;> omega
  · rintro ⟨i, hi, hix⟩
    omega

/-- The level decomposition behind inequality (4): low levels are bounded by binomials, level `t`
is empty, the levels below `qBound t` are kept, the levels in `[qBound t, n + t - qBound t]` are
grouped into the pairs `(i, n + t - i)` (with the self-paired middle level for `n + t` even), and
the top levels are bounded by binomials. -/
private lemma card_le_pair_sum (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ (n + t) / 2) :
    #𝓕 ≤ (∑ i ∈ range t, n.choose i)
        + (∑ i ∈ Finset.Icc (qBound t) (n + t - (n + t) / 2 - 1),
            (#(level 𝓕 i) + #(level 𝓕 (n + t - i))))
        + (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
        + (∑ i ∈ Finset.Ioc (n + t - qBound t) n, n.choose i)
        + ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hmu : m ≤ u := by omega
  have hun : u ≤ n := by omega
  have hcard : #𝓕 = ∑ i ∈ Finset.Ico 0 (n + 1), #(level 𝓕 i) := by
    rw [← Finset.range_eq_Ico]
    simp only [level]
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro A hA
    have h := Finset.card_le_card (h𝓕 A hA)
    rw [Finset.card_range] at h
    exact Finset.mem_range.mpr (by omega)
  have hIco : ∀ a b c : ℕ, a ≤ b → b ≤ c →
      (∑ i ∈ Finset.Ico a b, #(level 𝓕 i)) + (∑ i ∈ Finset.Ico b c, #(level 𝓕 i))
        = ∑ i ∈ Finset.Ico a c, #(level 𝓕 i) :=
    fun a b c hab hbc ↦ Finset.sum_Ico_consecutive _ hab hbc
  have e1 := hIco 0 t (n + 1) (by omega) (by omega)
  have e2 := hIco t (t + 1) (n + 1) (by omega) (by omega)
  have e3 := hIco (t + 1) q (n + 1) (by omega) (by omega)
  have e4 := hIco q (u + 1) (n + 1) (by omega) (by omega)
  have e5 := hIco q (m + 1) (u + 1) (by omega) (by omega)
  have hB1 : ∑ i ∈ Finset.Ico 0 t, #(level 𝓕 i) ≤ ∑ i ∈ range t, n.choose i := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
  have hB2 : ∑ i ∈ Finset.Ico t (t + 1), #(level 𝓕 i) = 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl t), level_eq_empty_of_avoids hav]
    simp
  have hB3 : ∑ i ∈ Finset.Ico (t + 1) q, #(level 𝓕 i)
      = ∑ i ∈ Finset.Ioo t q, #(level 𝓕 i) := by rw [Ico_succ_eq_Ioo]
  have hB6 : ∑ i ∈ Finset.Ico (u + 1) (n + 1), #(level 𝓕 i)
      ≤ ∑ i ∈ Finset.Ioc u n, n.choose i := by
    rw [Ico_succ_eq_Icc, Icc_succ_eq_Ioc]
    exact Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
  have hB4 : ∑ i ∈ Finset.Ico q (m + 1), #(level 𝓕 i)
      = (∑ i ∈ Finset.Icc q m', #(level 𝓕 i))
        + (if (n + t) % 2 = 0 then #(level 𝓕 m) else 0) := by
    split_ifs with hpar
    · have hset : Finset.Ico q m = Finset.Icc q m' := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [Finset.sum_Ico_succ_top (show q ≤ m by omega), hset]
    · have hset : Finset.Ico q (m + 1) = Finset.Icc q m' := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [hset, Nat.add_zero]
  have hB5 : ∑ i ∈ Finset.Ico (m + 1) (u + 1), #(level 𝓕 i)
      = ∑ i ∈ Finset.Icc q m', #(level 𝓕 (n + t - i)) := by
    have hr := sum_Icc_reflect (n + t) q m' (by omega) (by omega) (fun j ↦ #(level 𝓕 j))
    rw [show n + t - m' = m + 1 by omega, ← hudef] at hr
    rw [Ico_succ_eq_Icc]
    exact hr
  have hsum : (∑ i ∈ Finset.Icc q m', #(level 𝓕 i))
      + (∑ i ∈ Finset.Icc q m', #(level 𝓕 (n + t - i)))
      = ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) :=
    Finset.sum_add_distrib.symm
  omega

/-- `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} f_i` once `qBound t ≤ (n + t) / 2`. -/
theorem card_le_ffBound_add_middle (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ (n + t) / 2) :
    #𝓕 ≤ ffBound n t + ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have core := card_le_pair_sum n t h𝓕 hav ht hq
  have hmid : (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
      ≤ (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0) := by
    split_ifs with hpar
    · exact level_middle_le n t h𝓕 hav ht hq hpar
    · exact le_refl 0
  rw [ffBound]
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hmu : m ≤ u := by omega
  have hun : u ≤ n := by omega
  have hpair : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      ≤ ∑ i ∈ Finset.Ioc m u, n.choose i := by
    have hb : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
        ≤ ∑ i ∈ Finset.Icc q m', n.choose (n + t - i) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [Finset.mem_Icc] at hi
      exact level_add_level_le n t i h𝓕 hav ht (by omega) (by omega)
    have hr := sum_Icc_reflect (n + t) q m' (by omega) (by omega) (fun j ↦ n.choose j)
    rw [show n + t - m' = m + 1 by omega, ← hudef] at hr
    rw [← Icc_succ_eq_Ioc]
    omega
  have hIocC : (∑ i ∈ Finset.Ioc m u, n.choose i) + (∑ i ∈ Finset.Ioc u n, n.choose i)
      = ∑ i ∈ Finset.Ioc m n, n.choose i := Finset.sum_Ioc_consecutive _ hmu hun
  omega

/-- The refined form of inequality (4) keeping the pair `(n + t - (m + 1), m + 1)`
(`m = (n + t) / 2`) unbounded: its binomial bound `C(n, m + 1)` moves to the left. -/
theorem card_le_ffBound_add_middle_sub (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ n + t - (n + t) / 2 - 1) (hn : (n + t) / 2 + 1 ≤ n) :
    #𝓕 + n.choose ((n + t) / 2 + 1) ≤
      ffBound n t + (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i)) +
        (#(level 𝓕 (n + t - ((n + t) / 2 + 1))) + #(level 𝓕 ((n + t) / 2 + 1))) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hq' : qBound t ≤ (n + t) / 2 := by omega
  have core := card_le_pair_sum n t h𝓕 hav ht hq'
  have hmid : (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
      ≤ (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0) := by
    split_ifs with hpar
    · exact level_middle_le n t h𝓕 hav ht hq' hpar
    · exact le_refl 0
  rw [ffBound]
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hqm' : q ≤ m' := hq
  have hmu : m + 1 ≤ u := by omega
  have hun : u ≤ n := by omega
  rw [show n + t - (m + 1) = m' by omega]
  have hsplitlast : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      = (∑ i ∈ Finset.Ico q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i))))
        + (#(level 𝓕 m') + #(level 𝓕 (m + 1))) := by
    rw [← Ico_succ_eq_Icc, Finset.sum_Ico_succ_top hqm', show n + t - m' = m + 1 by omega]
  have hpair : ∑ i ∈ Finset.Ico q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      ≤ ∑ i ∈ Finset.Ioc (m + 1) u, n.choose i := by
    have hset : Finset.Ico q m' = Finset.Icc q (m' - 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    have hb : ∑ i ∈ Finset.Icc q (m' - 1), (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
        ≤ ∑ i ∈ Finset.Icc q (m' - 1), n.choose (n + t - i) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [Finset.mem_Icc] at hi
      exact level_add_level_le n t i h𝓕 hav ht (by omega) (by omega)
    have hr := sum_Icc_reflect (n + t) q (m' - 1) (by omega) (by omega) (fun j ↦ n.choose j)
    rw [show n + t - (m' - 1) = m + 2 by omega, ← hudef,
      show m + 2 = (m + 1) + 1 by omega, Icc_succ_eq_Ioc] at hr
    omega
  have hIocC : (∑ i ∈ Finset.Ioc (m + 1) u, n.choose i) + (∑ i ∈ Finset.Ioc u n, n.choose i)
      = ∑ i ∈ Finset.Ioc (m + 1) n, n.choose i := Finset.sum_Ioc_consecutive _ hmu hun
  have hsingle : Finset.Ioc m (m + 1) = {m + 1} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have htop : n.choose (m + 1) + (∑ i ∈ Finset.Ioc (m + 1) n, n.choose i)
      = ∑ i ∈ Finset.Ioc m n, n.choose i := by
    have h := Finset.sum_Ioc_consecutive (fun j ↦ n.choose j) (show m ≤ m + 1 by omega) hn
    rw [hsingle, Finset.sum_singleton] at h
    exact h
  omega

/-- The sets `B ⊆ range n` of size `b` with `#(B ∩ A₀) = t` number `C(#A₀, t) · C(n - #A₀, b - t)`
(`A₀ ⊆ range n`, `t ≤ b`), and none of them lies in `𝓕` when `A₀ ∈ 𝓕` and `#A₀ ≠ b`. -/
theorem level_card_le_choose_sub (n t b : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) {A₀ : Finset ℕ}
    (hA₀ : A₀ ∈ 𝓕) (hb : #A₀ ≠ b) (htb : t ≤ b) (htA : t ≤ #A₀) :
    #(level 𝓕 b) + (#A₀).choose t * (n - #A₀).choose (b - t) ≤ n.choose b := by
  classical
  -- `hb` and `htA` are not needed: `hav` forbids `#(B ∩ A₀) = t` even for `B = A₀`.
  have _hb := hb
  have _htA := htA
  have hA₀n : A₀ ⊆ range n := h𝓕 A₀ hA₀
  set 𝓑 : Finset (Finset ℕ) := ((range n).powersetCard b).filter fun B ↦ #(B ∩ A₀) = t with h𝓑
  -- the product injects into `𝓑`
  have hcount : (#A₀).choose t * (n - #A₀).choose (b - t) ≤ #𝓑 := by
    have hcard : #((A₀.powersetCard t) ×ˢ ((range n \ A₀).powersetCard (b - t)))
        = (#A₀).choose t * (n - #A₀).choose (b - t) := by
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hA₀n, Finset.card_range]
    rw [← hcard]
    refine Finset.card_le_card_of_injOn (fun p ↦ p.1 ∪ p.2) ?_ ?_
    · rintro ⟨S, T⟩ hST
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hST
      obtain ⟨⟨hS, hScard⟩, hT, hTcard⟩ := hST
      have hTA : Disjoint T A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT hx)).2 hxA
      have hdisjST : Disjoint S T := Finset.disjoint_of_subset_left hS hTA.symm
      have hinter : (S ∪ T) ∩ A₀ = S := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
          Finset.disjoint_iff_inter_eq_empty.mp hTA, Finset.union_empty]
      simp only [Finset.mem_coe, h𝓑, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.union_subset (hS.trans hA₀n) (hT.trans Finset.sdiff_subset), ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisjST, hScard, hTcard]
        omega
      · rw [hinter, hScard]
    · rintro ⟨S, T⟩ hST ⟨S', T'⟩ hST' heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hST hST'
      obtain ⟨⟨hS, -⟩, hT, -⟩ := hST
      obtain ⟨⟨hS', -⟩, hT', -⟩ := hST'
      have hTA : Disjoint T A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT hx)).2 hxA
      have hTA' : Disjoint T' A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT' hx)).2 hxA
      have heq' : S ∪ T = S' ∪ T' := heq
      have hS1 : (S ∪ T) ∩ A₀ = S := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
          Finset.disjoint_iff_inter_eq_empty.mp hTA, Finset.union_empty]
      have hS2 : (S' ∪ T') ∩ A₀ = S' := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS',
          Finset.disjoint_iff_inter_eq_empty.mp hTA', Finset.union_empty]
      have hSS : S = S' := by rw [← hS1, ← hS2, heq']
      have hT1 : (S ∪ T) \ A₀ = T := by
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hS,
          Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hTA]
      have hT2 : (S' ∪ T') \ A₀ = T' := by
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hS',
          Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hTA']
      have hTT : T = T' := by rw [← hT1, ← hT2, heq']
      rw [hSS, hTT]
  -- `level 𝓕 b` and `𝓑` are disjoint subsets of the `b`-subsets of `range n`
  have hsub₁ : level 𝓕 b ⊆ (range n).powersetCard b := by
    intro B hB
    rw [mem_level] at hB
    exact Finset.mem_powersetCard.mpr ⟨h𝓕 B hB.1, hB.2⟩
  have hsub₂ : 𝓑 ⊆ (range n).powersetCard b := Finset.filter_subset _ _
  have hdisj : Disjoint (level 𝓕 b) 𝓑 := by
    rw [Finset.disjoint_left]
    intro B hB hB'
    rw [mem_level] at hB
    rw [h𝓑, Finset.mem_filter] at hB'
    exact hav B hB.1 A₀ hA₀ hB'.2
  calc #(level 𝓕 b) + (#A₀).choose t * (n - #A₀).choose (b - t)
      ≤ #(level 𝓕 b) + #𝓑 := by omega
    _ = #(level 𝓕 b ∪ 𝓑) := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #((range n).powersetCard b) := Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
    _ = n.choose b := by rw [Finset.card_powersetCard, Finset.card_range]

end FranklFuredi
