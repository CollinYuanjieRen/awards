import Mathlib
import JSP573.FF.Basic

/-!
# Frankl–Füredi 1984, Theorem 1.5: a Katona-type shadow inequality under full row rank

Let `𝓕` be a family of `h`-subsets of `range n` whose containment rows
`inclVec n (h - t - 1) A` are linearly independent over `ℚ`, with `t + 1 ≤ h`. Then for every
`g` with `h - t - 1 ≤ g ≤ h`,
`#𝓕 · C(2h - t - 1, g) ≤ #(shadow g 𝓕) · C(2h - t - 1, h)`
(Katona's bound, which for intersecting families needs `#(A ∩ B) ≥ t + 1`; here the rank
hypothesis replaces the intersection condition).

Proof (Section 2 of the paper), by induction on `h` with `g` and `t` decreasing together.
* Base `g = h - t - 1`: linearly independent rows, restricted to the columns `G ∈ shadow g 𝓕`
  (all other columns are zero), give `#𝓕 ≤ #(shadow g 𝓕)`; and
  `C(2h - t - 1, h - t - 1) = C(2h - t - 1, h)`.
* Step `g ≥ h - t` (so `t ≥ 1` unless `g = h`, which is trivial): for `x ∈ range n` the link
  `link 𝓕 x = {A \ {x} : x ∈ A ∈ 𝓕}` is `(h - 1)`-uniform, its containment rows for the parameter
  `(h - 1) - (t - 1) - 1 = h - t - 1` are again independent (Proposition 2.1: a vanishing
  combination of the link rows lifts, with the same coefficients on `A = B ∪ {x}`, to a vanishing
  combination of the rows of `𝓕`; for a column `G ∌ x` this is immediate and for `G ∋ x` one
  averages over the `t + 1` ways of extending `G \ {x}`), so the induction hypothesis applies
  with `(h - 1, t - 1, g - 1)`. Double counting: `∑_x #(link 𝓕 x) = h · #𝓕` and
  `∑_x #(shadow (g - 1) (link 𝓕 x)) ≤ g · #(shadow g 𝓕)`. Then
  `C(N - 1, g - 1) · N / g = C(N, g)` and `C(N - 1, h - 1) · N / h = C(N, h)` with
  `N = 2h - t - 1` give the claim.
-/

open Finset

namespace FranklFuredi

/-- The link of `𝓕` at `x`: `{A \ {x} : x ∈ A ∈ 𝓕}`. -/
def link (𝓕 : Finset (Finset ℕ)) (x : ℕ) : Finset (Finset ℕ) :=
  (𝓕.filter fun A ↦ x ∈ A).image fun A ↦ A.erase x

/-- Membership in the link: `B ∈ link 𝓕 x` iff `x ∉ B` and `insert x B ∈ 𝓕`. -/
private lemma mem_link {𝓕 : Finset (Finset ℕ)} {x : ℕ} {B : Finset ℕ} :
    B ∈ link 𝓕 x ↔ x ∉ B ∧ insert x B ∈ 𝓕 := by
  simp only [link, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨A, ⟨hA, hxA⟩, rfl⟩
    exact ⟨Finset.notMem_erase _ _, by rwa [Finset.insert_erase hxA]⟩
  · rintro ⟨hx, hA⟩
    exact ⟨insert x B, ⟨hA, Finset.mem_insert_self _ _⟩, Finset.erase_insert hx⟩

/-- Reindexing a sum over the link as a sum over the members of `𝓕` containing `x`. -/
private lemma sum_link {M : Type*} [AddCommMonoid M] {𝓕 : Finset (Finset ℕ)} {x : ℕ}
    (f : Finset ℕ → M) :
    ∑ B ∈ link 𝓕 x, f (insert x B) = ∑ A ∈ 𝓕.filter fun A ↦ x ∈ A, f A := by
  classical
  rw [link, Finset.sum_image]
  · exact Finset.sum_congr rfl fun A hA ↦ by
      rw [Finset.insert_erase (Finset.mem_filter.1 hA).2]
  · intro A hA A' hA' hAA'
    rw [Finset.mem_coe, Finset.mem_filter] at hA hA'
    have h2 : insert x (A.erase x) = insert x (A'.erase x) := congrArg (insert x) hAA'
    rwa [Finset.insert_erase hA.2, Finset.insert_erase hA'.2] at h2

/-- Independence of the containment rows, restated as: the only family of coefficients killing
every column indexed by a `k`-subset of `range n` is the zero family. -/
private lemma linearIndependent_inclVec_iff (n k : ℕ) (𝓖 : Finset (Finset ℕ)) :
    LinearIndependent ℚ (fun A : 𝓖 ↦ inclVec n k (A : Finset ℕ)) ↔
      ∀ c : Finset ℕ → ℚ,
        (∀ G ⊆ range n, #G = k → ∑ A ∈ 𝓖, (if G ⊆ A then c A else 0) = 0) → ∀ A ∈ 𝓖, c A = 0 := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro H c hc A hA
    refine H (fun A ↦ c (A : Finset ℕ)) ?_ ⟨A, hA⟩
    funext G
    have hG := mem_powersetCard.1 G.2
    have h3 := hc (G : Finset ℕ) hG.1 hG.2
    rw [← Finset.sum_coe_sort 𝓖 fun A ↦ if (G : Finset ℕ) ⊆ A then c A else 0] at h3
    simpa only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero] using h3
  · intro H a ha i
    have key : ∀ G ⊆ range n, #G = k →
        ∑ A ∈ 𝓖, (if G ⊆ A then (if hA : A ∈ 𝓖 then a ⟨A, hA⟩ else 0) else 0) = 0 := by
      intro G hGr hGk
      have h2 := congrFun ha ⟨G, mem_powersetCard.2 ⟨hGr, hGk⟩⟩
      have h3 : ∑ i : 𝓖, (if G ⊆ (i : Finset ℕ) then a i else 0) = 0 := by
        simpa only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero] using h2
      rw [← Finset.sum_coe_sort 𝓖 fun A ↦ if G ⊆ A then (if hA : A ∈ 𝓖 then a ⟨A, hA⟩ else 0)
        else 0]
      exact Eq.trans (Finset.sum_congr rfl fun i _ ↦ by simp [i.2]) h3
    simpa [i.2] using H _ key i.1 i.2

/-- Proposition 2.1: independence of the containment rows passes to links (with `t - 1`). -/
theorem linearIndependent_link (n h t : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (ht : 1 ≤ t) (hth : t + 1 ≤ h)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A)) (x : ℕ) :
    LinearIndependent ℚ (fun B : link 𝓕 x ↦ inclVec n ((h - 1) - (t - 1) - 1) B) := by
  classical
  have hkk : h - 1 - (t - 1) - 1 = h - t - 1 := by omega
  rw [hkk, linearIndependent_inclVec_iff]
  rw [linearIndependent_inclVec_iff] at hli
  set k := h - t - 1 with hkdef
  intro a ha B hB
  set c : Finset ℕ → ℚ := fun A ↦ if x ∈ A then a (A.erase x) else 0 with hcdef
  have hcolx : ∀ G ⊆ range n, #G = k → x ∉ G → ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) = 0 := by
    intro G hGr hGk hxG
    have e1 : ∑ A ∈ 𝓕.filter (fun A ↦ x ∈ A), (if G ⊆ A then c A else 0)
        = ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun A hA hA' ↦ ?_
      have hxA : x ∉ A := by simpa [Finset.mem_filter, hA] using hA'
      simp [hcdef, hxA]
    rw [← e1, ← sum_link (fun A ↦ if G ⊆ A then c A else 0)]
    refine Eq.trans (Finset.sum_congr rfl fun B hB ↦ ?_) (ha G hGr hGk)
    rw [mem_link] at hB
    simp [hcdef, Finset.erase_insert hB.1, Finset.subset_insert_iff_of_notMem hxG]
  have hcol : ∀ G ⊆ range n, #G = k → ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) = 0 := by
    intro G hGr hGk
    by_cases hxG : x ∈ G
    swap
    · exact hcolx G hGr hGk hxG
    have key : ((t : ℚ) + 1) * ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0)
        = ∑ y ∈ range n \ G, ∑ A ∈ 𝓕, (if insert y G ⊆ A then c A else 0) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      by_cases hGA : G ⊆ A
      · have hAr : A ⊆ range n := (hU A hA).1
        have hAh : #A = h := (hU A hA).2
        have hinter : (range n \ G) ∩ A = A \ G := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_range]
          constructor
          · rintro ⟨⟨-, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨Finset.mem_range.1 (hAr h1), h2⟩, h1⟩
        have hcard : #(A \ G) = t + 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hGA, hAh, hGk]
          omega
        have e2 : ∑ y ∈ range n \ G, (if insert y G ⊆ A then c A else 0)
            = ∑ y ∈ (range n \ G) ∩ A, c A := by
          rw [← Finset.sum_ite_mem]
          exact Finset.sum_congr rfl fun y _ ↦ by simp [Finset.insert_subset_iff, hGA]
        have e3 : (if G ⊆ A then c A else 0) = c A := by simp [hGA]
        rw [e2, hinter, Finset.sum_const, hcard, nsmul_eq_mul, e3]
        push_cast
        ring
      · simp [hGA, Finset.insert_subset_iff]
    have hzero : ∀ y ∈ range n \ G, ∑ A ∈ 𝓕, (if insert y G ⊆ A then c A else 0) = 0 := by
      intro y hy
      rw [Finset.mem_sdiff, Finset.mem_range] at hy
      have hxmem : x ∈ insert y G := Finset.mem_insert_of_mem hxG
      set G' := (insert y G).erase x with hG'
      have hins : insert x G' = insert y G := Finset.insert_erase hxmem
      have hxG' : x ∉ G' := Finset.notMem_erase _ _
      have hG'r : G' ⊆ range n := (Finset.erase_subset _ _).trans (by
        rw [Finset.insert_subset_iff]
        exact ⟨Finset.mem_range.2 hy.1, hGr⟩)
      have hG'k : #G' = k := by
        rw [hG', Finset.card_erase_of_mem hxmem, Finset.card_insert_of_notMem hy.2, hGk]
        omega
      refine Eq.trans (Finset.sum_congr rfl fun A _ ↦ ?_) (hcolx G' hG'r hG'k hxG')
      by_cases hxA : x ∈ A
      · have hiff : insert y G ⊆ A ↔ G' ⊆ A := by
          rw [← hins, Finset.insert_subset_iff]
          simp [hxA]
        simp only [hiff]
      · simp [hcdef, hxA]
    have h0 := key.trans (Finset.sum_eq_zero hzero)
    have ht1 : ((t : ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0).resolve_left ht1
  have hcz := hli c hcol (insert x B) (mem_link.1 hB).2
  simpa [hcdef, Finset.erase_insert (mem_link.1 hB).1] using hcz

/-- Base case of Theorem 1.5: independent rows give `#𝓕 ≤ #(shadow (h - t - 1) 𝓕)`. -/
theorem card_le_card_shadow_of_linearIndependent (n h t : ℕ) (𝓕 : Finset (Finset ℕ))
    (_hU : IsUniformOn n h 𝓕)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A)) :
    #𝓕 ≤ #(shadow (h - t - 1) 𝓕) := by
  classical
  set k := h - t - 1 with hk
  have key : LinearIndependent ℚ (fun A : 𝓕 ↦ (fun G : (shadow k 𝓕 : Finset (Finset ℕ)) ↦
      if (G : Finset ℕ) ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fintype.linearIndependent_iff] at hli
    refine hli a ?_
    funext G
    have hG : #(G : Finset ℕ) = k := (mem_powersetCard.1 G.2).2
    simp only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hGs : (G : Finset ℕ) ∈ shadow k 𝓕
    · have h2 := congrFun ha ⟨(G : Finset ℕ), hGs⟩
      simpa only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero] using h2
    · refine Finset.sum_eq_zero fun A _ ↦ ?_
      have hns : ¬ (G : Finset ℕ) ⊆ (A : Finset ℕ) :=
        fun hsub ↦ hGs (mem_shadow.2 ⟨A, A.2, hsub, hG⟩)
      simp [hns]
  have h1 := key.fintype_card_le_finrank
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h1

/-- The `g`-shadow of a family of subsets of `range n` is `g`-uniform. -/
private lemma isUniformOn_shadow {n h g : ℕ} {𝓕 : Finset (Finset ℕ)} (hU : IsUniformOn n h 𝓕) :
    IsUniformOn n g (shadow g 𝓕) := by
  intro G hG
  obtain ⟨A, hA, hGA, hGg⟩ := mem_shadow.1 hG
  exact ⟨hGA.trans (hU A hA).1, hGg⟩

/-- The link of an `h`-uniform family is `(h - 1)`-uniform. -/
private lemma isUniformOn_link {n h : ℕ} {𝓕 : Finset (Finset ℕ)} (hU : IsUniformOn n h 𝓕)
    (x : ℕ) : IsUniformOn n (h - 1) (link 𝓕 x) := by
  intro B hB
  obtain ⟨hxB, hmem⟩ := mem_link.1 hB
  refine ⟨(Finset.subset_insert x B).trans (hU _ hmem).1, ?_⟩
  have hc := (hU _ hmem).2
  rw [Finset.card_insert_of_notMem hxB] at hc
  omega

/-- Double counting the incidences `x ∈ G ∈ 𝓖` for an `m`-uniform family on `range n`. -/
private lemma sum_card_filter_mem (n m : ℕ) (𝓖 : Finset (Finset ℕ)) (h𝓖 : IsUniformOn n m 𝓖) :
    ∑ x ∈ range n, #(𝓖.filter fun G ↦ x ∈ G) = m * #𝓖 := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have hin : ∀ G ∈ 𝓖, ∑ x ∈ range n, (if x ∈ G then 1 else 0) = m := by
    intro G hG
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (h𝓖 G hG).1, Finset.sum_const, smul_eq_mul,
      mul_one, (h𝓖 G hG).2]
  rw [Finset.sum_congr rfl hin, Finset.sum_const, smul_eq_mul, mul_comm]

/-- `∑_x #(link 𝓕 x) = h · #𝓕` for an `h`-uniform family. -/
private lemma sum_card_link (n h : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕) :
    ∑ x ∈ range n, #(link 𝓕 x) = h * #𝓕 := by
  classical
  have hcard : ∀ x : ℕ, #(link 𝓕 x) = #(𝓕.filter fun A ↦ x ∈ A) := by
    intro x
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
    exact sum_link (fun _ ↦ (1 : ℕ))
  simp only [hcard]
  exact sum_card_filter_mem n h 𝓕 hU

/-- `∑_x #(∂_{g-1} (link 𝓕 x)) ≤ g · #(∂_g 𝓕)`. -/
private lemma sum_card_shadow_link_le (n h g : ℕ) (𝓕 : Finset (Finset ℕ))
    (hU : IsUniformOn n h 𝓕) (hg : 1 ≤ g) :
    ∑ x ∈ range n, #(shadow (g - 1) (link 𝓕 x)) ≤ g * #(shadow g 𝓕) := by
  classical
  have hstep : ∀ x ∈ range n,
      #(shadow (g - 1) (link 𝓕 x)) ≤ #((shadow g 𝓕).filter fun G ↦ x ∈ G) := by
    intro x _
    refine Finset.card_le_card_of_injOn (fun G' ↦ insert x G') ?_ ?_
    · intro G' hG'
      obtain ⟨B, hB, hG'B, hG'g⟩ := mem_shadow.1 (Finset.mem_coe.1 hG')
      obtain ⟨hxB, hmem⟩ := mem_link.1 hB
      have hxG' : x ∉ G' := fun hx ↦ hxB (hG'B hx)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_shadow.2 ⟨insert x B, hmem,
        Finset.insert_subset_insert x hG'B, ?_⟩, Finset.mem_insert_self _ _⟩)
      rw [Finset.card_insert_of_notMem hxG', hG'g]
      omega
    · intro G₁ h₁ G₂ h₂ heq
      obtain ⟨B₁, hB₁, hG₁B, -⟩ := mem_shadow.1 (Finset.mem_coe.1 h₁)
      obtain ⟨B₂, hB₂, hG₂B, -⟩ := mem_shadow.1 (Finset.mem_coe.1 h₂)
      have hx₁ : x ∉ G₁ := fun hx ↦ (mem_link.1 hB₁).1 (hG₁B hx)
      have hx₂ : x ∉ G₂ := fun hx ↦ (mem_link.1 hB₂).1 (hG₂B hx)
      rw [← Finset.erase_insert hx₁, ← Finset.erase_insert hx₂]
      exact congrArg (fun G ↦ G.erase x) heq
  calc ∑ x ∈ range n, #(shadow (g - 1) (link 𝓕 x))
      ≤ ∑ x ∈ range n, #((shadow g 𝓕).filter fun G ↦ x ∈ G) := Finset.sum_le_sum hstep
    _ = g * #(shadow g 𝓕) := sum_card_filter_mem n g _ (isUniformOn_shadow hU)

/-- Theorem 1.5 (Frankl–Füredi). -/
theorem shadow_card_mul_choose_ge (n h t g : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A))
    (hth : t + 1 ≤ h) (hg₁ : h - t - 1 ≤ g) (hg₂ : g ≤ h) :
    (#𝓕 : ℚ) * ((2 * h - t - 1).choose g : ℚ) ≤
      (#(shadow g 𝓕) : ℚ) * ((2 * h - t - 1).choose h : ℚ) := by
  revert t g 𝓕
  induction h using Nat.strong_induction_on with
  | _ h IH =>
  intro t g 𝓕 hU hli hth hg₁ hg₂
  by_cases hgh : g = h
  · rw [hgh]
    have hsub : 𝓕 ⊆ shadow h 𝓕 := fun A hA ↦
      mem_shadow.2 ⟨A, hA, Finset.Subset.refl A, (hU A hA).2⟩
    have hc : (#𝓕 : ℚ) ≤ (#(shadow h 𝓕) : ℚ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  by_cases hgb : g = h - t - 1
  · rw [hgb]
    have hNh : 2 * h - t - 1 - h = h - t - 1 := by omega
    have hchoose : (2 * h - t - 1).choose (h - t - 1) = (2 * h - t - 1).choose h := by
      rw [← hNh]
      exact Nat.choose_symm (by omega)
    rw [hchoose]
    have hc : (#𝓕 : ℚ) ≤ (#(shadow (h - t - 1) 𝓕) : ℚ) := by
      exact_mod_cast card_le_card_shadow_of_linearIndependent n h t 𝓕 hU hli
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have ht1 : 1 ≤ t := by omega
  have hg0 : 1 ≤ g := by omega
  have hexp : 2 * (h - 1) - (t - 1) - 1 = 2 * h - t - 2 := by omega
  have hIH : ∀ x ∈ range n,
      (#(link 𝓕 x) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
        (#(shadow (g - 1) (link 𝓕 x)) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    intro x _
    have hx := IH (h - 1) (by omega) (t - 1) (g - 1) (link 𝓕 x) (isUniformOn_link hU x)
      (linearIndependent_link n h t 𝓕 hU ht1 hth hli x) (by omega) (by omega) (by omega)
    rwa [hexp] at hx
  have hsum : (∑ x ∈ range n, (#(link 𝓕 x) : ℚ)) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
      (∑ x ∈ range n, (#(shadow (g - 1) (link 𝓕 x)) : ℚ)) *
        (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hIH
  have e3 : (∑ x ∈ range n, (#(link 𝓕 x) : ℚ)) = (h : ℚ) * (#𝓕 : ℚ) := by
    rw [← Nat.cast_sum, sum_card_link n h 𝓕 hU]
    push_cast
    ring
  have e4 : (∑ x ∈ range n, (#(shadow (g - 1) (link 𝓕 x)) : ℚ))
      ≤ (g : ℚ) * (#(shadow g 𝓕) : ℚ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast sum_card_shadow_link_le n h g 𝓕 hU hg0
  have hsum' : (h : ℚ) * (#𝓕 : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
      (g : ℚ) * (#(shadow g 𝓕) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    rw [← e3]
    exact hsum.trans (mul_le_mul_of_nonneg_right e4 (by positivity))
  have hbg : (2 * h - t - 1) * ((2 * h - t - 2).choose (g - 1))
      = ((2 * h - t - 1).choose g) * g := by
    have h1 := Nat.add_one_mul_choose_eq (2 * h - t - 2) (g - 1)
    have e1 : 2 * h - t - 2 + 1 = 2 * h - t - 1 := by omega
    have e2 : g - 1 + 1 = g := by omega
    rwa [e1, e2] at h1
  have hbh : (2 * h - t - 1) * ((2 * h - t - 2).choose (h - 1))
      = ((2 * h - t - 1).choose h) * h := by
    have h1 := Nat.add_one_mul_choose_eq (2 * h - t - 2) (h - 1)
    have e1 : 2 * h - t - 2 + 1 = 2 * h - t - 1 := by omega
    have e2 : h - 1 + 1 = h := by omega
    rwa [e1, e2] at h1
  have hbg' : ((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)
      = (((2 * h - t - 1).choose g : ℕ) : ℚ) * (g : ℚ) := by exact_mod_cast congrArg Nat.cast hbg
  have hbh' : ((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)
      = (((2 * h - t - 1).choose h : ℕ) : ℚ) * (h : ℚ) := by exact_mod_cast congrArg Nat.cast hbh
  have hNpos : (0 : ℚ) ≤ ((2 * h - t - 1 : ℕ) : ℚ) := by positivity
  have step2 : (g : ℚ) * (h : ℚ) * ((#𝓕 : ℚ) * (((2 * h - t - 1).choose g : ℕ) : ℚ)) ≤
      (g : ℚ) * (h : ℚ) * ((#(shadow g 𝓕) : ℚ) * (((2 * h - t - 1).choose h : ℕ) : ℚ)) :=
    calc (g : ℚ) * (h : ℚ) * ((#𝓕 : ℚ) * (((2 * h - t - 1).choose g : ℕ) : ℚ))
        = (h : ℚ) * (#𝓕 : ℚ) * ((((2 * h - t - 1).choose g : ℕ) : ℚ) * (g : ℚ)) := by ring
      _ = (h : ℚ) * (#𝓕 : ℚ) *
            (((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)) := by
          rw [hbg']
      _ = ((2 * h - t - 1 : ℕ) : ℚ) *
            ((h : ℚ) * (#𝓕 : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)) := by ring
      _ ≤ ((2 * h - t - 1 : ℕ) : ℚ) * ((g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)) := by
          exact mul_le_mul_of_nonneg_left hsum' hNpos
      _ = (g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            (((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)) := by ring
      _ = (g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            ((((2 * h - t - 1).choose h : ℕ) : ℚ) * (h : ℚ)) := by rw [hbh']
      _ = (g : ℚ) * (h : ℚ) * ((#(shadow g 𝓕) : ℚ) * (((2 * h - t - 1).choose h : ℕ) : ℚ)) := by
          ring
  refine le_of_mul_le_mul_left step2 ?_
  have : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg0
  have : (0 : ℚ) < (h : ℚ) := by exact_mod_cast (by omega : 1 ≤ h)
  positivity

end FranklFuredi
