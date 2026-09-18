import CameronErdos.Statement

/-!
# The Cameron–Erdős interval `[⌈(n+1)/3⌉, n]` (JSP-000616)

This file formalises the combinatorial core of the argument of Cameron and Erdős as
recorded in Green's note *An argument of Cameron and Erdős* (`ref/green-ce-notes.pdf`,
page 1): counting the sum-free subsets of the top third `[⌈(n+1)/3⌉, n]` of `[1, n]`.

Write `m = topThird n = ⌈(n+1)/3⌉` and split the interval as `Icc m n = B ∪ U` with

* `B = Icc m (n - m)` — the *initial block*, and
* `U = Icc (n - m + 1) n` — the *upper part*.

The three plan nodes proved here are:

* `Def_IntervalSumFree` — `CameronErdos.intervalSumFreeCount`;
* `Lem_CE_OnlySolutions` — `CameronErdos.onlySolutions`: every solution of `x + y = z`
  inside `Icc m n` has both summands in the initial block `B`, and `n - m < 2 * m`;
* `Lem_CE_CountFormula` — `CameronErdos.countFormula` and the global form
  `CameronErdos.intervalSumFreeCount_eq`.

The `g(k)` recurrence of Green's Proposition 2 lives in `CameronErdos/CE/GFunction.lean`;
the two halves are combined by the assembly node `Thm_CE_IntervalCount`.
-/

open Finset
open scoped Pointwise

namespace CameronErdos

/-! ## `Def_IntervalSumFree`: the interval and its sum-free count -/

/-- `topThird n = ⌈(n + 1) / 3⌉`, the left endpoint of the Cameron–Erdős interval
`[⌈(n+1)/3⌉, n]`. -/
def topThird (n : ℕ) : ℕ := (n + 3) / 3

example : topThird 1 = 1 := by decide
example : topThird 2 = 1 := by decide
example : topThird 3 = 2 := by decide
example : topThird 5 = 2 := by decide
example : topThird 6 = 3 := by decide

lemma topThird_eq_div_add_one (n : ℕ) : topThird n = n / 3 + 1 := by
  unfold topThird; omega

/-- `topThird n` really is `≥ (n+1)/3`: it is the ceiling of `(n+1)/3`. -/
theorem three_mul_topThird_ge (n : ℕ) : n + 1 ≤ 3 * topThird n := by
  unfold topThird; omega

/-- `topThird n` really is `≤ (n+3)/3`: it is the ceiling of `(n+1)/3`. -/
theorem topThird_le (n : ℕ) : 3 * topThird n ≤ n + 3 := by
  unfold topThird; omega

theorem topThird_pos (n : ℕ) : 0 < topThird n := by
  unfold topThird; omega

/-- `T(n)`: the number of sum-free subsets of `Icc ⌈(n+1)/3⌉ n`. -/
def intervalSumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc (topThird n) n).powerset.filter IsSumFree).card

/-! ## The splitting `Icc m n = B ∪ U` -/

/-- The initial block `B = Icc m (n - m)` of the Cameron–Erdős interval. -/
def ceBlock (n : ℕ) : Finset ℕ := Finset.Icc (topThird n) (n - topThird n)

/-- The upper part `U = Icc (n - m + 1) n` of the Cameron–Erdős interval. -/
def ceUpper (n : ℕ) : Finset ℕ := Finset.Icc (n - topThird n + 1) n

lemma mem_ceBlock {n a : ℕ} : a ∈ ceBlock n ↔ topThird n ≤ a ∧ a ≤ n - topThird n := by
  simp [ceBlock]

lemma mem_ceUpper {n a : ℕ} : a ∈ ceUpper n ↔ n - topThird n + 1 ≤ a ∧ a ≤ n := by
  simp [ceUpper]

/-- `n - m < 2 * m`: the initial block is shorter than `m`, so any two of its elements
sum past its right endpoint. -/
theorem sub_topThird_lt_two_mul (n : ℕ) : n - topThird n < 2 * topThird n := by
  have := three_mul_topThird_ge n
  omega

theorem ceBlock_union_ceUpper (n : ℕ) : ceBlock n ∪ ceUpper n = Finset.Icc (topThird n) n := by
  have h1 := three_mul_topThird_ge n
  have h2 := topThird_le n
  ext a
  simp only [Finset.mem_union, mem_ceBlock, mem_ceUpper, Finset.mem_Icc]
  omega

theorem ceBlock_disjoint_ceUpper (n : ℕ) : Disjoint (ceBlock n) (ceUpper n) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [mem_ceBlock] at ha
  rw [mem_ceUpper] at hb
  omega

theorem ceBlock_subset (n : ℕ) : ceBlock n ⊆ Finset.Icc (topThird n) n := by
  rw [← ceBlock_union_ceUpper]; exact Finset.subset_union_left

theorem ceUpper_subset (n : ℕ) : ceUpper n ⊆ Finset.Icc (topThird n) n := by
  rw [← ceBlock_union_ceUpper]; exact Finset.subset_union_right

/-! ## `Lem_CE_OnlySolutions` -/

/-- **Lem_CE_OnlySolutions.**  With `m = ⌈(n+1)/3⌉`, any solution of `x + y = z` with
`x, y, z ∈ Icc m n` has `x ≤ n - m` and `y ≤ n - m`, i.e. both summands lie in the
initial block `B = Icc m (n - m)`. -/
theorem onlySolutions {n x y z : ℕ} (hx : x ∈ Finset.Icc (topThird n) n)
    (hy : y ∈ Finset.Icc (topThird n) n) (hz : z ∈ Finset.Icc (topThird n) n)
    (hxyz : x + y = z) : x ≤ n - topThird n ∧ y ≤ n - topThird n := by
  rw [Finset.mem_Icc] at hx hy hz
  omega

/-- The initial-block form of `Lem_CE_OnlySolutions`. -/
theorem onlySolutions_mem_ceBlock {n x y z : ℕ} (hx : x ∈ Finset.Icc (topThird n) n)
    (hy : y ∈ Finset.Icc (topThird n) n) (hz : z ∈ Finset.Icc (topThird n) n)
    (hxyz : x + y = z) : x ∈ ceBlock n ∧ y ∈ ceBlock n := by
  obtain ⟨h1, h2⟩ := onlySolutions hx hy hz hxyz
  rw [Finset.mem_Icc] at hx hy
  exact ⟨mem_ceBlock.mpr ⟨hx.1, h1⟩, mem_ceBlock.mpr ⟨hy.1, h2⟩⟩

/-! ## Sum-freeness bookkeeping -/

/-- Sum-freeness passes to subsets. -/
theorem IsSumFree.subset {A A' : Finset ℕ} (h : IsSumFree A) (hsub : A' ⊆ A) : IsSumFree A' :=
  fun a ha b hb hab => h a (hsub ha) b (hsub hb) (hsub hab)

/-- Every element of `S + S` for `S ⊆ B` is `≥ 2m > n - m`, hence outside `B`. -/
theorem sumset_disjoint_ceBlock {n : ℕ} {S : Finset ℕ} (hS : S ⊆ ceBlock n) :
    Disjoint (S + S) (ceBlock n) := by
  rw [Finset.disjoint_left]
  rintro a ha hb
  rw [Finset.mem_add] at ha
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  have hx' := mem_ceBlock.mp (hS hx)
  have hy' := mem_ceBlock.mp (hS hy)
  have hb' := mem_ceBlock.mp hb
  have h1 := three_mul_topThird_ge n
  omega

/-- Since `(S + S) ∩ B = ∅`, *every* subset of the initial block is automatically
sum-free (this is why the sum in `intervalSumFreeCount_eq` is really over all `S ⊆ B`). -/
theorem isSumFree_of_subset_ceBlock {n : ℕ} {S : Finset ℕ} (hS : S ⊆ ceBlock n) :
    IsSumFree S := by
  intro a ha b hb hab
  exact Finset.disjoint_left.mp (sumset_disjoint_ceBlock hS)
    (Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩) (hS hab)

/-! ## `Lem_CE_CountFormula` -/

section CountFormula

variable {n : ℕ} {S : Finset ℕ}

/-- For `V ⊆ U \ (S + S)` the upper part of `S ∪ V` recovers `V`. -/
private lemma union_inter_ceUpper (hS : S ⊆ ceBlock n) {V : Finset ℕ}
    (hV : V ⊆ ceUpper n \ (S + S)) : (S ∪ V) ∩ ceUpper n = V := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hs | hv, hu⟩
    · exact absurd hu (Finset.disjoint_left.mp (ceBlock_disjoint_ceUpper n) (hS hs))
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, (Finset.mem_sdiff.mp (hV hv)).1⟩

/-- The sets counted by `Lem_CE_CountFormula` are exactly the `S ∪ V` with
`V ⊆ U \ (S + S)`. -/
theorem filter_inter_ceBlock_eq_image (hS : S ⊆ ceBlock n) :
    (Finset.Icc (topThird n) n).powerset.filter (fun A => IsSumFree A ∧ A ∩ ceBlock n = S)
      = (ceUpper n \ (S + S)).powerset.image (fun V => S ∪ V) := by
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hAsub, hAsf, hAB⟩
    have hSA : S ⊆ A := hAB ▸ Finset.inter_subset_left
    refine ⟨A ∩ ceUpper n, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha
      refine Finset.mem_sdiff.mpr ⟨ha.2, ?_⟩
      intro hmem
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hmem
      exact hAsf x (hSA hx) y (hSA hy) (hxy ▸ ha.1)
    · ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (h | h)
        · exact hSA h
        · exact h.1
      · intro ha
        have : a ∈ ceBlock n ∪ ceUpper n := by
          rw [ceBlock_union_ceUpper]; exact hAsub ha
        rcases Finset.mem_union.mp this with h | h
        · exact Or.inl (hAB ▸ Finset.mem_inter.mpr ⟨ha, h⟩)
        · exact Or.inr ⟨ha, h⟩
  · rintro ⟨V, hV, rfl⟩
    have hVU : V ⊆ ceUpper n := fun a ha => (Finset.mem_sdiff.mp (hV ha)).1
    have hVsum : ∀ a ∈ V, a ∉ S + S := fun a ha => (Finset.mem_sdiff.mp (hV ha)).2
    have hsub : S ∪ V ⊆ Finset.Icc (topThird n) n := by
      rw [← ceBlock_union_ceUpper]
      exact Finset.union_subset (hS.trans Finset.subset_union_left)
        (hVU.trans Finset.subset_union_right)
    refine ⟨hsub, ?_, ?_⟩
    · -- sum-freeness of `S ∪ V`
      intro a ha b hb hab
      have hmemB : ∀ c ∈ S ∪ V, c ∈ ceBlock n → c ∈ S := by
        intro c hc hcB
        rcases Finset.mem_union.mp hc with h | h
        · exact h
        · exact absurd hcB
            (Finset.disjoint_right.mp (ceBlock_disjoint_ceUpper n) (hVU h))
      obtain ⟨haB, hbB⟩ :=
        onlySolutions_mem_ceBlock (hsub ha) (hsub hb) (hsub hab) rfl
      have haS : a ∈ S := hmemB a ha haB
      have hbS : b ∈ S := hmemB b hb hbB
      have hsum : a + b ∈ S + S := Finset.mem_add.mpr ⟨a, haS, b, hbS, rfl⟩
      rcases Finset.mem_union.mp hab with h | h
      · exact Finset.disjoint_left.mp (sumset_disjoint_ceBlock hS) hsum (hS h)
      · exact hVsum _ h hsum
    · -- `(S ∪ V) ∩ B = S`
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
        Finset.union_eq_left]
      intro a ha
      rw [Finset.mem_inter] at ha
      exact absurd ha.2
        (Finset.disjoint_right.mp (ceBlock_disjoint_ceUpper n) (hVU ha.1))

/-- **Lem_CE_CountFormula.**  With `m = ⌈(n+1)/3⌉`, `B = Icc m (n - m)` and
`U = Icc (n - m + 1) n`, for every `S ⊆ B` the number of sum-free `A ⊆ Icc m n` with
`A ∩ B = S` is `2 ^ |U \ (S + S)|` if `S` is sum-free, and `0` otherwise. -/
theorem countFormula (n : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc (topThird n) (n - topThird n)) :
    ((Finset.Icc (topThird n) n).powerset.filter
        (fun A => IsSumFree A ∧ A ∩ Finset.Icc (topThird n) (n - topThird n) = S)).card
      = if IsSumFree S then
          2 ^ ((Finset.Icc (n - topThird n + 1) n) \ (S + S)).card
        else 0 := by
  have hS' : S ⊆ ceBlock n := hS
  rw [ite_eq_left_of_eq_true _ _ (eq_true (isSumFree_of_subset_ceBlock hS'))]
  show ((Finset.Icc (topThird n) n).powerset.filter
      (fun A => IsSumFree A ∧ A ∩ ceBlock n = S)).card
    = 2 ^ (ceUpper n \ (S + S)).card
  rw [filter_inter_ceBlock_eq_image hS', Finset.card_image_of_injOn, Finset.card_powerset]
  intro V₁ h₁ V₂ h₂ h
  rw [Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
  simp only at h
  rw [← union_inter_ceUpper hS' h₁, ← union_inter_ceUpper hS' h₂, h]

end CountFormula

/-- The `ceBlock` / `ceUpper` packaging of `countFormula`. -/
theorem countFormula' (n : ℕ) {S : Finset ℕ} (hS : S ⊆ ceBlock n) :
    ((Finset.Icc (topThird n) n).powerset.filter
        (fun A => IsSumFree A ∧ A ∩ ceBlock n = S)).card
      = 2 ^ (ceUpper n \ (S + S)).card := by
  rw [filter_inter_ceBlock_eq_image hS, Finset.card_image_of_injOn, Finset.card_powerset]
  intro V₁ h₁ V₂ h₂ h
  rw [Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
  simp only at h
  rw [← union_inter_ceUpper hS h₁, ← union_inter_ceUpper hS h₂, h]

/-- **Global form of `Lem_CE_CountFormula`.**  Partitioning the sum-free subsets of
`Icc m n` by their trace on the initial block `B` gives
`T(n) = Σ_{S ⊆ B} [S sum-free] · 2 ^ |U \ (S + S)|`. -/
theorem intervalSumFreeCount_eq (n : ℕ) :
    intervalSumFreeCount n =
      ∑ S ∈ (Finset.Icc (topThird n) (n - topThird n)).powerset,
        (if IsSumFree S then
            2 ^ ((Finset.Icc (n - topThird n + 1) n) \ (S + S)).card
          else 0) := by
  rw [intervalSumFreeCount,
    Finset.card_eq_sum_card_fiberwise
      (f := fun A => A ∩ Finset.Icc (topThird n) (n - topThird n))
      (t := (Finset.Icc (topThird n) (n - topThird n)).powerset)
      (fun A _ => Finset.mem_powerset.mpr Finset.inter_subset_right)]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.filter_filter]
  exact countFormula n (Finset.mem_powerset.mp hS)

/-- The `ceBlock` / `ceUpper` packaging of `intervalSumFreeCount_eq`; since every subset
of the initial block is sum-free, the indicator disappears. -/
theorem intervalSumFreeCount_eq' (n : ℕ) :
    intervalSumFreeCount n =
      ∑ S ∈ (ceBlock n).powerset, 2 ^ (ceUpper n \ (S + S)).card := by
  rw [intervalSumFreeCount,
    Finset.card_eq_sum_card_fiberwise
      (f := fun A => A ∩ ceBlock n) (t := (ceBlock n).powerset)
      (fun A _ => Finset.mem_powerset.mpr Finset.inter_subset_right)]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.filter_filter]
  exact countFormula' n (Finset.mem_powerset.mp hS)

/-! ## Axiom audit -/

#print axioms three_mul_topThird_ge
#print axioms topThird_le
#print axioms topThird_pos
#print axioms topThird_eq_div_add_one
#print axioms sub_topThird_lt_two_mul
#print axioms ceBlock_union_ceUpper
#print axioms ceBlock_disjoint_ceUpper
#print axioms ceBlock_subset
#print axioms ceUpper_subset
#print axioms onlySolutions
#print axioms onlySolutions_mem_ceBlock
#print axioms IsSumFree.subset
#print axioms sumset_disjoint_ceBlock
#print axioms isSumFree_of_subset_ceBlock
#print axioms filter_inter_ceBlock_eq_image
#print axioms countFormula
#print axioms countFormula'
#print axioms intervalSumFreeCount_eq
#print axioms intervalSumFreeCount_eq'

end CameronErdos
