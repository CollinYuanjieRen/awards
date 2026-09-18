import Jsp751.Defs

/-!
# JSP-000751 / Erdős #903 — elementary counting in a linear space
-/

open Finset

namespace Erdos903

variable {v b : ℕ} {block : Fin b → Finset (Fin v)}

theorem mem_through_iff {x : Fin v} {i : Fin b} : i ∈ through block x ↔ x ∈ block i := by
  simp [through]

/-- Two distinct points lie in at most one common block. -/
theorem block_eq_of_two_mem (h : IsLinearSpace block) {i j : Fin b} {x y : Fin v} (hxy : x ≠ y)
    (hxi : x ∈ block i) (hyi : y ∈ block i) (hxj : x ∈ block j) (hyj : y ∈ block j) : i = j :=
  (h.2 x y hxy).unique ⟨hxi, hyi⟩ ⟨hxj, hyj⟩

/-- Two distinct blocks meet in at most one point. -/
theorem block_inter_card_le_one (h : IsLinearSpace block) {i j : Fin b} (hij : i ≠ j) :
    #(block i ∩ block j) ≤ 1 := by
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  rw [mem_inter] at hx hy
  by_contra hxy
  exact hij (block_eq_of_two_mem h hxy hx.1 hy.1 hx.2 hy.2)

/-- The blocks through a point cover all other points, each exactly once. -/
theorem sum_card_sub_one_through (h : IsLinearSpace block) (x : Fin v) :
    ∑ i ∈ through block x, (#(block i) - 1) = v - 1 := by
  classical
  have hdisj : ((through block x : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint
      fun i => (block i).erase x := by
    intro i hi j hj hij
    rw [mem_coe, mem_through_iff] at hi hj
    simp only [Function.onFun, disjoint_left]
    intro y hy hy'
    rw [mem_erase] at hy hy'
    exact hij (block_eq_of_two_mem h (Ne.symm hy.1) hi hy.2 hj hy'.2)
  have hunion : (through block x).biUnion (fun i => (block i).erase x) = univ.erase x := by
    ext y
    simp only [mem_biUnion, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨i, _, hy, -⟩
      exact hy
    · intro hy
      obtain ⟨i, hi, -⟩ := h.2 x y (Ne.symm hy)
      exact ⟨i, mem_through_iff.2 hi.1, hy, hi.2⟩
  have hcard := Finset.card_biUnion (fun i hi j hj hij => hdisj hi hj hij)
  rw [hunion, Finset.card_erase_of_mem (mem_univ x), Finset.card_univ, Fintype.card_fin] at hcard
  rw [hcard]
  exact Finset.sum_congr rfl fun i hi => (Finset.card_erase_of_mem (mem_through_iff.1 hi)).symm

/-- Counting pairs of points blockwise. -/
theorem sum_choose_two (h : IsLinearSpace block) :
    ∑ i, (#(block i)).choose 2 = v.choose 2 := by
  classical
  have hdisj : ((univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint
      fun i => (block i).powersetCard 2 := by
    intro i _ j _ hij
    simp only [Function.onFun, disjoint_left]
    intro s hs hs'
    rw [mem_powersetCard] at hs hs'
    have h2 : #s = 2 := hs.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 (by omega : 1 < #s)
    exact hij (block_eq_of_two_mem h hyz (hs.1 hy) (hs.1 hz) (hs'.1 hy) (hs'.1 hz))
  have hunion : (univ : Finset (Fin b)).biUnion (fun i => (block i).powersetCard 2)
      = (univ : Finset (Fin v)).powersetCard 2 := by
    ext s
    constructor
    · intro hs
      rw [mem_biUnion] at hs
      obtain ⟨i, -, hsi⟩ := hs
      rw [mem_powersetCard] at hsi ⊢
      exact ⟨Finset.subset_univ s, hsi.2⟩
    · intro hs
      rw [mem_powersetCard] at hs
      obtain ⟨y, z, hyz, hs2⟩ := Finset.card_eq_two.1 hs.2
      obtain ⟨i, hi, -⟩ := h.2 y z hyz
      rw [mem_biUnion]
      refine ⟨i, mem_univ i, ?_⟩
      rw [mem_powersetCard]
      refine ⟨?_, hs.2⟩
      rw [hs2]
      exact Finset.insert_subset hi.1 (Finset.singleton_subset_iff.2 hi.2)
  have hcard := Finset.card_biUnion (fun i hi j hj hij => hdisj hi hj hij)
  rw [hunion, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hcard
  rw [hcard]
  exact Finset.sum_congr rfl fun i _ => (Finset.card_powersetCard 2 (block i)).symm

/-- Double counting incidences. -/
theorem sum_degree_eq_sum_card : ∑ x, degree block x = ∑ i, #(block i) := by
  classical
  simp only [degree, through, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext y
  simp

/-- A point off a block has degree at least the size of that block: the blocks joining the point
to the points of the block are distinct. -/
theorem card_le_degree_of_not_mem (h : IsLinearSpace block) {x : Fin v} {j : Fin b}
    (hx : x ∉ block j) : #(block j) ≤ degree block x := by
  classical
  have key : ∀ y : Fin v, ∃ i, y ∈ block j → (x ∈ block i ∧ y ∈ block i) := by
    intro y
    by_cases hy : y ∈ block j
    · obtain ⟨i, hi, -⟩ := h.2 x y (fun e => hx (e ▸ hy))
      exact ⟨i, fun _ => hi⟩
    · exact ⟨j, fun h' => absurd h' hy⟩
  choose f hf using key
  refine Finset.card_le_card_of_injOn f (fun y hy => ?_) (fun y hy z hz hyz => ?_)
  · exact mem_through_iff.2 (hf y hy).1
  · rw [mem_coe] at hy hz
    by_contra hne
    have hz' : z ∈ block (f y) := by rw [hyz]; exact (hf z hz).2
    have : f y = j := block_eq_of_two_mem h hne (hf y hy).2 hz' hy hz
    exact hx (this ▸ (hf y hy).1)

/-- The blocks different from `block j` that meet it. -/
def meeting (block : Fin b → Finset (Fin v)) (j : Fin b) : Finset (Fin b) :=
  univ.filter fun i => i ≠ j ∧ (block i ∩ block j).Nonempty

theorem mem_meeting_iff {i j : Fin b} :
    i ∈ meeting block j ↔ i ≠ j ∧ (block i ∩ block j).Nonempty := by
  simp [meeting]

/-- A block meeting `block j` meets it in exactly one point. -/
theorem card_inter_eq_one_of_mem_meeting (h : IsLinearSpace block) {i j : Fin b}
    (hi : i ∈ meeting block j) : #(block i ∩ block j) = 1 := by
  obtain ⟨hij, hne⟩ := mem_meeting_iff.1 hi
  have h1 : 1 ≤ #(block i ∩ block j) := Finset.card_pos.2 hne
  have h2 := block_inter_card_le_one h hij
  omega

/-- The blocks meeting a block, counted point by point. -/
theorem card_meeting_eq (h : IsLinearSpace block) (j : Fin b) :
    #(meeting block j) = ∑ x ∈ block j, (degree block x - 1) := by
  classical
  have hdisj : ((block j : Finset (Fin v)) : Set (Fin v)).PairwiseDisjoint
      fun x => (through block x).erase j := by
    intro x hx y hy hxy
    rw [mem_coe] at hx hy
    simp only [Function.onFun, disjoint_left]
    intro i hi hi'
    rw [mem_erase, mem_through_iff] at hi hi'
    exact hi.1 (block_eq_of_two_mem h hxy hi.2 hi'.2 hx hy)
  have hunion : (block j).biUnion (fun x => (through block x).erase j) = meeting block j := by
    ext i
    simp only [mem_biUnion, mem_erase, mem_through_iff, mem_meeting_iff]
    constructor
    · rintro ⟨x, hxj, hij, hxi⟩
      exact ⟨hij, ⟨x, mem_inter.2 ⟨hxi, hxj⟩⟩⟩
    · rintro ⟨hij, ⟨x, hx⟩⟩
      rw [mem_inter] at hx
      exact ⟨x, hx.2, hij, hx.1⟩
  rw [← hunion, Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.card_erase_of_mem (mem_through_iff.2 hx), degree]

/-- For a point `y` off `block j`, the blocks through `y` meeting `block j` correspond to the
points of `block j`. -/
theorem card_meeting_filter_mem (h : IsLinearSpace block) {j : Fin b} {y : Fin v}
    (hy : y ∉ block j) :
    #((meeting block j).filter fun i => y ∈ block i) = #(block j) := by
  classical
  have key : ∀ x : Fin v, ∃ i, x ∈ block j → (y ∈ block i ∧ x ∈ block i) := by
    intro x
    by_cases hx : x ∈ block j
    · obtain ⟨i, hi, -⟩ := h.2 y x (fun e => hy (e ▸ hx))
      exact ⟨i, fun _ => hi⟩
    · exact ⟨j, fun h' => absurd h' hx⟩
  choose f hf using key
  refine (Finset.card_nbij f (fun x hx => ?_) (fun x hx x' hx' hxx' => ?_)
    (fun i hi => ?_)).symm
  · rw [mem_coe] at hx
    rw [mem_coe, mem_filter, mem_meeting_iff]
    refine ⟨⟨fun e => hy (e ▸ (hf x hx).1), ⟨x, mem_inter.2 ⟨(hf x hx).2, hx⟩⟩⟩, (hf x hx).1⟩
  · rw [mem_coe] at hx hx'
    by_contra hne
    have hx'' : x' ∈ block (f x) := by rw [hxx']; exact (hf x' hx').2
    have : f x = j := block_eq_of_two_mem h hne (hf x hx).2 hx'' hx hx'
    exact hy (this ▸ (hf x hx).1)
  · rw [mem_coe, mem_filter, mem_meeting_iff] at hi
    obtain ⟨⟨hij, ⟨x, hx⟩⟩, hyi⟩ := hi
    rw [mem_inter] at hx
    have hxy : y ≠ x := fun e => hy (e ▸ hx.2)
    refine ⟨x, hx.2, ?_⟩
    exact block_eq_of_two_mem h hxy (hf x hx.2).1 (hf x hx.2).2 hyi hx.1

/-- The total number of points of the blocks meeting `block j` off `block j`. -/
theorem sum_meeting_card_sub_one (h : IsLinearSpace block) (j : Fin b) :
    ∑ i ∈ meeting block j, (#(block i) - 1) = #(block j) * (v - #(block j)) := by
  classical
  have hcompl : #((univ : Finset (Fin v)) \ block j) = v - #(block j) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have step1 : ∀ i ∈ meeting block j,
      #(block i) - 1 = ∑ y ∈ (univ : Finset (Fin v)) \ block j, if y ∈ block i then 1 else 0 := by
    intro i hi
    have h1 := Finset.card_sdiff_add_card_inter (block i) (block j)
    have h2 := card_inter_eq_one_of_mem_meeting h hi
    rw [← Finset.card_filter]
    have hset : ((univ : Finset (Fin v)) \ block j).filter (fun y => y ∈ block i)
        = block i \ block j := by
      ext y
      simp only [mem_filter, mem_sdiff, mem_univ, true_and]
      tauto
    rw [hset]
    omega
  have step2 : ∀ y ∈ (univ : Finset (Fin v)) \ block j,
      ∑ i ∈ meeting block j, (if y ∈ block i then 1 else 0) = #(block j) := by
    intro y hy
    rw [mem_sdiff] at hy
    rw [← Finset.card_filter]
    exact card_meeting_filter_mem h hy.2
  rw [Finset.sum_congr rfl step1, Finset.sum_comm, Finset.sum_congr rfl step2,
    Finset.sum_const, hcompl, smul_eq_mul, mul_comm]

/-- The sum of squares bound feeding the Stanton–Kalbfleisch inequality. -/
theorem sum_meeting_sq_le (h : IsLinearSpace block) (j : Fin b) :
    ∑ i ∈ meeting block j, (#(block i) - 1) ^ 2 ≤ (v - #(block j)) * (v - 1) := by
  classical
  have hcompl : #((univ : Finset (Fin v)) \ block j) = v - #(block j) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have step1 : ∀ i ∈ meeting block j, (#(block i) - 1) ^ 2
      = ∑ y ∈ (univ : Finset (Fin v)) \ block j, if y ∈ block i then #(block i) - 1 else 0 := by
    intro i hi
    have h1 := Finset.card_sdiff_add_card_inter (block i) (block j)
    have h2 := card_inter_eq_one_of_mem_meeting h hi
    have h3 : #(block i \ block j) = #(block i) - 1 := by omega
    have hset : ((univ : Finset (Fin v)) \ block j).filter (fun y => y ∈ block i)
        = block i \ block j := by
      ext y
      simp only [mem_filter, mem_sdiff, mem_univ, true_and]
      tauto
    rw [← Finset.sum_filter, hset, Finset.sum_const, smul_eq_mul, h3, sq]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  calc ∑ y ∈ (univ : Finset (Fin v)) \ block j,
        ∑ i ∈ meeting block j, (if y ∈ block i then #(block i) - 1 else 0)
      ≤ ∑ _y ∈ (univ : Finset (Fin v)) \ block j, (v - 1) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.sum_filter, ← sum_card_sub_one_through h y]
        refine Finset.sum_le_sum_of_subset fun i hi => ?_
        rw [mem_filter] at hi
        exact mem_through_iff.2 hi.2
    _ = (v - #(block j)) * (v - 1) := by rw [Finset.sum_const, hcompl, smul_eq_mul]

/-- **Stanton–Kalbfleisch bound**: for a block of size `l`, the number of blocks meeting it is at
least `l² (v - l) / (v - 1)`. -/
theorem stanton_kalbfleisch (h : IsLinearSpace block) (j : Fin b) :
    #(block j) ^ 2 * (v - #(block j)) ≤ #(meeting block j) * (v - 1) := by
  rcases Nat.eq_zero_or_pos (v - #(block j)) with hz | hpos
  · simp [hz]
  · have hcs : (∑ i ∈ meeting block j, (#(block i) - 1)) ^ 2
        ≤ #(meeting block j) * ∑ i ∈ meeting block j, (#(block i) - 1) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [sum_meeting_card_sub_one h j] at hcs
    have hsq := sum_meeting_sq_le h j
    have key : #(block j) ^ 2 * (v - #(block j)) * (v - #(block j))
        ≤ #(meeting block j) * (v - 1) * (v - #(block j)) := by
      calc #(block j) ^ 2 * (v - #(block j)) * (v - #(block j))
          = (#(block j) * (v - #(block j))) ^ 2 := by ring
        _ ≤ #(meeting block j) * ∑ i ∈ meeting block j, (#(block i) - 1) ^ 2 := hcs
        _ ≤ #(meeting block j) * ((v - #(block j)) * (v - 1)) := Nat.mul_le_mul_left _ hsq
        _ = #(meeting block j) * (v - 1) * (v - #(block j)) := by ring
    exact Nat.le_of_mul_le_mul_right key hpos

/-- The blocks meeting `block j`, together with `block j` itself, are at most all blocks. -/
theorem card_meeting_add_one_le (j : Fin b) : #(meeting block j) + 1 ≤ b := by
  have hsub : meeting block j ⊆ univ.erase j := by
    intro i hi
    exact mem_erase.2 ⟨(mem_meeting_iff.1 hi).1, mem_univ i⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, Fintype.card_fin] at hcard
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  omega

end Erdos903
