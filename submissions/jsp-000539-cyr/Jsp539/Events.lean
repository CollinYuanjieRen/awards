import Jsp539.Plane
import Jsp539.Sample

/-!
# JSP-000539 / Erdős #664 — the three bad events

We instantiate the abstract sample space of `Jsp539.Sample` at `L := Line p`, `X := ZMod p`, so a
sample `ω : Ω (Line p) (ZMod p) M` assigns to every line `ℓ` and every coordinate `x` a value in
`Fin M`, and the point `(x, ℓ.1 * x + ℓ.2)` of `ℓ` is *kept* iff `ω ℓ x ≠ 0`.

* `kept ω ℓ` is the set of kept points of the line `ℓ`, `deg ω z` the number of lines through `z`
  on which `z` is kept.
* `card_bad1_le` : few samples have a line keeping at most `K` points.
* `card_bad2_le` : few samples have a point of degree at most `K`.
* `card_bad3_le` : few samples have a small set meeting all the kept sets.
* `exists_good` : if the three bounds add up to less than one, a sample avoiding all three bad
  events exists.
-/

open Finset

namespace Erdos664

variable {p M : ℕ} [Fact p.Prime] [NeZero M]

/-! ### The kept points and the degrees -/

/-- The points of the line `ℓ` kept by the sample `ω`: the point `(x, ℓ.1 * x + ℓ.2)` is kept iff
`ω ℓ x ≠ 0`. -/
def kept (ω : Ω (Line p) (ZMod p) M) (ℓ : Line p) : Finset (Pt p) :=
  (linePts ℓ).filter fun z => ω ℓ z.1 ≠ 0

/-- The number of lines through `z` on which the point `z` is kept. -/
def deg (ω : Ω (Line p) (ZMod p) M) (z : Pt p) : ℕ :=
  #((linesThrough z).filter fun ℓ => ω ℓ z.1 ≠ 0)

variable {ω : Ω (Line p) (ZMod p) M} {ℓ ℓ' : Line p} {z : Pt p}

theorem kept_subset_linePts : kept ω ℓ ⊆ linePts ℓ := Finset.filter_subset _ _

@[simp] theorem mem_kept : z ∈ kept ω ℓ ↔ z ∈ linePts ℓ ∧ ω ℓ z.1 ≠ 0 := Finset.mem_filter

theorem kept_inter_card_le_one (h : ℓ ≠ ℓ') : #(kept ω ℓ ∩ kept ω ℓ') ≤ 1 :=
  le_trans
    (Finset.card_le_card (Finset.inter_subset_inter kept_subset_linePts kept_subset_linePts))
    (linePts_inter_card_le_one h)

theorem card_kept_eq (ω : Ω (Line p) (ZMod p) M) (ℓ : Line p) :
    #(kept ω ℓ) = #((univ : Finset (ZMod p)).filter fun x => ω ℓ x ≠ 0) := by
  rw [kept, linePts_eq_image, Finset.filter_image,
    Finset.card_image_of_injective _ (linePts_param_injective ℓ)]

theorem deg_eq_card_filter (ω : Ω (Line p) (ZMod p) M) (z : Pt p) :
    deg ω z = #((univ : Finset (Line p)).filter fun ℓ => z ∈ kept ω ℓ) := by
  unfold deg
  congr 1
  ext ℓ
  simp [kept, mem_linesThrough_iff, mem_linePts]

/-- Double counting the incidences `(z, ℓ)` with `z ∈ B` kept on `ℓ`. -/
theorem sum_card_inter_kept (ω : Ω (Line p) (ZMod p) M) (B : Finset (Pt p)) :
    ∑ ℓ : Line p, #(B ∩ kept ω ℓ) = ∑ z ∈ B, deg ω z := by
  calc ∑ ℓ : Line p, #(B ∩ kept ω ℓ)
      = ∑ ℓ : Line p, ∑ z ∈ B, if z ∈ kept ω ℓ then 1 else 0 := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    _ = ∑ z ∈ B, ∑ ℓ : Line p, if z ∈ kept ω ℓ then 1 else 0 := Finset.sum_comm
    _ = ∑ z ∈ B, deg ω z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.card_filter, deg_eq_card_filter]

/-! ### The coordinate sets of a line and of a point -/

/-- The coordinates belonging to the line `ℓ`. -/
def coordsLine (ℓ : Line p) : Finset (Line p × ZMod p) :=
  (univ : Finset (ZMod p)).image fun x => ((ℓ, x) : Line p × ZMod p)

/-- The coordinates belonging to the lines through the point `z`. -/
def coordsPt (z : Pt p) : Finset (Line p × ZMod p) :=
  (linesThrough z).image fun ℓ => ((ℓ, z.1) : Line p × ZMod p)

omit [Fact p.Prime] in
theorem coordsLine_inj (ℓ : Line p) :
    Function.Injective fun x : ZMod p => ((ℓ, x) : Line p × ZMod p) :=
  fun _ _ h => congrArg Prod.snd h

omit [Fact p.Prime] in
theorem coordsPt_inj (z : Pt p) :
    Function.Injective fun ℓ : Line p => ((ℓ, z.1) : Line p × ZMod p) :=
  fun _ _ h => congrArg Prod.fst h

theorem card_coordsLine (ℓ : Line p) : #(coordsLine ℓ) = p := by
  rw [coordsLine, Finset.card_image_of_injective _ (coordsLine_inj ℓ), Finset.card_univ, ZMod.card]

theorem card_coordsPt (z : Pt p) : #(coordsPt z) = p := by
  rw [coordsPt, Finset.card_image_of_injective _ (coordsPt_inj z), card_linesThrough]

theorem card_filter_coordsLine (ω : Ω (Line p) (ZMod p) M) (ℓ : Line p) :
    #((coordsLine ℓ).filter fun c => ω c.1 c.2 ≠ 0) = #(kept ω ℓ) := by
  rw [coordsLine, Finset.filter_image,
    Finset.card_image_of_injective _ (coordsLine_inj ℓ), card_kept_eq]

theorem card_filter_coordsPt (ω : Ω (Line p) (ZMod p) M) (z : Pt p) :
    #((coordsPt z).filter fun c => ω c.1 c.2 ≠ 0) = deg ω z := by
  rw [coordsPt, Finset.filter_image, Finset.card_image_of_injective _ (coordsPt_inj z), deg]

/-! ### The first bad event: a line keeping few points -/

theorem card_bad1_le (hM : 1 ≤ M) (K : ℕ) :
    (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ ℓ, #(kept ω ℓ) ≤ K) : ℝ)
      ≤ (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p := by
  have hline : ∀ ℓ : Line p,
      (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K) : ℝ)
        ≤ (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K / (M : ℝ) ^ p := by
    intro ℓ
    have h := card_tail_le (L := Line p) (X := ZMod p) M hM (coordsLine ℓ) K
    rw [card_coordsLine] at h
    have hset : (univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K)
        = univ.filter fun ω : Ω (Line p) (ZMod p) M =>
            #((coordsLine ℓ).filter fun c => ω c.1 c.2 ≠ 0) ≤ K := by
      refine Finset.filter_congr fun ω _ => ?_
      rw [card_filter_coordsLine]
    rw [hset]
    exact h
  have hsub : (univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ ℓ, #(kept ω ℓ) ≤ K)
      ⊆ (univ : Finset (Line p)).biUnion
          fun ℓ => univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K := by
    intro ω hω
    obtain ⟨ℓ, hℓ⟩ := (Finset.mem_filter.1 hω).2
    exact Finset.mem_biUnion.2 ⟨ℓ, mem_univ _, Finset.mem_filter.2 ⟨mem_univ _, hℓ⟩⟩
  have hcard : #(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ ℓ, #(kept ω ℓ) ≤ K)
      ≤ ∑ ℓ : Line p, #(univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K) :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardR : (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ ℓ, #(kept ω ℓ) ≤ K) : ℝ)
      ≤ ∑ ℓ : Line p,
          (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K) : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans ?_
  calc ∑ ℓ : Line p, (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => #(kept ω ℓ) ≤ K) : ℝ)
      ≤ ∑ _ℓ : Line p,
          (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K / (M : ℝ) ^ p :=
        Finset.sum_le_sum fun ℓ _ => hline ℓ
    _ = (p : ℝ) ^ 2 * ((Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p) := by
        rw [Finset.sum_const, Finset.card_univ, card_Line, nsmul_eq_mul]
        push_cast
        ring
    _ = (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p := by ring

/-! ### The second bad event: a point of small degree -/

theorem card_bad2_le (hM : 1 ≤ M) (K : ℕ) :
    (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ z, deg ω z ≤ K) : ℝ)
      ≤ (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p := by
  have hpt : ∀ z : Pt p,
      (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K) : ℝ)
        ≤ (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K / (M : ℝ) ^ p := by
    intro z
    have h := card_tail_le (L := Line p) (X := ZMod p) M hM (coordsPt z) K
    rw [card_coordsPt] at h
    have hset : (univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K)
        = univ.filter fun ω : Ω (Line p) (ZMod p) M =>
            #((coordsPt z).filter fun c => ω c.1 c.2 ≠ 0) ≤ K := by
      refine Finset.filter_congr fun ω _ => ?_
      rw [card_filter_coordsPt]
    rw [hset]
    exact h
  have hsub : (univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ z, deg ω z ≤ K)
      ⊆ (univ : Finset (Pt p)).biUnion
          fun z => univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K := by
    intro ω hω
    obtain ⟨z, hz⟩ := (Finset.mem_filter.1 hω).2
    exact Finset.mem_biUnion.2 ⟨z, mem_univ _, Finset.mem_filter.2 ⟨mem_univ _, hz⟩⟩
  have hcard : #(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ z, deg ω z ≤ K)
      ≤ ∑ z : Pt p, #(univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K) :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardR : (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∃ z, deg ω z ≤ K) : ℝ)
      ≤ ∑ z : Pt p, (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K) : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans ?_
  calc ∑ z : Pt p, (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => deg ω z ≤ K) : ℝ)
      ≤ ∑ _z : Pt p,
          (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K / (M : ℝ) ^ p :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = (p : ℝ) ^ 2 * ((Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p) := by
        rw [Finset.sum_const, Finset.card_univ, card_Pt, nsmul_eq_mul]
        push_cast
        ring
    _ = (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K
          / (M : ℝ) ^ p := by ring

/-! ### Counting small subsets -/

/-- There are at most `(N + 1) ^ K` subsets of size at most `K` of an `N`-element type. -/
theorem card_small_subsets_le (α : Type*) [Fintype α] [DecidableEq α] (K : ℕ) :
    #((univ : Finset (Finset α)).filter fun B => #B ≤ K) ≤ (Fintype.card α + 1) ^ K := by
  have hsub : ((univ : Finset (Finset α)).filter fun B => #B ≤ K)
      ⊆ (Finset.range (K + 1)).biUnion fun k => Finset.powersetCard k (univ : Finset α) := by
    intro B hB
    refine Finset.mem_biUnion.2 ⟨#B, Finset.mem_range.2 ?_,
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
    exact Nat.lt_succ_of_le (Finset.mem_filter.1 hB).2
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have h1 : ∑ k ∈ Finset.range (K + 1), #(Finset.powersetCard k (univ : Finset α))
      = ∑ k ∈ Finset.range (K + 1), (Fintype.card α).choose k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [h1]
  calc ∑ k ∈ Finset.range (K + 1), (Fintype.card α).choose k
      ≤ ∑ k ∈ Finset.range (K + 1), Fintype.card α ^ k :=
        Finset.sum_le_sum fun k _ => Nat.choose_le_pow _ _
    _ ≤ (Fintype.card α + 1) ^ K := by
        rw [add_pow]
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        simpa using Nat.le_mul_of_pos_right _ (Nat.choose_pos hk')

/-! ### The coordinates of a candidate transversal on a line -/

/-- The coordinates on the line `ℓ` of the points of `B`. -/
def coordsSet (B : Finset (Pt p)) (ℓ : Line p) : Finset (ZMod p) :=
  (univ : Finset (ZMod p)).filter fun x => ((x, ℓ.1 * x + ℓ.2) : Pt p) ∈ B

theorem inter_linePts_eq_image (B : Finset (Pt p)) (ℓ : Line p) :
    B ∩ linePts ℓ = (coordsSet B ℓ).image fun x => ((x, ℓ.1 * x + ℓ.2) : Pt p) := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_image, coordsSet, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_linePts]
  constructor
  · rintro ⟨hzB, hz⟩
    have hz' : ((z.1, ℓ.1 * z.1 + ℓ.2) : Pt p) = z := Prod.ext rfl hz.symm
    exact ⟨z.1, by rwa [hz'], hz'⟩
  · rintro ⟨x, hxB, rfl⟩
    exact ⟨hxB, rfl⟩

theorem card_coordsSet (B : Finset (Pt p)) (ℓ : Line p) :
    #(coordsSet B ℓ) = #(B ∩ linePts ℓ) := by
  rw [inter_linePts_eq_image, Finset.card_image_of_injective _ (linePts_param_injective ℓ)]

theorem nonempty_inter_kept_iff (B : Finset (Pt p)) (ω : Ω (Line p) (ZMod p) M) (ℓ : Line p) :
    (B ∩ kept ω ℓ).Nonempty ↔ ∃ x ∈ coordsSet B ℓ, ω ℓ x ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    rw [Finset.mem_inter, mem_kept] at hz
    have hz' : ((z.1, ℓ.1 * z.1 + ℓ.2) : Pt p) = z := Prod.ext rfl (mem_linePts.1 hz.2.1).symm
    refine ⟨z.1, ?_, hz.2.2⟩
    simp only [coordsSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hz']
    exact hz.1
  · rintro ⟨x, hx, hxne⟩
    simp only [coordsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨(x, ℓ.1 * x + ℓ.2), Finset.mem_inter.2 ⟨hx, mem_kept.2 ⟨mk_mem_linePts ℓ x, hxne⟩⟩⟩

/-! ### The third bad event: a small set meeting every kept set -/

theorem card_bad3_le (hM : 1 ≤ M) (C : ℕ) :
    (#(univ.filter fun ω : Ω (Line p) (ZMod p) M =>
        ∃ B : Finset (Pt p), #B ≤ 2 * p * (C + 1) ∧ ∀ ℓ, (B ∩ kept ω ℓ).Nonempty) : ℝ)
      ≤ ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
          * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hinvle : (1 / (M : ℝ)) ^ (4 * C + 3) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one hMpos]; exact hM1)
  have hη0 : (0 : ℝ) ≤ 1 - (1 / (M : ℝ)) ^ (4 * C + 3) := by linarith
  have hη1 : 1 - (1 / (M : ℝ)) ^ (4 * C + 3) ≤ 1 := by
    have : (0 : ℝ) ≤ (1 / (M : ℝ)) ^ (4 * C + 3) := by positivity
    linarith
  -- the bound for a single candidate `B`
  have key : ∀ B : Finset (Pt p), #B ≤ 2 * p * (C + 1) →
      (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∀ ℓ, (B ∩ kept ω ℓ).Nonempty) : ℝ)
        ≤ (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2) := by
    intro B hB
    have hevent : (univ.filter fun ω : Ω (Line p) (ZMod p) M => ∀ ℓ, (B ∩ kept ω ℓ).Nonempty)
        = univ.filter fun ω : Ω (Line p) (ZMod p) M =>
            ∀ ℓ, ∃ x ∈ coordsSet B ℓ, ω ℓ x ≠ 0 := by
      refine Finset.filter_congr fun ω _ => ?_
      exact forall_congr' fun ℓ => nonempty_inter_kept_iff B ω ℓ
    have hsumT : ∑ ℓ : Line p, #(coordsSet B ℓ) = #B * p := by
      rw [← sum_card_inter_linePts B]
      exact Finset.sum_congr rfl fun ℓ _ => card_coordsSet B ℓ
    -- heavy lines are few
    have hHsum : #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
        * (4 * C + 4) ≤ 2 * p * (C + 1) * p := by
      calc #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
              * (4 * C + 4)
          ≤ ∑ ℓ ∈ (univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3,
              #(coordsSet B ℓ) := by
            have h := Finset.card_nsmul_le_sum
              ((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
              (fun ℓ => #(coordsSet B ℓ)) (4 * C + 4)
              (fun ℓ hℓ => by
                have := (Finset.mem_filter.1 hℓ).2
                omega)
            simpa [smul_eq_mul] using h
        _ ≤ ∑ ℓ : Line p, #(coordsSet B ℓ) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = #B * p := hsumT
        _ ≤ 2 * p * (C + 1) * p := Nat.mul_le_mul_right p hB
    have h2H : 2 * #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
        ≤ p ^ 2 := by
      have heq1 : #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
          * (4 * C + 4)
          = (2 * #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3))
              * (2 * (C + 1)) := by ring
      have heq2 : 2 * p * (C + 1) * p = p ^ 2 * (2 * (C + 1)) := by ring
      rw [heq1, heq2] at hHsum
      exact Nat.le_of_mul_le_mul_right hHsum (by omega)
    have hLH : #((univ : Finset (Line p)).filter fun ℓ => #(coordsSet B ℓ) ≤ 4 * C + 3)
        + #((univ : Finset (Line p)).filter fun ℓ => ¬ #(coordsSet B ℓ) ≤ 4 * C + 3)
        = p ^ 2 := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, card_Line]
    have hLcard : p ^ 2 / 2
        ≤ #((univ : Finset (Line p)).filter fun ℓ => #(coordsSet B ℓ) ≤ 4 * C + 3) := by
      obtain ⟨n, hn⟩ : ∃ n, p ^ 2 = n := ⟨_, rfl⟩
      rw [hn] at hLH h2H ⊢
      omega
    have happ := card_hitsAll_le' (L := Line p) (X := ZMod p) M hM (coordsSet B) (4 * C + 3)
      ((univ : Finset (Line p)).filter fun ℓ => #(coordsSet B ℓ) ≤ 4 * C + 3)
      (fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2)
    rw [hevent]
    refine happ.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη0 hη1 hLcard) (by positivity)
  -- sum over the candidates `B`
  have hsmall : #((univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1))
      ≤ (p ^ 2 + 1) ^ (2 * p * (C + 1)) := by
    have h := card_small_subsets_le (Pt p) (2 * p * (C + 1))
    rwa [card_Pt] at h
  have hsub : (univ.filter fun ω : Ω (Line p) (ZMod p) M =>
        ∃ B : Finset (Pt p), #B ≤ 2 * p * (C + 1) ∧ ∀ ℓ, (B ∩ kept ω ℓ).Nonempty)
      ⊆ ((univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1)).biUnion
          fun B => univ.filter fun ω : Ω (Line p) (ZMod p) M =>
            ∀ ℓ, (B ∩ kept ω ℓ).Nonempty := by
    intro ω hω
    obtain ⟨B, hB1, hB2⟩ := (Finset.mem_filter.1 hω).2
    exact Finset.mem_biUnion.2 ⟨B, Finset.mem_filter.2 ⟨mem_univ _, hB1⟩,
      Finset.mem_filter.2 ⟨mem_univ _, hB2⟩⟩
  have hcard := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc (#(univ.filter fun ω : Ω (Line p) (ZMod p) M =>
          ∃ B : Finset (Pt p), #B ≤ 2 * p * (C + 1) ∧ ∀ ℓ, (B ∩ kept ω ℓ).Nonempty) : ℝ)
      ≤ ∑ B ∈ (univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1),
          (#(univ.filter fun ω : Ω (Line p) (ZMod p) M => ∀ ℓ, (B ∩ kept ω ℓ).Nonempty) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ _B ∈ (univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1),
          (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2) :=
        Finset.sum_le_sum fun B hB => key B (Finset.mem_filter.1 hB).2
    _ = (#((univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1)) : ℝ)
          * ((Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
          * ((Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := (Nat.cast_le (α := ℝ)).2 hsmall
        calc (#((univ : Finset (Finset (Pt p))).filter fun B => #B ≤ 2 * p * (C + 1)) : ℝ)
            ≤ (((p ^ 2 + 1) ^ (2 * p * (C + 1)) : ℕ) : ℝ) := h
          _ = ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) := by push_cast; ring
    _ = ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
          * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2) := by ring

/-! ### Existence of a good sample -/

/-- If the three failure bounds add up to less than one, some sample avoids all three bad events:
every line keeps more than `K₁` points, every point has degree more than `K₂`, and every set
meeting all the kept sets has more than `2 p (C + 1)` points. -/
theorem exists_good (hM : 1 ≤ M) (K₁ K₂ C : ℕ)
    (hsum : (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ K₁ / (M : ℝ) ^ p
        + (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ K₂ / (M : ℝ) ^ p
        + ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2) < 1) :
    ∃ ω : Ω (Line p) (ZMod p) M, (∀ ℓ, K₁ < #(kept ω ℓ)) ∧ (∀ z, K₂ < deg ω z) ∧
      ∀ B : Finset (Pt p), (∀ ℓ, (B ∩ kept ω ℓ).Nonempty) → 2 * p * (C + 1) < #B := by
  have hNpos : 0 < Fintype.card (Ω (Line p) (ZMod p) M) :=
    Fintype.card_pos_iff.2 ⟨fun _ _ => (0 : Fin M)⟩
  have hN0 : (0 : ℝ) < (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) := by exact_mod_cast hNpos
  have hb1 := card_bad1_le (p := p) (M := M) hM K₁
  have hb2 := card_bad2_le (p := p) (M := M) hM K₂
  have hb3 := card_bad3_le (p := p) (M := M) hM C
  obtain ⟨bad1, hbad1⟩ : ∃ s : Finset (Ω (Line p) (ZMod p) M),
      s = univ.filter fun ω => ∃ ℓ, #(kept ω ℓ) ≤ K₁ := ⟨_, rfl⟩
  obtain ⟨bad2, hbad2⟩ : ∃ s : Finset (Ω (Line p) (ZMod p) M),
      s = univ.filter fun ω => ∃ z, deg ω z ≤ K₂ := ⟨_, rfl⟩
  obtain ⟨bad3, hbad3⟩ : ∃ s : Finset (Ω (Line p) (ZMod p) M),
      s = univ.filter fun ω =>
        ∃ B : Finset (Pt p), #B ≤ 2 * p * (C + 1) ∧ ∀ ℓ, (B ∩ kept ω ℓ).Nonempty := ⟨_, rfl⟩
  rw [← hbad1] at hb1
  rw [← hbad2] at hb2
  rw [← hbad3] at hb3
  have e1 : (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K₁
        / (M : ℝ) ^ p
      = (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
          * ((p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ K₁ / (M : ℝ) ^ p) := by ring
  have e2 : (p : ℝ) ^ 2 * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) * 2 ^ p * (M : ℝ) ^ K₂
        / (M : ℝ) ^ p
      = (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
          * ((p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ K₂ / (M : ℝ) ^ p) := by ring
  have e3 : ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
        * (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
        * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)
      = (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ)
          * (((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)) := by ring
  rw [e1] at hb1
  rw [e2] at hb2
  rw [e3] at hb3
  have hmul := mul_lt_mul_of_pos_left hsum hN0
  rw [mul_one, mul_add, mul_add] at hmul
  have hcardR : (#(bad1 ∪ bad2 ∪ bad3) : ℝ) ≤ (#bad1 : ℝ) + (#bad2 : ℝ) + (#bad3 : ℝ) := by
    have h : #(bad1 ∪ bad2 ∪ bad3) ≤ #bad1 + #bad2 + #bad3 :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    exact_mod_cast h
  have hlt : (#(bad1 ∪ bad2 ∪ bad3) : ℝ) < (Fintype.card (Ω (Line p) (ZMod p) M) : ℝ) := by
    linarith
  have hne : ∃ ω : Ω (Line p) (ZMod p) M, ω ∉ bad1 ∪ bad2 ∪ bad3 := by
    by_contra h
    push Not at h
    rw [Finset.eq_univ_of_forall h, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨ω, hω⟩ := hne
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or, hbad1, hbad2, hbad3] at hω
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  refine ⟨ω, fun ℓ => ?_, fun z => ?_, fun B hB => ?_⟩
  · by_contra hc
    push Not at hc
    exact h1 (Finset.mem_filter.2 ⟨mem_univ _, ⟨ℓ, hc⟩⟩)
  · by_contra hc
    push Not at hc
    exact h2 (Finset.mem_filter.2 ⟨mem_univ _, ⟨z, hc⟩⟩)
  · by_contra hc
    push Not at hc
    exact h3 (Finset.mem_filter.2 ⟨mem_univ _, ⟨B, hc, hB⟩⟩)

end Erdos664
