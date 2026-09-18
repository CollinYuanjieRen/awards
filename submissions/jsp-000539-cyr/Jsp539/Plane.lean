import Jsp539.Defs

/-!
# The affine plane over `ZMod p`

For a prime `p` we work with the affine plane over the field `ZMod p`:

* points are pairs `Pt p = ZMod p × ZMod p`;
* `Line p = ZMod p × ZMod p` encodes the *non-vertical* lines, the pair `(a, b)` standing for
  the line `y = a * x + b`.

There are `p ^ 2` points and `p ^ 2` such lines, every line carries exactly `p` points, every
point lies on exactly `p` lines, and two distinct lines meet in at most one point.  Double
counting these incidences gives `∑ ℓ, #(B ∩ linePts ℓ) = #B * p` for every set of points `B`,
which is the combinatorial input for the construction in later modules.
-/

open Finset

namespace Erdos664

variable {p : ℕ} [Fact p.Prime]

/-- Points of the affine plane over `ZMod p`. -/
abbrev Pt (p : ℕ) := ZMod p × ZMod p

/-- Non-vertical lines of the affine plane over `ZMod p`: `(a, b)` is the line `y = a * x + b`. -/
abbrev Line (p : ℕ) := ZMod p × ZMod p

/-- The point `z` lies on the line `ℓ`. -/
def onLine (ℓ : Line p) (z : Pt p) : Prop := z.2 = ℓ.1 * z.1 + ℓ.2

instance instDecidableOnLine (ℓ : Line p) (z : Pt p) : Decidable (onLine ℓ z) := by
  unfold onLine; infer_instance

/-- The points of the line `ℓ`. -/
def linePts (ℓ : Line p) : Finset (Pt p) := univ.filter (fun z => onLine ℓ z)

/-- The lines through the point `z`. -/
def linesThrough (z : Pt p) : Finset (Line p) := univ.filter (fun ℓ => onLine ℓ z)

/-! ### Cardinality of the plane -/

theorem card_Pt (p : ℕ) [Fact p.Prime] : Fintype.card (Pt p) = p ^ 2 := by
  rw [Fintype.card_prod, ZMod.card, pow_two]

theorem card_Line (p : ℕ) [Fact p.Prime] : Fintype.card (Line p) = p ^ 2 := by
  rw [Fintype.card_prod, ZMod.card, pow_two]

/-! ### Membership -/

@[simp] theorem mem_linePts {ℓ : Line p} {z : Pt p} :
    z ∈ linePts ℓ ↔ z.2 = ℓ.1 * z.1 + ℓ.2 := by
  rw [linePts, Finset.mem_filter]
  exact and_iff_right (mem_univ z)

@[simp] theorem mem_linesThrough_iff {z : Pt p} {ℓ : Line p} :
    ℓ ∈ linesThrough z ↔ z.2 = ℓ.1 * z.1 + ℓ.2 := by
  rw [linesThrough, Finset.mem_filter]
  exact and_iff_right (mem_univ ℓ)

/-- Incidence is symmetric in the two descriptions. -/
theorem mem_linesThrough {z : Pt p} {ℓ : Line p} : ℓ ∈ linesThrough z ↔ z ∈ linePts ℓ := by
  rw [mem_linesThrough_iff, mem_linePts]

theorem onLine_iff_mem_linePts {ℓ : Line p} {z : Pt p} : onLine ℓ z ↔ z ∈ linePts ℓ := by
  rw [mem_linePts]; rfl

theorem mk_mem_linePts (ℓ : Line p) (x : ZMod p) : ((x, ℓ.1 * x + ℓ.2) : Pt p) ∈ linePts ℓ := by
  rw [mem_linePts]

theorem linesThrough_eq_filter (z : Pt p) :
    linesThrough z = univ.filter (fun ℓ : Line p => z ∈ linePts ℓ) := by
  ext ℓ; simp

/-! ### The `x`-coordinate parametrisation of a line -/

theorem linePts_param_injective (ℓ : Line p) :
    Function.Injective (fun x : ZMod p => ((x, ℓ.1 * x + ℓ.2) : Pt p)) := fun _ _ h =>
  congrArg Prod.fst h

theorem linePts_eq_image (ℓ : Line p) :
    linePts ℓ = univ.image (fun x : ZMod p => ((x, ℓ.1 * x + ℓ.2) : Pt p)) := by
  ext ⟨x, y⟩
  simp only [mem_linePts, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨x, rfl, h.symm⟩
  · rintro ⟨x', rfl, h⟩; exact h.symm

theorem exists_x_of_mem_linePts {ℓ : Line p} {z : Pt p} (hz : z ∈ linePts ℓ) :
    ∃ x : ZMod p, z = (x, ℓ.1 * x + ℓ.2) :=
  ⟨z.1, Prod.ext rfl (mem_linePts.1 hz)⟩

/-- A point of `ℓ` has its second coordinate determined by the first. -/
theorem snd_of_mem_linePts {ℓ : Line p} {z : Pt p} (hz : z ∈ linePts ℓ) :
    z.2 = ℓ.1 * z.1 + ℓ.2 := mem_linePts.1 hz

/-- A point of `ℓ` is determined by its first coordinate. -/
theorem inj_fst_on_line {ℓ : Line p} {z w : Pt p} (hz : z ∈ linePts ℓ) (hw : w ∈ linePts ℓ)
    (h : z.1 = w.1) : z = w :=
  Prod.ext h (by rw [snd_of_mem_linePts hz, snd_of_mem_linePts hw, h])

theorem fst_of_mem_linePts_injOn (ℓ : Line p) :
    Set.InjOn (fun z : Pt p => z.1) (linePts ℓ) := fun _ hz _ hw h =>
  inj_fst_on_line (mem_coe.1 hz) (mem_coe.1 hw) h

/-! ### Every line has `p` points, every point lies on `p` lines -/

theorem card_linePts (ℓ : Line p) : #(linePts ℓ) = p := by
  rw [linePts_eq_image, Finset.card_image_of_injective _ (linePts_param_injective ℓ),
    Finset.card_univ, ZMod.card]

theorem linesThrough_param_injective (z : Pt p) :
    Function.Injective (fun a : ZMod p => ((a, z.2 - a * z.1) : Line p)) := fun _ _ h =>
  congrArg Prod.fst h

theorem linesThrough_eq_image (z : Pt p) :
    linesThrough z = univ.image (fun a : ZMod p => ((a, z.2 - a * z.1) : Line p)) := by
  ext ⟨a, b⟩
  simp only [mem_linesThrough_iff, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨a, rfl, by rw [h]; ring⟩
  · rintro ⟨a', rfl, rfl⟩; ring

theorem card_linesThrough (z : Pt p) : #(linesThrough z) = p := by
  rw [linesThrough_eq_image, Finset.card_image_of_injective _ (linesThrough_param_injective z),
    Finset.card_univ, ZMod.card]

/-! ### Distinct lines meet in at most one point -/

theorem linePts_inter_card_le_one {ℓ ℓ' : Line p} (h : ℓ ≠ ℓ') :
    #(linePts ℓ ∩ linePts ℓ') ≤ 1 := by
  refine Finset.card_le_one.2 fun z hz w hw => ?_
  rw [mem_inter, mem_linePts, mem_linePts] at hz hw
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  by_cases haa : ℓ.1 = ℓ'.1
  · refine absurd (Prod.ext haa ?_) h
    linear_combination hz2 - hz1 - z.1 * haa
  · have key : (ℓ.1 - ℓ'.1) * z.1 = (ℓ.1 - ℓ'.1) * w.1 := by
      have h1 : ℓ.1 * z.1 + ℓ.2 = ℓ'.1 * z.1 + ℓ'.2 := by rw [← hz1, hz2]
      have h2 : ℓ.1 * w.1 + ℓ.2 = ℓ'.1 * w.1 + ℓ'.2 := by rw [← hw1, hw2]
      linear_combination h1 - h2
    have hfst : z.1 = w.1 := mul_left_cancel₀ (sub_ne_zero.2 haa) key
    exact Prod.ext hfst (by rw [hz1, hw1, hfst])

/-! ### Double counting incidences -/

theorem sum_card_inter_linePts (B : Finset (Pt p)) :
    ∑ ℓ : Line p, #(B ∩ linePts ℓ) = #B * p := by
  calc ∑ ℓ : Line p, #(B ∩ linePts ℓ)
      = ∑ ℓ : Line p, ∑ z ∈ B, if z ∈ linePts ℓ then 1 else 0 := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    _ = ∑ z ∈ B, ∑ ℓ : Line p, if z ∈ linePts ℓ then 1 else 0 := Finset.sum_comm
    _ = ∑ _z ∈ B, p := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.card_filter, ← linesThrough_eq_filter, card_linesThrough]
    _ = #B * p := by rw [Finset.sum_const, smul_eq_mul]

end Erdos664
