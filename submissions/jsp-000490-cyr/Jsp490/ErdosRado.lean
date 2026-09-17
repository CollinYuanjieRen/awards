import Jsp490.Recursion
import Jsp490.Counting

/-!
# JSP-000490 / Erdős #603 — Erdős–Rado, countable-homogeneous form

If `λ` is infinite, `#Y ≤ λ` and `#V ≥ (2^λ)⁺`, every symmetric colouring `c : V → V → Y` has a
countably infinite set `S ⊆ V` all of whose pairs of distinct elements receive one colour.

Proof: index the recursion of `Recursion.lean` by `W := (succ λ).ord.ToType`.  If every `y` were
hit by its own sequence, the code map `y ↦ (first hit, colour pattern below it)` would inject `V`
into `Σ β : W, (Iio β → Y)`, a type of cardinality `≤ 2^λ` — impossible.  So some `y` is never
hit; its sequence is injective and end-homogeneous with pattern `p : W → Y`; some fibre of `p` is
infinite and any countably infinite subset of it, pushed forward, is homogeneous.
-/

universe u

open Cardinal

namespace Erdos603

theorem erdos_rado_countable {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {V Y : Type u}
    (hV : Order.succ (2 ^ lam) ≤ #V) (hY : #Y ≤ lam) (c : V → V → Y)
    (hsymm : ∀ u v, c u v = c v u) :
    ∃ S : Set V, S.Countable ∧ S.Infinite ∧ ∃ y₀ : Y, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = y₀ := by
  classical
  -- the index type
  let W := (Order.succ lam).ord.ToType
  -- some `y` is never hit by its own sequence
  have hnot : ¬ ∀ y : V, ∃ w : W, seq c y w = y := by
    intro hall
    have h1 : #V ≤ #(Σ β : W, (Set.Iio β → Y)) := mk_le_of_injective (code_injective c hall)
    have h2 := mk_sigma_codes_le hlam hY
    have h3 := two_pow_lt_succ lam
    exact absurd (h1.trans h2) (not_le.mpr (lt_of_lt_of_le h3 hV))
  obtain ⟨y, hy⟩ := not_forall.mp hnot
  have hy' : ∀ w : W, seq c y w ≠ y := fun w h => hy ⟨w, h⟩
  -- the end-homogeneous sequence and its pattern
  have hinj : Function.Injective (seq c y) := seq_injective_of_forall_ne c y hy'
  have hcol : ∀ {v w : W}, v < w → c (seq c y v) (seq c y w) = pattern c y v :=
    fun hvw => colour_seq_of_forall_ne c y hy' hvw
  -- an infinite fibre of the pattern
  obtain ⟨y₀, hfib⟩ := exists_infinite_fiber hlam hY (pattern c y)
  obtain ⟨T, hTsub, hTc, hTi⟩ := exists_countable_infinite_subset hfib
  refine ⟨seq c y '' T, hTc.image _, hTi.image hinj.injOn, y₀, ?_⟩
  rintro u ⟨a, ha, rfl⟩ v ⟨b, hb, rfl⟩ huv
  have hab : a ≠ b := fun h => huv (by rw [h])
  have hpa : pattern c y a = y₀ := hTsub ha
  have hpb : pattern c y b = y₀ := hTsub hb
  rcases lt_or_gt_of_ne hab with h | h
  · rw [hcol h, hpa]
  · rw [hsymm, hcol h, hpb]

end Erdos603
