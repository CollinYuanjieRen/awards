import Mathlib

/-!
# JSP-000490 / Erdős #603 — cardinal arithmetic

Pure cardinal bookkeeping for the Erdős–Rado step: the index type `W := (succ λ).ord.ToType`,
the count of the "codes" `Σ β : W, (Iio β → Y)`, and the fibre pigeonhole on `W`.
-/

universe u

open Cardinal

namespace Erdos603

/-- The index type `W := (succ λ).ord.ToType` has cardinality `succ λ`. -/
theorem mk_index (lam : Cardinal.{u}) : #((Order.succ lam).ord.ToType) = Order.succ lam :=
  Cardinal.mk_ord_toType _

/-- Every initial segment of the index type has cardinality at most `λ`. -/
theorem mk_Iio_index_le (lam : Cardinal.{u}) (β : (Order.succ lam).ord.ToType) :
    #(Set.Iio β) ≤ lam := by
  have h : #(Set.Iio β) < #((Order.succ lam).ord.ToType) := Cardinal.mk_Iio_lt β (by simp)
  rw [mk_index] at h
  exact Order.lt_succ_iff.mp h

/-- The codes `Σ β, (Iio β → Y)` number at most `2 ^ λ` when `#Y ≤ λ` and `λ` is infinite. -/
theorem mk_sigma_codes_le {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {Y : Type u} (hY : #Y ≤ lam) :
    #(Σ β : (Order.succ lam).ord.ToType, (Set.Iio β → Y)) ≤ 2 ^ lam := by
  have hlam0 : lam ≠ 0 := (lt_of_lt_of_le aleph0_pos hlam).ne'
  have hpow : ℵ₀ ≤ (2 : Cardinal.{u}) ^ lam := hlam.trans (Cardinal.cantor lam).le
  have hterm : ∀ β : (Order.succ lam).ord.ToType,
      #(Set.Iio β → Y) ≤ (2 : Cardinal.{u}) ^ lam := by
    intro β
    have h1 : #(Set.Iio β → Y) = #Y ^ #(Set.Iio β) := by simp
    rw [h1]
    calc #Y ^ #(Set.Iio β) ≤ lam ^ #(Set.Iio β) := Cardinal.power_le_power_right hY
      _ ≤ lam ^ lam := Cardinal.power_le_power_left hlam0 (mk_Iio_index_le lam β)
      _ = 2 ^ lam := Cardinal.power_self_eq hlam
  calc #(Σ β : (Order.succ lam).ord.ToType, (Set.Iio β → Y))
      = sum (fun β : (Order.succ lam).ord.ToType => #(Set.Iio β → Y)) := Cardinal.mk_sigma _
    _ ≤ sum (fun _ : (Order.succ lam).ord.ToType => (2 : Cardinal.{u}) ^ lam) :=
        Cardinal.sum_le_sum _ _ hterm
    _ = #((Order.succ lam).ord.ToType) * 2 ^ lam := Cardinal.sum_const' _ _
    _ = Order.succ lam * 2 ^ lam := by rw [mk_index]
    _ ≤ 2 ^ lam * 2 ^ lam := mul_le_mul' (Order.succ_le_of_lt (Cardinal.cantor lam)) le_rfl
    _ = 2 ^ lam := Cardinal.mul_eq_self hpow

/-- `2 ^ λ < succ (2 ^ λ)`, packaged. -/
theorem two_pow_lt_succ (lam : Cardinal.{u}) : (2 : Cardinal.{u}) ^ lam < Order.succ (2 ^ lam) :=
  Order.lt_succ _

/-- Pigeonhole: a map from the index type to `Y` (with `#Y ≤ λ`, `λ` infinite) has an
infinite fibre. -/
theorem exists_infinite_fiber {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {Y : Type u} (hY : #Y ≤ lam)
    (p : (Order.succ lam).ord.ToType → Y) : ∃ y₀ : Y, (p ⁻¹' {y₀}).Infinite := by
  by_contra hcon
  have hfin : ∀ y : Y, (p ⁻¹' {y}).Finite := by
    intro y
    by_contra hy
    exact hcon ⟨y, hy⟩
  have hunion : (⋃ y : Y, p ⁻¹' {y}) = Set.univ := by
    ext x; simp
  have h1 : #((Order.succ lam).ord.ToType) ≤ #Y * ⨆ y : Y, #(p ⁻¹' {y}) := by
    have h := Cardinal.mk_iUnion_le (fun y : Y => p ⁻¹' {y})
    rwa [hunion, Cardinal.mk_univ] at h
  have h2 : (⨆ y : Y, #(p ⁻¹' {y})) ≤ ℵ₀ :=
    ciSup_le' fun y => Cardinal.mk_le_aleph0_iff.mpr (hfin y).countable.to_subtype
  have h3 : #((Order.succ lam).ord.ToType) ≤ lam :=
    h1.trans ((mul_le_mul' hY (h2.trans hlam)).trans (Cardinal.mul_eq_self hlam).le)
  rw [mk_index] at h3
  exact absurd h3 (Order.lt_succ lam).not_ge

/-- Every infinite set contains a countably infinite subset. -/
theorem exists_countable_infinite_subset {α : Type u} {s : Set α} (hs : s.Infinite) :
    ∃ t ⊆ s, t.Countable ∧ t.Infinite := by
  refine ⟨Set.range fun n : ℕ => ((hs.natEmbedding s n : s) : α), ?_, Set.countable_range _, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hs.natEmbedding s n).2
  · exact Set.infinite_range_of_injective
      (Subtype.val_injective.comp (hs.natEmbedding s).injective)

/-- A type of cardinality at least `succ (2 ^ λ)` has at least two elements. -/
theorem two_le_mk_of_succ_le {lam : Cardinal.{u}} {V : Type u} (hV : Order.succ (2 ^ lam) ≤ #V) :
    2 ≤ #V := by
  have hpos : (0 : Cardinal.{u}) < 2 ^ lam := lt_of_le_of_lt zero_le (Cardinal.cantor lam)
  have hone : (1 : Cardinal.{u}) ≤ 2 ^ lam := Cardinal.one_le_iff_ne_zero.mpr hpos.ne'
  have h2 : (2 : Cardinal.{u}) ≤ 2 ^ lam + 1 := by
    calc (2 : Cardinal.{u}) = 1 + 1 := one_add_one_eq_two.symm
      _ ≤ 2 ^ lam + 1 := add_le_add hone le_rfl
  exact h2.trans ((Cardinal.add_one_le_of_lt (two_pow_lt_succ lam)).trans hV)

/-- A type of cardinality at least `succ (2 ^ λ)` is infinite. -/
theorem infinite_of_succ_le {lam : Cardinal.{u}} (hlam : ℵ₀ ≤ lam) {V : Type u}
    (hV : Order.succ (2 ^ lam) ≤ #V) : Infinite V :=
  Cardinal.infinite_iff.mpr
    (hlam.trans (((Cardinal.cantor lam).le.trans (two_pow_lt_succ lam).le).trans hV))

end Erdos603

