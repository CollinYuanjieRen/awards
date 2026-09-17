import Mathlib

/-!
# Erdős Problem #624: the weaker statement `H(2^k) ≥ k + 1` for every `k ≥ 2`

Let `X` be a finite set of size `n` and let `H(n)` be the least `m` such that some
`f : 𝒫(X) → X` satisfies `{f(A) : A ⊆ Y} = X` for every `Y ⊆ X` with `|Y| ≥ m`.  Erdős asked
whether `H(n) − log₂ n → ∞` (OPEN; not addressed here).  The problem page records: "Erdős said
that even the weaker statement that for `n = 2^k` we have `H(n) ≥ k + 1` is open, but Alon has
provided the following simple proof: by the pigeonhole principle there are `(n−1)/2` subsets
`A_i` of size `2` such that `f(A_i)` is the same.  Any set `Y` of size `k` containing at least
`k/2` of them can have at most `2^k − ⌊k/2⌋ + 1 < 2^k = n` distinct elements in the union of the
images of `f(A)` for `A ⊆ Y`."

This file proves `H(2^k) ≥ k + 1` for every `k ≥ 2`, with the definitions `ExistsEventuallySurjective`
and `H` copied verbatim from the formal-conjectures rendering of #624 (`Fin n` as the set of
size `n`).  The statement cannot hold for all `k`: it fails for `k = 1`, since `H(2) = 1` (proved
below), so `k ≥ 2` is the optimal range.  Alon's argument as recorded needs `k ≥ 4` (the
displayed inequality `2^k − ⌊k/2⌋ + 1 < 2^k` needs `⌊k/2⌋ ≥ 2`); a simplification of it, using
two distinct `2`-subsets with the same `f`-value (there are such since `C(n, 2) > n` for
`n ≥ 4`), is given for `k ≥ 4` as `not_existsEventuallySurjective_two_pow_of_four_le`.  The
same pigeonhole idea applied to the singletons and `∅` works for all `k ≥ 2`: if `f` covered `X`
from every `k`-set `Y`, then, as `|𝒫(Y)| = 2^k = n`, `f` would be injective on each `𝒫(Y)`;
every pair `{∅, {a}}` and `{{a}, {b}}` lies in some `k`-set, so `a ↦ f({a})` would be injective
and avoid `f(∅)`, mapping `n` elements into `n − 1` values.  Together with `H(n) ≤ n` (take
`f(A) = min A`), this gives `H(2^k) ≥ k + 1`.
-/

namespace Erdos624

open Filter Finset

/--
The condition that an integer `m` ensures the existence of a function `f` covering `Fin n`
for all large enough subsets `Y`.

The property is invariant under bijection, so we use a representative `Fin n` for a finite set
of size `n`.
-/
def ExistsEventuallySurjective (n m : ℕ) : Prop :=
  ∃ (f : Finset (Fin n) → Fin n),
    ∀ (Y : Finset (Fin n)), #Y ≥ m →
      Y.powerset.image f = Finset.univ

/--
Let $H(n)$ be the minimum integer $m$ such that there is a function $f: \mathcal{P}(X) \to X$
where $X$ is a finite set of size $n$, such that for every subset $Y \subseteq X$ with $|Y| \ge m$,
the set $\{f(A) : A \subseteq Y\}$ covers $X$.
-/
noncomputable def H (n : ℕ) : ℕ :=
  if 0 < n then
    sInf {m : ℕ | ExistsEventuallySurjective n m}
  else 0

end Erdos624

open Erdos624 Finset

/-- Relaxing the threshold `m` preserves `ExistsEventuallySurjective`: the same `f` works, since
a larger `Y` is still large enough. -/
theorem existsEventuallySurjective_mono {n m m' : ℕ} (h : m ≤ m')
    (hm : ExistsEventuallySurjective n m) : ExistsEventuallySurjective n m' := by
  obtain ⟨f, hf⟩ := hm
  exact ⟨f, fun Y hY => hf Y (le_trans h hY)⟩

/-- For `n ≥ 4` there are more `2`-subsets of an `n`-set than there are elements. -/
theorem self_lt_choose_two {n : ℕ} (hn : 4 ≤ n) : n < n.choose 2 := by
  rw [Nat.choose_two_right, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 3 ≤ n - 1 := by omega
  nlinarith

/-- `m = 1` works for `n = 2`: take `f(∅) = 0` and `f(A) = 1` for `A ≠ ∅`. -/
theorem existsEventuallySurjective_two_one : ExistsEventuallySurjective 2 1 := by
  refine ⟨fun A => if A = ∅ then 0 else 1, ?_⟩
  decide

/-- `m = n` always works (for `n > 0`): with `f(A) = min A` (and `f(∅) = 0`), the only `Y` with
`|Y| ≥ n` is `X` itself, whose singletons are mapped onto `X`. -/
theorem existsEventuallySurjective_self (n : ℕ) (hn : 0 < n) :
    ExistsEventuallySurjective n n := by
  refine ⟨fun A => if h : A.Nonempty then A.min' h else ⟨0, hn⟩, ?_⟩
  intro Y hY
  have hYuniv : Y = univ := by
    refine Finset.eq_univ_of_card Y ?_
    have := Finset.card_le_univ Y
    simp only [Fintype.card_fin] at *
    omega
  subst hYuniv
  refine Finset.eq_univ_iff_forall.mpr fun x => ?_
  refine Finset.mem_image.mpr ⟨{x}, Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  simp

/-- Alon's pigeonhole step, simplified: for `k ≥ 4` and `n = 2^k`, no `f` covers `X` from every
`k`-set, because two distinct `2`-subsets share their `f`-value and a `k`-set containing both
has fewer than `2^k` image values. -/
theorem not_existsEventuallySurjective_two_pow_of_four_le (k : ℕ) (hk : 4 ≤ k) :
    ¬ ExistsEventuallySurjective (2 ^ k) k := by
  rintro ⟨f, hf⟩
  have hkn : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
  have hn4 : 4 ≤ 2 ^ k :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  have hcard : #(univ : Finset (Fin (2 ^ k))) <
      #((univ : Finset (Fin (2 ^ k))).powersetCard 2) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact self_lt_choose_two hn4
  obtain ⟨A, hA, B, hB, hAB, hfAB⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f) (fun _ _ => Finset.mem_univ _)
  have hA2 : #A = 2 := (Finset.mem_powersetCard.mp hA).2
  have hB2 : #B = 2 := (Finset.mem_powersetCard.mp hB).2
  have hunion : #(A ∪ B) ≤ k := le_trans (Finset.card_union_le A B) (by omega)
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_superset_card_eq hunion (by simpa using hkn)
  have himg := hf Y hYcard.ge
  have hinj : Set.InjOn f ↑Y.powerset := by
    refine Finset.injOn_of_card_image_eq ?_
    rw [himg, Finset.card_univ, Fintype.card_fin, Finset.card_powerset, hYcard]
  exact hAB (hinj (Finset.mem_coe.mpr (Finset.mem_powerset.mpr
      (Finset.subset_union_left.trans hYsub)))
    (Finset.mem_coe.mpr (Finset.mem_powerset.mpr
      (Finset.subset_union_right.trans hYsub))) hfAB)

/-- The pigeonhole step for every `k ≥ 2`: if `f` covered `X = Fin (2^k)` from every `k`-set,
it would be injective on each `𝒫(Y)` with `|Y| = k`, hence injective on singletons and never
equal to `f(∅)` there, mapping `2^k` elements into `2^k − 1` values. -/
theorem not_existsEventuallySurjective_two_pow (k : ℕ) (hk : 2 ≤ k) :
    ¬ ExistsEventuallySurjective (2 ^ k) k := by
  rintro ⟨f, hf⟩
  have hkn : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
  have hinjY : ∀ Y : Finset (Fin (2 ^ k)), #Y = k → Set.InjOn f ↑Y.powerset := by
    intro Y hY
    refine Finset.injOn_of_card_image_eq ?_
    rw [hf Y hY.ge, Finset.card_univ, Fintype.card_fin, Finset.card_powerset, hY]
  have key : ∀ S : Finset (Fin (2 ^ k)), #S ≤ 2 →
      ∀ A B, A ⊆ S → B ⊆ S → f A = f B → A = B := by
    intro S hS A B hA hB hAB
    obtain ⟨Y, hSY, hYk⟩ := Finset.exists_superset_card_eq (le_trans hS hk) (by simpa using hkn)
    exact hinjY Y hYk (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hA.trans hSY)))
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hB.trans hSY))) hAB
  have hg : Function.Injective (fun a : Fin (2 ^ k) => f {a}) := by
    intro a b hab
    by_contra hne
    have := key {a, b} (by rw [Finset.card_pair hne]) {a} {b} (by simp) (by simp) hab
    exact hne (Finset.singleton_inj.mp this)
  have hg0 : ∀ a : Fin (2 ^ k), f {a} ≠ f ∅ := by
    intro a h
    have := key {a} (by simp) {a} ∅ (by simp) (by simp) h
    simp at this
  have hsub : (univ.image fun a : Fin (2 ^ k) => f {a}) ⊆ univ.erase (f ∅) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨hg0 a, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, Fintype.card_fin] at h1
  have : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

/-- **Erdős #624, the weaker statement (Alon)**: `H(2^k) ≥ k + 1` for every `k ≥ 2`. -/
theorem erdos_624_alon (k : ℕ) (hk : 2 ≤ k) : k + 1 ≤ H (2 ^ k) := by
  rw [H, ite_eq_left (Nat.two_pow_pos k)]
  refine le_csInf ⟨2 ^ k, existsEventuallySurjective_self _ (Nat.two_pow_pos k)⟩ fun m hm => ?_
  by_contra hcon
  exact not_existsEventuallySurjective_two_pow k hk
    (existsEventuallySurjective_mono (by omega) hm)

/-- Closed form of `erdos_624_alon`: no `k ≥ 2` has `H(2^k) < k + 1`. -/
theorem erdos_624_alon_closed : ¬ ∃ k : ℕ, 2 ≤ k ∧ H (2 ^ k) < k + 1 := by
  rintro ⟨k, hk, hlt⟩
  exact absurd (erdos_624_alon k hk) (not_le.mpr hlt)

/-- The statement `H(2^k) ≥ k + 1` fails at `k = 1`, so `k ≥ 2` is optimal: `H(2) = 1` (with `f(∅) = 0` and
`f({0}) = f({1}) = 1`, every nonempty `Y ⊆ {0, 1}` has `{f(A) : A ⊆ Y} = {0, 1}`, while `m = 0`
fails at `Y = ∅`). -/
theorem H_two_eq_one : H 2 = 1 := by
  rw [H, ite_eq_left (by norm_num : (0:ℕ) < 2)]
  refine le_antisymm (Nat.sInf_le existsEventuallySurjective_two_one)
    (le_csInf ⟨1, existsEventuallySurjective_two_one⟩ fun m hm => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exfalso
    obtain ⟨f, hf⟩ := hm
    have hu := hf ∅ (by simp)
    rw [Finset.powerset_empty, Finset.image_singleton] at hu
    have hcard := congrArg Finset.card hu
    simp at hcard
  · exact hpos
