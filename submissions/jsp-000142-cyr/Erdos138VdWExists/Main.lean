import Mathlib

/-!
# Erdős Problem #138: existence of the van der Waerden numbers (van der Waerden's theorem)

The van der Waerden number `W(k)` is the least `N` such that every `2`-colouring of
`{1, …, N}` contains a monochromatic `k`-term arithmetic progression.  Erdős asked for better
bounds on `W(k)`, e.g. whether `W(k)^{1/k} → ∞` (OPEN, $500; not addressed here).  The
formal-conjectures rendering of the problem defines `W` as the infimum of the set
`monoAP_guarantee_set 2 k` of all such `N`, and leaves the fact that this set is nonempty for
every number of colours `r` and every length `k` — van der Waerden's theorem — as a `sorry`
(`Erdos138.monoAP_guarantee_set_nonempty`, tagged "research solved").  This file proves that
statement, in the exact formal-conjectures shape, with the definitions `Set.IsAPOfLengthWith`,
`Set.IsAPOfLength`, `ContainsMonoAPofLength` (formal-conjectures
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`) and `Erdos138.monoAP_guarantee_set`
copied verbatim.  None of the bounds on `W(k)` (Berlekamp, Gowers, Kozik–Shabanov, DeepMind) is
claimed.

Proof.  By the Hales–Jewett theorem (Mathlib `Combinatorics.Line.exists_mono_in_high_dimension`)
there is a finite index type `ι` such that every `r`-colouring of the cube `ι → Fin k` has a
monochromatic combinatorial line.  Colour `v : ι → Fin k` by the colour of `1 + ∑ᵢ vᵢ ∈ {1, …, N}`
with `N = k·|ι| + 1`; a monochromatic line with `s ≥ 1` free coordinates and fixed-part sum
`b` gives the monochromatic progression `1 + b + x·s`, `x < k`, of length `k` and difference `s`.
-/

open Nat Filter

open scoped ENat

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/--
A set $S$ is an arithmetic progression of length $l$ if it is an arithmetic progression of
length $l$ with some first term and some difference.
-/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- A colouring of a set `M` contains a monochromatic arithmetic progression of length `k`
(formal-conjectures definition). -/
def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

namespace Erdos138

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.
A number `N` belongs to this set if, for a given number of colors `r` and an arithmetic
progression length `k`, any `r`-coloring of the integers `{1, ..., N}` must contain a
monochromatic arithmetic progression of length `k`.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

end Erdos138

open Erdos138

private lemma sum_fin_val_le {ι : Type} [Fintype ι] {k : ℕ} (v : ι → Fin k) :
    ∑ i, ((v i : ℕ)) ≤ Fintype.card ι * k := by
  calc ∑ i, ((v i : ℕ)) ≤ ∑ _i : ι, k := Finset.sum_le_sum fun i _ => (v i).isLt.le
    _ = Fintype.card ι * k := by
        simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

private lemma isAPOfLength_empty_zero : (∅ : Set ℕ).IsAPOfLength 0 := by
  refine ⟨0, 0, ?_, ?_⟩
  · show Set.encard (∅ : Set ℕ) = 0
    simp
  · ext y
    simp

/-- **Van der Waerden's theorem** in the formal-conjectures shape
`Erdos138.monoAP_guarantee_set_nonempty`: for every number of colours `r` and every length `k`
some `N` forces a monochromatic `k`-term arithmetic progression. -/
theorem monoAP_guarantee_set_nonempty (r k : ℕ) : (monoAP_guarantee_set r k).Nonempty := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, ?_⟩
    intro coloring
    refine ⟨coloring ⟨1, by simp⟩, ∅, ?_, by simp⟩
    rw [Set.image_empty]
    exact isAPOfLength_empty_zero
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι * k + 1, ?_⟩
  intro coloring
  have hmem : ∀ v : ι → Fin k,
      1 + ∑ i, ((v i : ℕ)) ∈ Finset.Icc 1 (Fintype.card ι * k + 1) := by
    intro v
    have h := sum_fin_val_le v
    rw [Finset.mem_Icc]
    omega
  obtain ⟨l, c, hl⟩ := hι (fun v => coloring ⟨1 + ∑ i, ((v i : ℕ)), hmem v⟩)
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  have hspos : 0 < s.card := by
    refine Finset.card_pos.mpr ⟨l.proper.choose, ?_⟩
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
  set b : ℕ := ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y : Fin k => (y : ℕ))).getD 0 with hb
  have key : ∀ (n : ℕ) (hn : n < k),
      ∑ i, ((l (⟨n, hn⟩ : Fin k) i : ℕ)) = n * s.card + b := by
    intro n hn
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => n) ?_, Finset.sum_const, smul_eq_mul, mul_comm]
      intro i hi
      rw [hs, Finset.mem_filter] at hi
      rw [l.apply_none _ _ hi.2]
    · rw [hb]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
      simp [← hy]
  have hptmem : ∀ (n : ℕ), n < k →
      1 + b + n * s.card ∈ Finset.Icc 1 (Fintype.card ι * k + 1) := by
    intro n hn
    have h := hmem (l (⟨n, hn⟩ : Fin k))
    rw [key n hn] at h
    have he : 1 + (n * s.card + b) = 1 + b + n * s.card := by ring
    rwa [he] at h
  have hinj : Set.InjOn (fun n : ℕ => 1 + b + n * s.card) {n : ℕ | n < k} := by
    intro n₁ _ n₂ _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hspos (by omega)
  have hAP : ∀ T : Set ℕ,
      T = {x : ℕ | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), 1 + b + n • s.card = x} →
      T.IsAPOfLengthWith (k : ℕ∞) (1 + b) s.card := by
    rintro T rfl
    refine ⟨?_, rfl⟩
    have himg : {x : ℕ | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), 1 + b + n • s.card = x}
        = (fun n : ℕ => 1 + b + n * s.card) '' {n : ℕ | n < k} := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, by exact_mod_cast hn, by simp⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, by exact_mod_cast hn, by simp⟩
    show Set.encard _ = _
    rw [himg, hinj.encard_image, Set.Nat.encard_range]
  refine ⟨c, {m | ∃ n : ℕ, ∃ _ : n < k, (m : ℕ) = 1 + b + n * s.card}, ⟨1 + b, s.card, ?_⟩, ?_⟩
  · refine hAP _ ?_
    ext y
    constructor
    · rintro ⟨m, ⟨n, hn, hmn⟩, rfl⟩
      refine ⟨n, by exact_mod_cast hn, ?_⟩
      simp [hmn]
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < k := by exact_mod_cast hn
      exact ⟨⟨1 + b + n * s.card, hptmem n hn'⟩, ⟨n, hn', rfl⟩, by simp⟩
  · rintro m ⟨n, hn, hmn⟩
    have hm : m = ⟨1 + ∑ i, ((l (⟨n, hn⟩ : Fin k) i : ℕ)), hmem _⟩ := by
      apply Subtype.ext
      show (m : ℕ) = 1 + ∑ i, ((l (⟨n, hn⟩ : Fin k) i : ℕ))
      rw [hmn, key n hn]
      ring
    rw [hm]
    exact hl ⟨n, hn⟩
