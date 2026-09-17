import Mathlib

/-!
# Erdős Problem #697: existence of `δ(m, α)` and the trivial bound `δ(m, α) < (m^α + 1)/m`

Let `δ(m, α)` be the density of the set of integers divisible by some `d ≡ 1 (mod m)` with
`1 < d < exp(m^α)`.  Erdős asked for the threshold `β` at which `lim_{m→∞} δ(m, α)` jumps from
`0` to `1`; Hall proved `β = 1/log 2` (OPEN question settled, not formalized here).  The problem
page records: "It is trivial that `δ(m, α) < (m^α + 1)/m → 0` if `α < 1`".

This file proves that trivial bound, together with the existence of the density (which the
formal-conjectures rendering `Erdos697.density_exists` also leaves as `sorry`), in the shape of
the formal-conjectures statements `Erdos697.density_exists` and
`Erdos697.erdos_697.variants.delta_lt`, with the definitions `Set.partialDensity`,
`Set.HasDensity` (formal-conjectures `FormalConjecturesForMathlib/Data/Set/Density.lean`) and
`Erdos697.δ` copied verbatim.

**Deviation from formal-conjectures.**  The upstream statement `delta_lt (m : ℕ) (α : ℝ) :
δ m α < (m ^ α + 1) / m` is false for `m = 0`: the set is then empty (`d ≡ 1 [MOD 0]` forces
`d = 1 ∉ Ioo 1 _`), so `δ 0 α = 0`, while the right-hand side is `(0 ^ α + 1) / 0 = 0` in Lean.
The bound is therefore proved for `m ≥ 1` (graded root in the offset form `m + 1`, plus the
formal-conjectures-shaped corollary with the hypothesis `1 ≤ m`).  Hall's theorem and the two
limit statements `erdos_697.parts.i/ii` are not claimed.

Proof.  The set is the union of the multiples of the finitely many admissible `d`, hence periodic
with period `L = lcm d`; a periodic set has natural density `|S ∩ [0, L)| / L`.  The union bound
gives `δ ≤ ∑_d 1/d` over `d = 1 + jm`, `1 ≤ j ≤ J`, `1 + Jm < exp(m^α)`, so
`δ < (1/m) ∑_{j ≤ J} 1/j ≤ (1 + log J)/m < (m^α + 1)/m` (and `δ ≤ 0 < (m^α + 1)/m` if `J = 0`).
-/

open Filter

open scoped Topology

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

open Set Real

namespace Erdos697

private lemma count_add_period (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (pp : Function.Periodic p L) (n : ℕ) :
    Nat.count p (n + L) = Nat.count p n + Nat.count p L := by
  have h : (Finset.filter p (Finset.Ico n (n + L))).card = Nat.count p L :=
    Nat.filter_Ico_card_eq_of_periodic n L p pp
  have hdisj : Disjoint (Finset.Ico 0 n) (Finset.Ico n (n + L)) :=
    Finset.Ico_disjoint_Ico_consecutive 0 n (n + L)
  rw [← h, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    ← Finset.filter_union,
    Finset.Ico_union_Ico_eq_Ico (Nat.zero_le n) (Nat.le_add_right n L)]

private lemma count_mul_period (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (pp : Function.Periodic p L) (q : ℕ) :
    Nat.count p (q * L) = q * Nat.count p L := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, count_add_period p L pp, ih, Nat.succ_mul]

private lemma partialDensity_eq_count (p : ℕ → Prop) [DecidablePred p] (b : ℕ) :
    Set.partialDensity {n : ℕ | p n} Set.univ b = (Nat.count p b : ℝ) / b := by
  have h1 : (({n : ℕ | p n} ∩ Set.univ) ∩ Set.Iio b) = ↑(Finset.filter p (Finset.range b)) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_range]
    tauto
  have h2 : ((Set.univ : Set ℕ) ∩ Set.Iio b) = ↑(Finset.range b) := by
    ext n; simp
  simp only [Set.partialDensity]
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range,
    Nat.count_eq_card_filter_range]

private lemma abs_div_sub_div_le {A B c L Q : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hc0 : 0 ≤ c) (hcL : c ≤ L)
    (h1 : Q * c ≤ A) (h2 : A ≤ (Q + 1) * c)
    (h3 : Q * L ≤ B) (h4 : B ≤ (Q + 1) * L) :
    |A / B - c / L| ≤ L / B := by
  have e : A / B - c / L = (A * L - B * c) / (B * L) := by field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < B * L),
    div_le_div_iff₀ (by positivity) hB]
  have habs : |A * L - B * c| ≤ L * L := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [mul_le_mul_of_nonneg_right h4 hc0, mul_le_mul_of_nonneg_right h1 hL.le,
        mul_le_mul_of_nonneg_right hcL hL.le]
    · linarith [mul_le_mul_of_nonneg_right h2 hL.le, mul_le_mul_of_nonneg_right h3 hc0,
        mul_le_mul_of_nonneg_right hcL hL.le]
  nlinarith [mul_le_mul_of_nonneg_right habs hB.le]

private lemma hasDensity_of_periodic (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hL : 0 < L)
    (pp : Function.Periodic p L) :
    Set.HasDensity {n : ℕ | p n} ((Nat.count p L : ℝ) / L) := by
  have hcL : Nat.count p L ≤ L := Nat.count_le p
  have key : ∀ b : ℕ, 0 < b →
      |(Nat.count p b : ℝ) / b - (Nat.count p L : ℝ) / L| ≤ (L : ℝ) / b := by
    intro b hb
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < L ∧ b = q * L + r :=
      ⟨b / L, b % L, Nat.mod_lt b hL, (Nat.div_add_mod' b L).symm⟩
    have hq1 : q * L ≤ q * L + r := Nat.le_add_right _ _
    have hq2 : q * L + r ≤ (q + 1) * L := by
      have h : (q + 1) * L = q * L + L := by ring
      omega
    have hA1 : q * Nat.count p L ≤ Nat.count p (q * L + r) := by
      rw [← count_mul_period p L pp q]; exact Nat.count_monotone p hq1
    have hA2 : Nat.count p (q * L + r) ≤ (q + 1) * Nat.count p L := by
      rw [← count_mul_period p L pp (q + 1)]; exact Nat.count_monotone p hq2
    refine abs_div_sub_div_le (Q := (q : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact_mod_cast hb
    · exact_mod_cast hL
    · exact Nat.cast_nonneg _
    · exact_mod_cast hcL
    · exact_mod_cast hA1
    · exact_mod_cast hA2
    · push_cast; exact_mod_cast hq1
    · push_cast; exact_mod_cast hq2
  have hmain : Filter.Tendsto (fun b : ℕ => (Nat.count p b : ℝ) / b) atTop
      (𝓝 ((Nat.count p L : ℝ) / L)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' (a := fun b : ℕ => (L:ℝ)/b) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with b hb
      simpa [Real.norm_eq_abs] using key b hb
    · exact tendsto_const_div_atTop_nhds_zero_nat (L:ℝ)
  exact hmain.congr (fun b => (partialDensity_eq_count p b).symm)


/-! ### The finite set of admissible divisors -/

private noncomputable def admissible (m : ℕ) (α : ℝ) : Finset ℕ :=
  (Finset.range ⌈exp ((m : ℝ) ^ α)⌉₊).filter (fun d => d ≡ 1 [MOD m] ∧ 1 < d)

private lemma admissible_props {m : ℕ} {α : ℝ} {d : ℕ} (hd : d ∈ admissible m α) :
    d ≡ 1 [MOD m] ∧ 1 < d ∧ (d : ℝ) < exp ((m : ℝ) ^ α) := by
  simp only [admissible, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil] at hd
  exact ⟨hd.2.1, hd.2.2, hd.1⟩

private lemma mem_admissible {m : ℕ} {α : ℝ} {d : ℕ} (h1 : d ≡ 1 [MOD m]) (h2 : 1 < d)
    (h3 : (d : ℝ) < exp ((m : ℝ) ^ α)) : d ∈ admissible m α := by
  simp only [admissible, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  exact ⟨h3, h1, h2⟩

private lemma setOf_admissible (m : ℕ) (α : ℝ) :
    {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp ((m : ℝ) ^ α)) ∧ d ∣ n}
      = {n : ℕ | ∃ d ∈ admissible m α, d ∣ n} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨d, h1, ⟨h2, h3⟩, h4⟩
    exact ⟨d, mem_admissible h1 (by exact_mod_cast h2) h3, h4⟩
  · rintro ⟨d, hd, h4⟩
    obtain ⟨h1, h2, h3⟩ := admissible_props hd
    exact ⟨d, h1, ⟨by exact_mod_cast h2, h3⟩, h4⟩

private lemma hasDensity_multiples (D : Finset ℕ) (h0 : ∀ d ∈ D, d ≠ 0) :
    ∃ x : ℝ, Set.HasDensity {n : ℕ | ∃ d ∈ D, d ∣ n} x := by
  have hLpos : 0 < D.lcm id := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    exact h0 x hx hx0
  have hper : Function.Periodic (fun n => ∃ d ∈ D, d ∣ n) (D.lcm id) := by
    intro n
    simp only [eq_iff_iff]
    constructor
    · rintro ⟨d, hd, hdvd⟩
      have hdL : d ∣ D.lcm id := Finset.dvd_lcm hd
      exact ⟨d, hd, by simpa using Nat.dvd_sub hdvd hdL⟩
    · rintro ⟨d, hd, hdvd⟩
      exact ⟨d, hd, hdvd.add (Finset.dvd_lcm hd)⟩
  exact ⟨_, hasDensity_of_periodic _ (D.lcm id) hLpos hper⟩

/-- For each $m$ and $\alpha$, the density of the set of integers which are divisible by
some $d \equiv 1 \pmod{m}$ with $1 < d < \exp (m ^ \alpha)$ exists. -/
theorem density_exists (m : ℕ) (α : ℝ) : ∃ δ, HasDensity
    {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp (m ^ α)) ∧ d ∣ n} δ := by
  rw [setOf_admissible m α]
  refine hasDensity_multiples _ fun d hd => ?_
  have := (admissible_props hd).2.1
  omega

/-- For each $m$ and $\alpha$, $\delta (m, \alpha)$ is the density of the set of integers which are
divisible by some $d \equiv 1 \pmod{m}$ with $1 < d < exp (m ^ \alpha)$ exists. -/
noncomputable def δ (m : ℕ) (α : ℝ) : ℝ := (density_exists m α).choose

/-! ### The union bound -/

private lemma card_filter_dvd_le (b d : ℕ) :
    (Finset.filter (fun n => d ∣ n) (Finset.range b)).card ≤ b / d + 1 := by
  have : (Finset.filter (fun n => d ∣ n) (Finset.range b)).card
      ≤ (Finset.range (b / d + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      have hxy' : x / d = y / d := hxy
      rw [← Nat.div_mul_cancel hx.2, ← Nat.div_mul_cancel hy.2, hxy']
  simpa using this

private lemma card_filter_exists_le (D : Finset ℕ) (b : ℕ) :
    (Finset.filter (fun n => ∃ d ∈ D, d ∣ n) (Finset.range b)).card
      ≤ ∑ d ∈ D, (b / d + 1) := by
  have hsub : Finset.filter (fun n => ∃ d ∈ D, d ∣ n) (Finset.range b)
      ⊆ D.biUnion (fun d => Finset.filter (fun n => d ∣ n) (Finset.range b)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnb, d, hd, hdvd⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨d, hd, by simp [hnb, hdvd]⟩
  calc (Finset.filter (fun n => ∃ d ∈ D, d ∣ n) (Finset.range b)).card
      ≤ (D.biUnion (fun d => Finset.filter (fun n => d ∣ n) (Finset.range b))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ d ∈ D, (Finset.filter (fun n => d ∣ n) (Finset.range b)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D, (b / d + 1) := Finset.sum_le_sum fun d _ => card_filter_dvd_le b d

private lemma density_le_sum (D : Finset ℕ) (x : ℝ)
    (h : Set.HasDensity {n : ℕ | ∃ d ∈ D, d ∣ n} x) :
    x ≤ ∑ d ∈ D, (1 : ℝ) / d := by
  have h' : Filter.Tendsto
      (fun b : ℕ => Set.partialDensity {n : ℕ | ∃ d ∈ D, d ∣ n} Set.univ b) atTop (𝓝 x) := h
  have htend : Filter.Tendsto (fun b : ℕ => (∑ d ∈ D, (1 : ℝ) / d) + (D.card : ℝ) / b)
      atTop (𝓝 (∑ d ∈ D, (1 : ℝ) / d)) := by
    have h1 : Filter.Tendsto (fun _ : ℕ => (∑ d ∈ D, (1 : ℝ) / d)) atTop
        (𝓝 (∑ d ∈ D, (1 : ℝ) / d)) := tendsto_const_nhds
    simpa using h1.add (tendsto_const_div_atTop_nhds_zero_nat (D.card : ℝ))
  refine le_of_tendsto_of_tendsto h' htend ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with b hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcount : (Nat.count (fun n => ∃ d ∈ D, d ∣ n) b : ℝ) ≤ ∑ d ∈ D, ((b : ℝ) / d + 1) := by
    rw [Nat.count_eq_card_filter_range]
    have h1 : ((Finset.filter (fun n => ∃ d ∈ D, d ∣ n) (Finset.range b)).card : ℝ)
        ≤ ((∑ d ∈ D, (b / d + 1) : ℕ) : ℝ) := by exact_mod_cast card_filter_exists_le D b
    refine h1.trans ?_
    push_cast
    refine Finset.sum_le_sum fun d _ => ?_
    have : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := Nat.cast_div_le
    linarith
  have hsum : (∑ d ∈ D, ((b : ℝ) / d + 1)) = (b : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by rw [mul_one_div]
  have hrw : ((∑ d ∈ D, (1 : ℝ) / d) + (D.card : ℝ) / b) * b
      = (b : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
    field_simp
  rw [partialDensity_eq_count, div_le_iff₀ hbR, hrw]
  exact hcount.trans (le_of_eq hsum)

/-! ### The harmonic-sum bound -/

private lemma admissible_index {M : ℕ} (hM : 0 < M) {α : ℝ} {d : ℕ}
    (hd : d ∈ admissible M α) :
    d = (d - 1) / M * M + 1 ∧ 1 ≤ (d - 1) / M ∧ (d - 1) / M < d := by
  obtain ⟨h1, h2, -⟩ := admissible_props hd
  have hdvd : M ∣ d - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
  have hmul : (d - 1) / M * M = d - 1 := Nat.div_mul_cancel hdvd
  have hj1 : 1 ≤ (d - 1) / M := by
    rcases Nat.eq_zero_or_pos ((d - 1) / M) with h | h
    · rw [h] at hmul; omega
    · exact h
  have hle : (d - 1) / M ≤ (d - 1) / M * M := Nat.le_mul_of_pos_right _ hM
  exact ⟨by omega, hj1, by omega⟩

private lemma sum_admissible_lt (m : ℕ) (α : ℝ) :
    ∑ d ∈ admissible (m + 1) α, (1 : ℝ) / d
      < (((m + 1 : ℕ) : ℝ) ^ α + 1) / ((m + 1 : ℕ) : ℝ) := by
  have hM0 : 0 < m + 1 := Nat.succ_pos m
  have hMR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hM0
  have hXpos : (0 : ℝ) < exp (((m + 1 : ℕ) : ℝ) ^ α) := Real.exp_pos _
  have hrhs : (0 : ℝ) < (((m + 1 : ℕ) : ℝ) ^ α + 1) / ((m + 1 : ℕ) : ℝ) := by
    have h := Real.rpow_pos_of_pos hMR α
    positivity
  rcases Finset.eq_empty_or_nonempty (admissible (m + 1) α) with hD | hD
  · rw [hD]; simpa using hrhs
  set M : ℕ := m + 1 with hMdef
  set J : ℕ := ⌈exp ((M : ℝ) ^ α)⌉₊ - 1 with hJdef
  set f : ℕ → ℕ := fun d => (d - 1) / M with hfdef
  have hfact : ∀ d ∈ admissible M α,
      d = f d * M + 1 ∧ 1 ≤ f d ∧ f d ∈ Finset.Icc 1 J := by
    intro d hd
    obtain ⟨he, hj1, hjd⟩ := admissible_index hM0 hd
    obtain ⟨-, -, hdX⟩ := admissible_props hd
    refine ⟨he, hj1, Finset.mem_Icc.mpr ⟨hj1, ?_⟩⟩
    have h1 : (f d : ℝ) < exp ((M : ℝ) ^ α) := by
      have h2 : (f d : ℝ) < (d : ℝ) := by exact_mod_cast hjd
      linarith
    have h3 : f d < ⌈exp ((M : ℝ) ^ α)⌉₊ := Nat.lt_ceil.mpr h1
    omega
  have step1 : ∑ d ∈ admissible M α, (1 : ℝ) / d
      < ∑ d ∈ admissible M α, (1 : ℝ) / ((f d : ℝ) * M) := by
    refine Finset.sum_lt_sum_of_nonempty hD fun d hd => ?_
    obtain ⟨he, hj1, -⟩ := hfact d hd
    have hfR : (0 : ℝ) < (f d : ℝ) := by exact_mod_cast hj1
    have hfM : (0 : ℝ) < (f d : ℝ) * M := by positivity
    have hlt : ((f d : ℝ) * M) < (d : ℝ) := by
      have h4 : ((f d * M : ℕ) : ℝ) < (d : ℝ) := by
        exact_mod_cast (by omega : f d * M < d)
      push_cast at h4
      linarith
    exact one_div_lt_one_div_of_lt hfM hlt
  have hinj : Set.InjOn f (admissible M α) := by
    intro x hx y hy hxy
    obtain ⟨hex, -, -⟩ := hfact x (by simpa using hx)
    obtain ⟨hey, -, -⟩ := hfact y (by simpa using hy)
    rw [hex, hey, hxy]
  have step2 : ∑ j ∈ (admissible M α).image f, (1 : ℝ) / ((j : ℝ) * M)
      = ∑ d ∈ admissible M α, (1 : ℝ) / ((f d : ℝ) * M) := Finset.sum_image hinj
  have hsubset : (admissible M α).image f ⊆ Finset.Icc 1 J := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
    exact (hfact d hd).2.2
  have step3 : ∑ j ∈ (admissible M α).image f, (1 : ℝ) / ((j : ℝ) * M)
      ≤ ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) * M) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun j _ _ => by positivity
  have step4 : ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) * M)
      = ((harmonic J : ℚ) : ℝ) / M := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_inv]
  obtain ⟨d0, hd0⟩ := hD
  have hJ1 : 1 ≤ J := by
    have h5 := (hfact d0 hd0).2.2
    rw [Finset.mem_Icc] at h5
    omega
  have hceil1 : 1 ≤ ⌈exp ((M : ℝ) ^ α)⌉₊ := by omega
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
  have hJX : (J : ℝ) < exp ((M : ℝ) ^ α) := by
    have h6 : ((⌈exp ((M : ℝ) ^ α)⌉₊ : ℕ) : ℝ) < exp ((M : ℝ) ^ α) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h7 : (J : ℝ) = (⌈exp ((M : ℝ) ^ α)⌉₊ : ℝ) - 1 := by
      rw [hJdef, Nat.cast_sub hceil1, Nat.cast_one]
    linarith
  have hlog : Real.log J < (M : ℝ) ^ α := by
    have h8 := Real.log_lt_log hJR hJX
    rwa [Real.log_exp] at h8
  have hMR' : (0 : ℝ) < (M : ℝ) := hMR
  calc ∑ d ∈ admissible M α, (1 : ℝ) / d
      < ∑ d ∈ admissible M α, (1 : ℝ) / ((f d : ℝ) * M) := step1
    _ = ∑ j ∈ (admissible M α).image f, (1 : ℝ) / ((j : ℝ) * M) := step2.symm
    _ ≤ ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) * M) := step3
    _ = ((harmonic J : ℚ) : ℝ) / M := step4
    _ ≤ (1 + Real.log J) / M := by gcongr; exact harmonic_le_one_add_log J
    _ < ((M : ℝ) ^ α + 1) / M := by
        rw [div_lt_div_iff₀ hMR' hMR']
        exact mul_lt_mul_of_pos_right (by linarith) hMR'

private lemma delta_le_sum (m : ℕ) (α : ℝ) : δ m α ≤ ∑ d ∈ admissible m α, (1 : ℝ) / d := by
  have h : Set.HasDensity {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧
      (d : ℝ) ∈ Set.Ioo 1 (exp ((m : ℝ) ^ α)) ∧ d ∣ n} (δ m α) :=
    (density_exists m α).choose_spec
  rw [setOf_admissible] at h
  exact density_le_sum _ _ h

end Erdos697

open Erdos697

/-- **Erdős #697, the trivial bound**, in the offset form `m + 1` (so `m + 1 ≥ 1` without a
hypothesis): `δ(m + 1, α) < ((m + 1)^α + 1) / (m + 1)`. -/
theorem erdos_697_delta_lt_succ (m : ℕ) (α : ℝ) :
    δ (m + 1) α < (((m + 1 : ℕ) : ℝ) ^ α + 1) / ((m + 1 : ℕ) : ℝ) := by
  exact lt_of_le_of_lt (delta_le_sum (m + 1) α) (sum_admissible_lt m α)

/-- The same bound as a closed statement (no binders), used as the graded root: there is no
`m`, `α` with `((m + 1)^α + 1) / (m + 1) ≤ δ(m + 1, α)`. -/
theorem erdos_697_delta_lt_closed :
    ¬ ∃ (m : ℕ) (α : ℝ), (((m + 1 : ℕ) : ℝ) ^ α + 1) / ((m + 1 : ℕ) : ℝ) ≤ δ (m + 1) α := by
  rintro ⟨m, α, h⟩
  exact absurd (erdos_697_delta_lt_succ m α) (not_lt.mpr h)

namespace Erdos697

/-- The formal-conjectures shape `erdos_697.variants.delta_lt`, restricted to `1 ≤ m`
(the upstream statement is false at `m = 0`, see the module docstring). -/
theorem erdos_697_delta_lt (m : ℕ) (hm : 1 ≤ m) (α : ℝ) : δ m α < (m ^ α + 1) / m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simpa using erdos_697_delta_lt_succ k α

end Erdos697
