import Jsp825.Blocks

/-!
# JSP-000825 / Erdős #992 — digits, cylinder measure and Borel–Cantelli

This file proves, for the construction of `Jsp825.Params`:

* `fract_mem_of_mem_E` — on the event `E j` the fractional part of `2 ^ m j * α` lies in
  `[3 / (8 L j), 5 / (8 L j)]`;
* `card_G` and `p_ge` — the event `E j` has probability at least `1 / (8 L j)`;
* `volume_floor_mem` — the measure of a finite union of dyadic cylinders;
* `card_B` — the exact proportion of the "no event in `[J, K]`" digit patterns;
* `volume_not_E` — `volume {α ∈ [0,1) | ∀ j ∈ [J,K], α ∉ E j} = ∏ (1 - p j)`;
* `ae_frequently_E` — if those products tend to `0`, then almost every `α ∈ [0,1]` lies in
  infinitely many `E j`.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-! ## The digit positions `M j = m j + r j` -/

/-- The last digit position used by block `j`; equal to `m (j+1)`. -/
def M (j : ℕ) : ℕ := m j + r j

theorem M_def (j : ℕ) : M j = m j + r j := rfl

theorem M_eq_m_succ (j : ℕ) : M j = m (j + 1) := rfl

theorem M_mono : Monotone M := fun _ _ h ↦ m_mono (Nat.succ_le_succ h)

theorem M_succ (j : ℕ) : M (j + 1) = M j + r (j + 1) := by
  rw [M_def, M_def, m_succ]

/-! ## Basic facts about `G j` -/

theorem G_subset (j : ℕ) : G j ⊆ Finset.range (2 ^ r j) := Finset.filter_subset _ _

theorem mem_G_iff {j g : ℕ} :
    g ∈ G j ↔ g < 2 ^ r j ∧ 3 * 2 ^ r j ≤ 8 * L j * g ∧ 8 * L j * (g + 1) ≤ 5 * 2 ^ r j := by
  simp only [G, Finset.mem_filter, Finset.mem_range]

theorem card_G_le (j : ℕ) : (G j).card ≤ 2 ^ r j := by
  calc (G j).card ≤ (Finset.range (2 ^ r j)).card := Finset.card_le_card (G_subset j)
    _ = 2 ^ r j := Finset.card_range _

/-! ## The digit lemma -/

/-- On the event `E j` the fractional part of `2 ^ m j * α` lies in `[3/(8 L j), 5/(8 L j)]`. -/
theorem fract_mem_of_mem_E {j : ℕ} {α : ℝ} (h : α ∈ E j) :
    Int.fract ((2 : ℝ) ^ m j * α) ∈ Icc (3 / (8 * L j : ℝ)) (5 / (8 * L j)) := by
  obtain ⟨hα, hg⟩ := h
  have hα0 : (0 : ℝ) ≤ α := hα.1
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ m j * α := by positivity
  set t : ℝ := Int.fract ((2 : ℝ) ^ m j * α) with ht
  set k : ℕ := ⌊(2 : ℝ) ^ m j * α⌋₊ with hk
  have hβ0 : 0 ≤ t := Int.fract_nonneg _
  have hβ1 : t < 1 := Int.fract_lt_one _
  have hyeq : (k : ℝ) + t = (2 : ℝ) ^ m j * α := by
    rw [hk, ht, natCast_floor_eq_intCast_floor hy0]
    exact Int.floor_add_fract _
  clear_value t k
  -- split off the top digits
  have hrw : (2 : ℝ) ^ (m j + r j) * α = (2 : ℝ) ^ r j * t + ((2 ^ r j * k : ℕ) : ℝ) := by
    have h1 : (2 : ℝ) ^ (m j + r j) * α = (2 : ℝ) ^ r j * ((2 : ℝ) ^ m j * α) := by
      rw [pow_add]; ring
    rw [h1, ← hyeq]
    push_cast
    ring
  have hp : (0 : ℝ) < (2 : ℝ) ^ r j := by positivity
  have hlt : ⌊(2 : ℝ) ^ r j * t⌋₊ < 2 ^ r j := by
    have h2 : (2 : ℝ) ^ r j * t < (2 : ℝ) ^ r j := by nlinarith
    rw [Nat.floor_lt (by positivity)]
    push_cast
    linarith
  have hmod : ⌊(2 : ℝ) ^ (m j + r j) * α⌋₊ % 2 ^ r j = ⌊(2 : ℝ) ^ r j * t⌋₊ := by
    rw [hrw, Nat.floor_add_natCast (by positivity), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]
  rw [hmod, mem_G_iff] at hg
  obtain ⟨-, h3, h5⟩ := hg
  have hL : (0 : ℝ) < 8 * (L j : ℝ) := by
    have h := L_pos j
    have : (0 : ℝ) < (L j : ℝ) := by exact_mod_cast h
    linarith
  have hgle : ((⌊(2 : ℝ) ^ r j * t⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ r j * t :=
    Nat.floor_le (by positivity)
  have hglt : (2 : ℝ) ^ r j * t < ((⌊(2 : ℝ) ^ r j * t⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h3' : (3 : ℝ) * (2 : ℝ) ^ r j ≤ 8 * (L j : ℝ) * ((⌊(2 : ℝ) ^ r j * t⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h3
  have h5' : 8 * (L j : ℝ) * (((⌊(2 : ℝ) ^ r j * t⌋₊ : ℕ) : ℝ) + 1) ≤ 5 * (2 : ℝ) ^ r j := by
    exact_mod_cast h5
  have hlow : 3 / (8 * (L j : ℝ)) ≤ t := by
    rw [div_le_iff₀ hL]
    refine le_of_mul_le_mul_left ?_ hp
    linarith only [h3', mul_le_mul_of_nonneg_left hgle hL.le]
  have hhigh : t ≤ 5 / (8 * (L j : ℝ)) := by
    rw [le_div_iff₀ hL]
    refine le_of_mul_le_mul_left ?_ hp
    linarith only [h5', mul_le_mul_of_nonneg_left hglt.le hL.le]
  exact ⟨hlow, hhigh⟩

/-! ## The size of `G j` -/

/-- Counting the integers `g` with `3 P ≤ Q g` and `Q (g+1) ≤ 5 P`. -/
private theorem count_window {P Q : ℕ} (hQ : 8 ≤ Q) (hPQ : 2 * Q ≤ P) (S : Finset ℕ)
    (hS : ∀ g, g < P → 3 * P ≤ Q * g → Q * (g + 1) ≤ 5 * P → g ∈ S) :
    P ≤ Q * S.card := by
  have hQ0 : 0 < Q := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = 3 * P / Q + 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 5 * P / Q := ⟨_, rfl⟩
  have hQa : Q * a = Q * (3 * P / Q) + Q := by rw [ha, Nat.mul_add, Nat.mul_one]
  have e3 : Q * (3 * P / Q) + 3 * P % Q = 3 * P := Nat.div_add_mod _ _
  have m3 : 3 * P % Q < Q := Nat.mod_lt _ hQ0
  have e5 : Q * (5 * P / Q) + 5 * P % Q = 5 * P := Nat.div_add_mod _ _
  have m5 : 5 * P % Q < Q := Nat.mod_lt _ hQ0
  have hQb : Q * b = Q * (5 * P / Q) := by rw [hb]
  have hA : Q * a ≤ 3 * P + Q := by omega
  have hA' : 3 * P ≤ Q * a := by omega
  have hB : Q * b ≤ 5 * P := by omega
  have hB' : 5 * P < Q * b + Q := by omega
  have hmul : Q * a < Q * b := by omega
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hmul
  have hsub : Finset.Ico a b ⊆ S := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    have hga : Q * a ≤ Q * g := Nat.mul_le_mul le_rfl hg.1
    have hgb : Q * (g + 1) ≤ Q * b := Nat.mul_le_mul le_rfl hg.2
    have h8 : 8 * (g + 1) ≤ Q * (g + 1) := Nat.mul_le_mul hQ le_rfl
    refine hS g (by omega) (le_trans hA' hga) (le_trans hgb hB)
  have hcard : b - a ≤ S.card := by
    have h := Finset.card_le_card hsub
    rwa [Nat.card_Ico] at h
  obtain ⟨c, hc⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have hQbc : Q * b = Q * a + Q * c := by rw [hc, Nat.mul_add]
  have hPc : P ≤ Q * c := by omega
  have hcS : c ≤ S.card := by omega
  exact le_trans hPc (Nat.mul_le_mul le_rfl hcS)

/-- The digit set of block `j` is large: `2 ^ r j ≤ 8 * L j * |G j|`. -/
theorem card_G (j : ℕ) : 2 ^ r j ≤ 8 * L j * (G j).card := by
  refine count_window (P := 2 ^ r j) (Q := 8 * L j) ?_ ?_ (G j) ?_
  · have := L_pos j; omega
  · have := sixteen_L_le j; omega
  · intro g h1 h2 h3
    exact mem_G_iff.mpr ⟨h1, h2, h3⟩

theorem p_nonneg (j : ℕ) : 0 ≤ p j := by
  rw [p]; positivity

theorem p_le_one (j : ℕ) : p j ≤ 1 := by
  rw [p, div_le_one (by positivity)]
  exact_mod_cast card_G_le j

/-- The event `E j` has probability at least `1 / (8 L j)`. -/
theorem p_ge (j : ℕ) : 1 / (8 * L j : ℝ) ≤ p j := by
  have hL : (0 : ℝ) < 8 * (L j : ℝ) := by
    have h := L_pos j
    have : (0 : ℝ) < (L j : ℝ) := by exact_mod_cast h
    linarith
  have hP : (0 : ℝ) < (2 : ℝ) ^ r j := by positivity
  have h := card_G j
  have h' : (2 : ℝ) ^ r j ≤ 8 * (L j : ℝ) * ((G j).card : ℝ) := by exact_mod_cast h
  rw [p, div_le_div_iff₀ hL hP]
  linarith

/-! ## The measure of a union of dyadic cylinders -/

theorem volume_floor_mem (M : ℕ) (B : Finset ℕ) (hB : ∀ n ∈ B, n < 2 ^ M) :
    volume {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ⌊(2 : ℝ) ^ M * α⌋₊ ∈ B}
      = ENNReal.ofReal (B.card / 2 ^ M) := by
  have hpow : (0 : ℝ) < 2 ^ M := by positivity
  have hfl : ∀ (n : ℕ) (α : ℝ), (n : ℝ) / 2 ^ M ≤ α → α < ((n : ℝ) + 1) / 2 ^ M →
      ⌊(2 : ℝ) ^ M * α⌋₊ = n := by
    intro n α h1 h2
    have hα0 : (0 : ℝ) ≤ α := le_trans (by positivity) h1
    rw [div_le_iff₀ hpow] at h1
    rw [lt_div_iff₀ hpow] at h2
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · linarith
    · linarith
  have hset : {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ⌊(2 : ℝ) ^ M * α⌋₊ ∈ B}
      = ⋃ n ∈ B, Ico ((n : ℝ) / 2 ^ M) (((n : ℝ) + 1) / 2 ^ M) := by
    ext α
    simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Ico, exists_prop]
    constructor
    · rintro ⟨⟨h0, h1⟩, hmem⟩
      refine ⟨_, hmem, ?_, ?_⟩
      · rw [div_le_iff₀ hpow]
        have := Nat.floor_le (show (0:ℝ) ≤ (2 : ℝ) ^ M * α by positivity)
        linarith
      · rw [lt_div_iff₀ hpow]
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ M * α)
        linarith
    · rintro ⟨n, hn, h1, h2⟩
      have hα0 : (0 : ℝ) ≤ α := le_trans (by positivity) h1
      have hnb : (n : ℝ) + 1 ≤ 2 ^ M := by
        have := hB n hn
        have : (n : ℝ) + 1 ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast this
        simpa using this
      have hα1 : α < 1 := by
        rw [lt_div_iff₀ hpow] at h2
        nlinarith
      exact ⟨⟨hα0, hα1⟩, by rw [hfl n α h1 h2]; exact hn⟩
  have hdisj : (B : Set ℕ).PairwiseDisjoint
      fun n : ℕ ↦ Ico ((n : ℝ) / 2 ^ M) (((n : ℝ) + 1) / 2 ^ M) := by
    intro q _ q' _ hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro α ⟨h1, h2⟩ ⟨h3, h4⟩
    exact hqq' (((hfl q α h1 h2).symm).trans (hfl q' α h3 h4))
  rw [hset, measure_biUnion_finset hdisj fun _ _ ↦ measurableSet_Ico]
  have hval : ∀ n ∈ B, volume (Ico ((n : ℝ) / 2 ^ M) (((n : ℝ) + 1) / 2 ^ M))
      = ENNReal.ofReal (1 / 2 ^ M) := by
    intro n _
    rw [Real.volume_Ico]
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast B.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-! ## Counting the digit patterns avoiding all events -/

/-- Splitting `n < a * b` into `n / b` and `n % b`. -/
theorem card_filter_divmod (a b : ℕ) (S T : Finset ℕ) (hS : S ⊆ Finset.range a)
    (hT : T ⊆ Finset.range b) :
    ((Finset.range (a * b)).filter fun n ↦ n / b ∈ S ∧ n % b ∈ T).card = S.card * T.card := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have hT0 : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    simp [hT0]
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun n ↦ (n / b, n % b)) (fun q ↦ q.1 * b + q.2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨hn.2.1, hn.2.2⟩
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_product] at hq
    have h1 : q.1 < a := Finset.mem_range.mp (hS hq.1)
    have h2 : q.2 < b := Finset.mem_range.mp (hT hq.2)
    have hsplit : q.1 * b + q.2 = q.2 + b * q.1 := by ring
    have hd : (q.1 * b + q.2) / b = q.1 := by
      rw [hsplit, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h2, Nat.zero_add]
    have hm : (q.1 * b + q.2) % b = q.2 := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · calc q.1 * b + q.2 < q.1 * b + b := by omega
        _ = (q.1 + 1) * b := by ring
        _ ≤ a * b := Nat.mul_le_mul h1 le_rfl
    · rw [hd]; exact hq.1
    · rw [hm]; exact hq.2
  · intro n _
    exact Nat.div_add_mod' n b
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_product] at hq
    have hq2 : q.2 < b := Finset.mem_range.mp (hT hq.2)
    have hsplit : q.1 * b + q.2 = q.2 + b * q.1 := by ring
    have hd : (q.1 * b + q.2) / b = q.1 := by
      rw [hsplit, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hq2, Nat.zero_add]
    have hm : (q.1 * b + q.2) % b = q.2 := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq2]
    simp [hd, hm]

/-- The digit patterns of block `j` which are *not* in `G j`. -/
def Gc (j : ℕ) : Finset ℕ := (Finset.range (2 ^ r j)).filter fun g ↦ g ∉ G j

theorem Gc_subset (j : ℕ) : Gc j ⊆ Finset.range (2 ^ r j) := Finset.filter_subset _ _

theorem card_Gc (j : ℕ) : (Gc j).card = 2 ^ r j - (G j).card := by
  have hunion : Gc j ∪ G j = Finset.range (2 ^ r j) := by
    ext g
    simp only [Gc, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact Finset.mem_range.mp (G_subset j h)
    · intro h
      by_cases hg : g ∈ G j
      · exact Or.inr hg
      · exact Or.inl ⟨h, hg⟩
  have hdisj : Disjoint (Gc j) (G j) := by
    rw [Finset.disjoint_left]
    intro g hg hg'
    exact (Finset.mem_filter.mp hg).2 hg'
  have h1 : (Gc j).card + (G j).card = 2 ^ r j := by
    calc (Gc j).card + (G j).card = (Gc j ∪ G j).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = (Finset.range (2 ^ r j)).card := by rw [hunion]
      _ = 2 ^ r j := Finset.card_range _
  omega

theorem mem_Gc_iff {j g : ℕ} (hg : g < 2 ^ r j) : g ∈ Gc j ↔ g ∉ G j := by
  simp [Gc, Finset.mem_filter, Finset.mem_range, hg]

/-- The digit patterns of the positions `< M K` that avoid all the events `E j`, `J ≤ j ≤ K`. -/
def B (J K : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ M K)).filter fun n ↦
    ∀ j ∈ Finset.Icc J K, (n / 2 ^ (M K - M j)) % 2 ^ r j ∉ G j

theorem B_mem_lt {J K n : ℕ} (h : n ∈ B J K) : n < 2 ^ M K :=
  Finset.mem_range.mp (Finset.mem_filter.mp h).1

theorem B_subset (J K : ℕ) : B J K ⊆ Finset.range (2 ^ M K) := Finset.filter_subset _ _

/-- The proportion of digit patterns avoiding all the events `E j`, `J ≤ j ≤ K`. -/
theorem card_B (J K : ℕ) (hJK : J ≤ K) :
    ((B J K).card : ℝ) / 2 ^ M K = ∏ j ∈ Finset.Icc J K, (1 - p j) := by
  have hGle : ∀ j, ((G j).card : ℝ) ≤ 2 ^ r j := by
    intro j
    exact_mod_cast card_G_le j
  induction K, hJK using Nat.le_induction with
  | base =>
    have hBJ : B J J = (Finset.range (2 ^ m J * 2 ^ r J)).filter fun n ↦
        n / 2 ^ r J ∈ Finset.range (2 ^ m J) ∧ n % 2 ^ r J ∈ Gc J := by
      rw [B, show (2 : ℕ) ^ M J = 2 ^ m J * 2 ^ r J from by rw [M_def, pow_add]]
      refine Finset.filter_congr ?_
      intro n hn
      rw [Finset.mem_range] at hn
      have hdvd : n / 2 ^ r J < 2 ^ m J := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        exact hn
      constructor
      · intro h
        refine ⟨Finset.mem_range.mpr hdvd, ?_⟩
        rw [mem_Gc_iff (Nat.mod_lt _ (by positivity))]
        have := h J (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
        simpa using this
      · rintro ⟨-, h⟩ j hj
        rw [Finset.mem_Icc] at hj
        have hjJ : j = J := by omega
        subst hjJ
        rw [mem_Gc_iff (Nat.mod_lt _ (by positivity))] at h
        simpa using h
    rw [hBJ, card_filter_divmod _ _ _ _ (subset_refl _) (Gc_subset J), Finset.card_range,
      card_Gc, Finset.Icc_self, Finset.prod_singleton]
    have hc := card_G_le J
    rw [show (2 : ℝ) ^ M J = 2 ^ m J * 2 ^ r J from by rw [M_def, pow_add]]
    rw [p]
    push_cast [Nat.cast_sub hc]
    have h1 : (2 : ℝ) ^ m J ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ r J ≠ 0 := by positivity
    field_simp
  | succ K hK ih =>
    have hdiv : ∀ j, j ≤ K → ∀ n : ℕ,
        (n / 2 ^ r (K + 1)) / 2 ^ (M K - M j) = n / 2 ^ (M (K + 1) - M j) := by
      intro j hj n
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      have h : M j ≤ M K := M_mono hj
      rw [show r (K + 1) + (M K - M j) = M (K + 1) - M j from by rw [M_succ]; omega]
    have hBS : B J (K + 1) = (Finset.range (2 ^ M K * 2 ^ r (K + 1))).filter fun n ↦
        n / 2 ^ r (K + 1) ∈ B J K ∧ n % 2 ^ r (K + 1) ∈ Gc (K + 1) := by
      rw [B, show (2 : ℕ) ^ M (K + 1) = 2 ^ M K * 2 ^ r (K + 1) from by rw [M_succ, pow_add]]
      refine Finset.filter_congr ?_
      intro n hn
      rw [Finset.mem_range] at hn
      have hdvd : n / 2 ^ r (K + 1) < 2 ^ M K := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        exact hn
      constructor
      · intro h
        constructor
        · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdvd, ?_⟩
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [hdiv j hj.2 n]
          exact h j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩)
        · rw [mem_Gc_iff (Nat.mod_lt _ (by positivity))]
          have := h (K + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
          simpa using this
      · rintro ⟨h1, h2⟩ j hj
        rw [Finset.mem_Icc] at hj
        rcases Nat.lt_or_ge j (K + 1) with hj' | hj'
        · have hjK : j ≤ K := by omega
          have := (Finset.mem_filter.mp h1).2 j (Finset.mem_Icc.mpr ⟨hj.1, hjK⟩)
          rwa [hdiv j hjK n] at this
        · have hjeq : j = K + 1 := by omega
          subst hjeq
          rw [mem_Gc_iff (Nat.mod_lt _ (by positivity))] at h2
          simpa using h2
    rw [hBS, card_filter_divmod _ _ _ _ (B_subset J K) (Gc_subset (K + 1)), card_Gc]
    rw [Finset.prod_Icc_succ_top (by omega : J ≤ K + 1), ← ih]
    rw [show (2 : ℝ) ^ M (K + 1) = 2 ^ M K * 2 ^ r (K + 1) from by rw [M_succ, pow_add]]
    have hc := card_G_le (K + 1)
    rw [p]
    push_cast [Nat.cast_sub hc]
    have h1 : (2 : ℝ) ^ M K ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ r (K + 1) ≠ 0 := by positivity
    field_simp

/-! ## The intersection of the complements is a cylinder -/

theorem floor_scale {α : ℝ} (_hα : 0 ≤ α) {j K : ℕ} (h : M j ≤ M K) :
    ⌊(2 : ℝ) ^ M j * α⌋₊ = ⌊(2 : ℝ) ^ M K * α⌋₊ / 2 ^ (M K - M j) := by
  have hsplit : (2 : ℝ) ^ M K = 2 ^ M j * 2 ^ (M K - M j) := by
    rw [← pow_add]
    congr 1
    omega
  have hne : ((2 ^ (M K - M j) : ℕ) : ℝ) ≠ 0 := by positivity
  have heq : (2 : ℝ) ^ M j * α = ((2 : ℝ) ^ M K * α) / ((2 ^ (M K - M j) : ℕ) : ℝ) := by
    rw [hsplit]
    push_cast
    field_simp
  rw [heq, Nat.floor_div_natCast]

theorem not_E_eq (J K : ℕ) (_hJK : J ≤ K) :
    {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ∀ j ∈ Finset.Icc J K, α ∉ E j}
      = {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ⌊(2 : ℝ) ^ M K * α⌋₊ ∈ B J K} := by
  ext α
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨hα, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · rw [Nat.floor_lt (by have := hα.1; positivity)]
      have h2 : (2 : ℝ) ^ M K * α < 2 ^ M K * 1 :=
        mul_lt_mul_of_pos_left hα.2 (by positivity)
      push_cast
      linarith
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hMj : M j ≤ M K := M_mono hj.2
      rw [← floor_scale hα.1 hMj]
      have := h j (Finset.mem_Icc.mpr hj)
      intro hmem
      exact this ⟨hα, hmem⟩
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    intro j hj hE
    rw [Finset.mem_Icc] at hj
    have hMj : M j ≤ M K := M_mono hj.2
    have hcond := (Finset.mem_filter.mp h).2 j (Finset.mem_Icc.mpr hj)
    rw [← floor_scale hα.1 hMj] at hcond
    exact hcond hE.2

/-- The measure of the set of `α ∈ [0,1)` avoiding every event `E j` with `J ≤ j ≤ K`. -/
theorem volume_not_E (J K : ℕ) (hJK : J ≤ K) :
    volume {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ∀ j ∈ Finset.Icc J K, α ∉ E j}
      = ENNReal.ofReal (∏ j ∈ Finset.Icc J K, (1 - p j)) := by
  rw [not_E_eq J K hJK, volume_floor_mem (M K) (B J K) fun _ hn ↦ B_mem_lt hn,
    card_B J K hJK]

/-! ## The null set of `α` in only finitely many events -/

/-- The set of `α ∈ [0,1)` lying in no event `E j` with `j ≥ J`. -/
def noEventFrom (J : ℕ) : Set ℝ :=
  ⋂ K, {α : ℝ | α ∈ Ico (0 : ℝ) 1 ∧ ∀ j ∈ Finset.Icc J K, α ∉ E j}

theorem volume_noEventFrom
    (hdiv : ∀ J : ℕ, Tendsto (fun K ↦ ∏ j ∈ Finset.Icc J K, (1 - p j)) atTop (nhds 0))
    (J : ℕ) : volume (noEventFrom J) = 0 := by
  refine nonpos_iff_eq_zero.mp ?_
  have hlim : Tendsto (fun K ↦ ENNReal.ofReal (∏ j ∈ Finset.Icc J K, (1 - p j))) atTop
      (nhds 0) := by
    have := ENNReal.tendsto_ofReal (hdiv J)
    rwa [ENNReal.ofReal_zero] at this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop J] with K hK
  rw [← volume_not_E J K hK]
  exact measure_mono (Set.iInter_subset _ K)

/-- **Borel–Cantelli.** If the products `∏_{j=J}^{K} (1 - p j)` tend to `0` for every `J`,
then almost every `α ∈ [0,1]` lies in infinitely many events `E j`. -/
theorem ae_frequently_E
    (hdiv : ∀ J : ℕ, Tendsto (fun K ↦ ∏ j ∈ Finset.Icc J K, (1 - p j)) atTop (nhds 0)) :
    ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 → ∃ᶠ j in atTop, α ∈ E j := by
  have hnull : volume ({(1 : ℝ)} ∪ ⋃ J, noEventFrom J) = 0 := by
    refine measure_union_null (measure_singleton _) ?_
    exact measure_iUnion_null fun J ↦ volume_noEventFrom hdiv J
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro α hα
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hα
  obtain ⟨hmem, hfreq⟩ := hα
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion]
  rcases eq_or_lt_of_le hmem.2 with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    rw [Filter.not_frequently, eventually_atTop] at hfreq
    obtain ⟨J, hJ⟩ := hfreq
    refine ⟨J, ?_⟩
    rw [noEventFrom, mem_iInter]
    intro K
    exact ⟨⟨hmem.1, h1⟩, fun j hj ↦ hJ j (Finset.mem_Icc.mp hj).1⟩

end Erdos992
