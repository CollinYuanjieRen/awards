import Mathlib
import Jsp827.Tower.Basic
import Jsp827.Arith
import Jsp827.Circle

/-!
# One scale of Marstrand's construction (discrete log-coordinate version)

Fix `J ≥ 3`, the list `p : Fin d → ℕ` of all primes `≤ 2^J` (distinct), a box side `N`
with `J ∣ N`, and a tower base `W` for the action `e ↦ gvalC p e • x` on the unit circle
with pairwise disjoint levels `level e = f e ⁻¹' W`, `e ∈ box (fun _ ↦ N)`.

* `L e := Nat.log 2 (gvalC p e)`; the *scale* of a level is `L e % J`.
* `badSet := ⋃ {level e : L e % J ∈ {0,1}}`  (this is `E` at this scale);
* `goodSet j₀ := ⋃ {level e : (∀ i, J ≤ e i) ∧ j₀ ≤ L e % J}`.

Counting claim: if `x ∈ level e` with `∀ i, J ≤ e i` and `j := L e % J ≥ 1`, then for every
`n ∈ (2^(j-1), 2^j]` we have `n • x ∈ badSet`, so at least half of the `n ≤ 2^j` visit
`badSet`.  Measure claims: `μ badSet ≤ 2 / J` and
`μ (goodSet j₀) ≥ (1 - ε) * (1 - J/N)^d * (1 - j₀/J)` when the tower has measure `≥ 1-ε`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos994

open RokhlinTower

attribute [local instance] Classical.propDecidable

variable {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)

/-- The action (abbreviation for readability). -/
noncomputable abbrev act : NatAction (volume : Measure UnitAddCircle) d :=
  smoothAction p fun i => (hp i).pos

/-- `Nat.log 2` of the multiplier of a level. -/
def L (e : Fin d → ℕ) : ℕ := Nat.log 2 (gvalC p e)

/-- The set of levels carrying the bad set at scale `J`. -/
def badIdx (J N : ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ : Fin d => N).filter fun e => L p e % J = 0 ∨ L p e % J = 1

/-- The set of levels carrying the good set at scale `J` with threshold `j₀`. -/
def goodIdx (J N j₀ : ℕ) : Finset (Fin d → ℕ) :=
  (box fun _ : Fin d => N).filter fun e => (∀ i, J ≤ e i) ∧ j₀ ≤ L p e % J

/-- The bad set: union of the bad levels over the base `W`. -/
def badSet (J N : ℕ) (W : Set UnitAddCircle) : Set UnitAddCircle :=
  ⋃ e ∈ badIdx p J N, (act p hp).f e ⁻¹' W

/-- The good set. -/
def goodSet (J N j₀ : ℕ) (W : Set UnitAddCircle) : Set UnitAddCircle :=
  ⋃ e ∈ goodIdx p J N j₀, (act p hp).f e ⁻¹' W

/-- Hypothesis packaging the choice of primes: `p` enumerates exactly the primes `≤ 2^J`. -/
def PrimesUpTo (J : ℕ) : Prop :=
  Function.Injective p ∧ ∀ q : ℕ, q.Prime → q ≤ 2 ^ J → ∃ i, p i = q

/-- The action is multiplication by `gvalC p e`. -/
lemma act_apply (e : Fin d → ℕ) (x : UnitAddCircle) : (act p hp).f e x = gvalC p e • x := rfl

/-- `gvalC` agrees with `gval`. -/
lemma gvalC_eq_gval (e : Fin d → ℕ) : gvalC p e = gval p e := rfl

/-- **Counting claim (C′).**  For `x` in a good level, every `n` in the dyadic range
`(2^(j-1), 2^j]` (with `j = L e % J`) sends `x` into the bad set. -/
theorem nsmul_mem_badSet {J N j₀ : ℕ} (hJ : 3 ≤ J) (hprimes : PrimesUpTo p J)
    {W : Set UnitAddCircle} {e : Fin d → ℕ} (he : e ∈ goodIdx p J N j₀) (hj₀ : 1 ≤ j₀)
    {x : UnitAddCircle} (hx : x ∈ (act p hp).f e ⁻¹' W) {n : ℕ}
    (hlo : 2 ^ (L p e % J - 1) < n) (hhi : n ≤ 2 ^ (L p e % J)) :
    n • x ∈ badSet p hp J N W := by
  classical
  rw [goodIdx, Finset.mem_filter] at he
  obtain ⟨hbox, hge, hj₀le⟩ := he
  set j : ℕ := L p e % J with hjdef
  have hj1 : 1 ≤ j := le_trans hj₀ hj₀le
  have hjJ : j < J := Nat.mod_lt _ (by omega)
  have h1le : (1 : ℕ) ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hlo.le
  have hnJ : n ≤ 2 ^ J := hhi.trans (Nat.pow_le_pow_right (by norm_num) hjJ.le)
  set a : Fin d → ℕ := expVec p n with hadef
  have hga : gvalC p a = n := by
    rw [gvalC_eq_gval]
    exact gval_expVec hp hprimes.1 hn0 fun q hq hqd ↦
      hprimes.2 q hq ((Nat.le_of_dvd hn0 hqd).trans hnJ)
  have hale : ∀ i, a i ≤ e i := fun i ↦ (expVec_le_of_le_pow hp hnJ i).trans (hge i)
  have hsub : (e - a) + a = e := by
    funext i
    have := hale i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have key : (act p hp).f (e - a) (n • x) = (act p hp).f e x := by
    rw [← hga, ← act_apply p hp a x, ← NatAction.f_apply_add, hsub]
  have hmemW : n • x ∈ (act p hp).f (e - a) ⁻¹' W := by
    simp only [Set.mem_preimage, key]
    exact hx
  have hsplit : gvalC p (e - a) * n = gvalC p e := by
    rw [← hga, ← gvalC_add, hsub]
  have hg0 : 0 < gvalC p e := gvalC_pos (fun i ↦ (hp i).pos) e
  have hdvd : n ∣ gvalC p e := ⟨gvalC p (e - a), by rw [← hsplit, Nat.mul_comm]⟩
  have hdiv : gvalC p e / n = gvalC p (e - a) := by
    rw [← hsplit, Nat.mul_div_cancel _ hn0]
  have hjL : j ≤ L p e := Nat.mod_le _ _
  have hlog : L p (e - a) = L p e - j ∨ L p (e - a) = L p e - j + 1 := by
    have := log_div_mem (g := gvalC p e) (n := n) (j := j) hg0 hdvd hj1 hlo hhi hjL
    rwa [hdiv] at this
  have hmod : L p e - j = J * (L p e / J) := by
    have := Nat.div_add_mod (L p e) J
    omega
  have hbad : e - a ∈ badIdx p J N := by
    refine Finset.mem_filter.mpr ⟨mem_box.mpr fun i ↦ ?_, ?_⟩
    · have := (mem_box.mp hbox) i
      simp only [Pi.sub_apply]
      omega
    · rcases hlog with h | h
      · left
        rw [h, hmod, Nat.mul_mod_right]
      · right
        rw [h, hmod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact Set.mem_biUnion hbad hmemW

/-- At least half of the multiples `1 ≤ n ≤ 2^j` of a good point visit the bad set. -/
theorem half_visits {J N j₀ : ℕ} (hJ : 3 ≤ J) (hprimes : PrimesUpTo p J)
    {W : Set UnitAddCircle} {e : Fin d → ℕ} (he : e ∈ goodIdx p J N j₀) (hj₀ : 1 ≤ j₀)
    {x : UnitAddCircle} (hx : x ∈ (act p hp).f e ⁻¹' W) :
    2 ^ (L p e % J - 1) ≤
      ((Finset.Icc 1 (2 ^ (L p e % J))).filter fun n => n • x ∈ badSet p hp J N W).card := by
  classical
  have hj1 : 1 ≤ L p e % J :=
    hj₀.trans (Finset.mem_filter.mp he).2.2
  set j : ℕ := L p e % J with hjdef
  have hsub : Finset.Ioc (2 ^ (j - 1)) (2 ^ j) ⊆
      (Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ badSet p hp J N W := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hn.2⟩, ?_⟩
    · have : (1 : ℕ) ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
      omega
    · exact nsmul_mem_badSet p hp hJ hprimes he hj₀ hx hn.1 hn.2
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hpow : (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring
  omega

/-- Every residue `r < J` is realised by `s ↦ (s + c) % J` for some `s < J`. -/
lemma exists_add_mod_eq {J c r : ℕ} (hJ : 0 < J) (hr : r < J) : ∃ s, s < J ∧ (s + c) % J = r := by
  have h1 : J * (c / J) + c % J = c := Nat.div_add_mod c J
  have h2 : c % J < J := Nat.mod_lt _ hJ
  refine ⟨(r + (J - c % J)) % J, Nat.mod_lt _ hJ, ?_⟩
  rw [Nat.mod_add_mod]
  have h3 : r + (J - c % J) + c = J * (c / J + 1) + r := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- In an interval `[A, B)` with endpoints divisible by `J`, every residue class of
`a ↦ (a + c) % J` has exactly `(B - A) / J` elements. -/
lemma card_filter_Ico_mod {J A B c r : ℕ} (hJ : 0 < J) (hAB : A ≤ B) (hA : J ∣ A) (hB : J ∣ B)
    (hr : r < J) :
    ((Finset.Ico A B).filter fun a ↦ (a + c) % J = r).card = (B - A) / J := by
  classical
  obtain ⟨s, hsJ, hs⟩ := exists_add_mod_eq hJ hr
  obtain ⟨u, hu⟩ := id hA
  obtain ⟨k, hk⟩ : ∃ k, B - A = J * k := Nat.dvd_sub hB hA
  have hkv : (B - A) / J = k := by rw [hk, Nat.mul_div_cancel_left _ hJ]
  rw [hkv, ← Finset.card_range k]
  refine Finset.card_nbij' (fun a ↦ (a - A) / J) (fun t ↦ A + J * t + s) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at ha ⊢
    exact Nat.div_lt_of_lt_mul (by omega)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    have hlt : J * t + s < J * k := by
      calc J * t + s < J * t + J := by omega
        _ = J * (t + 1) := by ring
        _ ≤ J * k := Nat.mul_le_mul_left _ (by omega)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hsplit : A + J * t + s + c = J * (u + t) + (s + c) := by rw [hu]; ring
    rw [hsplit, Nat.mul_add_mod, hs]
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
    obtain ⟨⟨hAa, haB⟩, hmod⟩ := ha
    have hsa : a % J = s := by
      have h : a + c ≡ s + c [MOD J] := by rw [Nat.ModEq, hmod, hs]
      have h' := Nat.ModEq.add_right_cancel' c h
      rw [Nat.ModEq] at h'
      rw [h', Nat.mod_eq_of_lt hsJ]
    have haA : (a - A) % J = s := by
      have heq : J * u + (a - A) = a := by omega
      have hmm := Nat.mul_add_mod J u (a - A)
      rw [heq] at hmm
      rw [← hmm, hsa]
    have hd := Nat.div_add_mod (a - A) J
    simp only
    omega
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    have hsimp : A + J * t + s - A = J * t + s := by omega
    simp only
    rw [hsimp, Nat.mul_add_div hJ, Nat.div_eq_of_lt hsJ, Nat.add_zero]

/-- Counting the elements of `[A, B)` whose residue satisfies `Q`. -/
lemma card_filter_Ico_residue {J A B c : ℕ} (hJ : 0 < J) (hAB : A ≤ B) (hA : J ∣ A) (hB : J ∣ B)
    (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J)).card
      = ((Finset.range J).filter Q).card * ((B - A) / J) := by
  classical
  have hmaps : ∀ a ∈ (Finset.Ico A B).filter fun a ↦ Q ((a + c) % J),
      (a + c) % J ∈ (Finset.range J).filter Q := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hJ), ha.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ r ∈ (Finset.range J).filter Q,
      (((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J)).filter
        fun a ↦ (a + c) % J = r).card = (B - A) / J := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.filter_filter]
    have heq : ((Finset.Ico A B).filter fun a ↦ Q ((a + c) % J) ∧ (a + c) % J = r)
        = (Finset.Ico A B).filter fun a ↦ (a + c) % J = r := by
      ext a
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h.2 ▸ hr.2, h.2⟩⟩
    rw [heq, card_filter_Ico_mod hJ hAB hA hB hr.1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]


/-- `Nat.log 2` of `2 ^ a * m` splits off the power of two. -/
lemma log_two_pow_mul (a : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Nat.log 2 (2 ^ a * m) = a + Nat.log 2 m := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : (2 : ℕ) ^ (n + 1) * m = 2 ^ n * m * 2 := by ring
    rw [h, Nat.log_mul_base (by norm_num) (Nat.mul_ne_zero (pow_ne_zero n two_ne_zero) hm), ih]
    omega

include hp in
/-- The scale splits as the exponent at the prime `2` plus the log of the remaining factor. -/
lemma L_eq_add {i₀ : Fin d} (hp2 : p i₀ = 2) (e : Fin d → ℕ) :
    L p e = e i₀ + Nat.log 2 (∏ i ∈ Finset.univ.erase i₀, p i ^ e i) := by
  have hpos : (0 : ℕ) < ∏ i ∈ Finset.univ.erase i₀, p i ^ e i :=
    Finset.prod_pos fun i _ ↦ pow_pos (hp i).pos _
  have hsplit : gvalC p e = 2 ^ e i₀ * ∏ i ∈ Finset.univ.erase i₀, p i ^ e i := by
    rw [gvalC, ← Finset.mul_prod_erase Finset.univ (fun i ↦ p i ^ e i) (Finset.mem_univ i₀), hp2]
  rw [L, hsplit, log_two_pow_mul _ hpos.ne']

include hp in
/-- Counting the exponent vectors in the cube `[A, B)^d` whose scale residue satisfies `Q`. -/
lemma card_filter_scale {i₀ : Fin d} (hp2 : p i₀ = 2) {J A B : ℕ} (hJ : 0 < J) (hAB : A ≤ B)
    (hA : J ∣ A) (hB : J ∣ B) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B).filter fun e ↦ Q (L p e % J)).card
      = (∏ _i ∈ Finset.univ.erase i₀, (B - A)) *
          (((Finset.range J).filter Q).card * ((B - A) / J)) := by
  classical
  set S : Finset (Fin d → ℕ) :=
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B).filter fun e ↦ Q (L p e % J) with hSdef
  set T : Finset (Fin d → ℕ) :=
    Fintype.piFinset (Function.update (fun _ : Fin d ↦ Finset.Ico A B) i₀ {0}) with hTdef
  have hmaps : ∀ e ∈ S, Function.update e i₀ 0 ∈ T := by
    intro e he
    rw [hSdef, Finset.mem_filter, Fintype.mem_piFinset] at he
    rw [hTdef, Fintype.mem_piFinset]
    intro i
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact he.1 i
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ b ∈ T, (S.filter fun e ↦ Function.update e i₀ 0 = b).card
      = ((Finset.range J).filter Q).card * ((B - A) / J) := by
    intro b hb
    rw [hTdef, Fintype.mem_piFinset] at hb
    have hb0 : b i₀ = 0 := by have := hb i₀; simpa using this
    have hbI : ∀ i, i ≠ i₀ → b i ∈ Finset.Ico A B := by
      intro i hi
      have := hb i
      rwa [Function.update_of_ne hi] at this
    set c : ℕ := Nat.log 2 (∏ i ∈ Finset.univ.erase i₀, p i ^ b i) with hcdef
    rw [← card_filter_Ico_residue (c := c) hJ hAB hA hB Q]
    refine Finset.card_nbij' (fun e ↦ e i₀) (fun a ↦ Function.update b i₀ a) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, hSdef, Fintype.mem_piFinset] at he
      obtain ⟨⟨hmem, hQ⟩, hupd⟩ := he
      have hrest : ∏ i ∈ Finset.univ.erase i₀, p i ^ e i
          = ∏ i ∈ Finset.univ.erase i₀, p i ^ b i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [← hupd, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [L_eq_add p hp hp2 e, hrest, ← hcdef] at hQ
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hmem i₀, hQ⟩)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
      have hrest : ∏ i ∈ Finset.univ.erase i₀, p i ^ (Function.update b i₀ a) i
          = ∏ i ∈ Finset.univ.erase i₀, p i ^ b i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hmem : Function.update b i₀ a ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Ico A B := by
        rw [Fintype.mem_piFinset]
        intro i
        show Function.update b i₀ a i ∈ Finset.Ico A B
        rcases eq_or_ne i i₀ with rfl | hi
        · rw [Function.update_self]
          exact Finset.mem_Ico.mpr ha.1
        · rw [Function.update_of_ne hi]
          exact hbI i hi
      have hQa : Q (L p (Function.update b i₀ a) % J) := by
        rw [L_eq_add p hp hp2 (Function.update b i₀ a), hrest, Function.update_self, ← hcdef]
        exact ha.2
      have hback : Function.update (Function.update b i₀ a) i₀ 0 = b := by
        funext i
        rcases eq_or_ne i i₀ with rfl | hi
        · simp [hb0]
        · simp [Function.update_of_ne hi]
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hQa⟩, hback⟩)
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter] at he
      funext i
      show Function.update b i₀ (e i₀) i = e i
      rcases eq_or_ne i i₀ with rfl | hi
      · rw [Function.update_self]
      · rw [Function.update_of_ne hi, ← he.2, Function.update_of_ne hi]
    · intro a _
      show Function.update b i₀ a i₀ = a
      rw [Function.update_self]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  have hcards : ∀ i : Fin d,
      (Function.update (fun _ : Fin d ↦ Finset.Ico A B) i₀ ({0} : Finset ℕ) i).card
        = Function.update (fun _ : Fin d ↦ B - A) i₀ 1 i := by
    intro i
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · simp [Function.update_of_ne hi, Nat.card_Ico]
  rw [hTdef, Fintype.card_piFinset, Finset.prod_congr rfl fun i _ ↦ hcards i,
    Finset.prod_update_of_mem (Finset.mem_univ i₀), one_mul, ← Finset.erase_eq]

/-- The measure of a union of levels of an admissible tower. -/
lemma measure_levels {N : ℕ} {W : Set UnitAddCircle}
    (hW : (act p hp).Admissible (fun _ ↦ N) W) {S : Finset (Fin d → ℕ)}
    (hS : S ⊆ box fun _ : Fin d ↦ N) :
    volume (⋃ e ∈ S, (act p hp).f e ⁻¹' W) = S.card * volume W := by
  have hd : (↑S : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ (act p hp).f k ⁻¹' W :=
    fun k hk l hl hkl ↦ hW.2 k (hS (by simpa using hk)) l (hS (by simpa using hl)) hkl
  have hm : ∀ k ∈ S, MeasurableSet ((act p hp).f k ⁻¹' W) :=
    fun k _ ↦ (act p hp).measurable k hW.1
  rw [measure_biUnion_finset hd hm]
  simp only [(act p hp).measure_preimage _ hW.1, Finset.sum_const, nsmul_eq_mul]

/-- Every set on the unit circle has finite measure. -/
lemma volume_ne_top (W : Set UnitAddCircle) : volume W ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ W))
  rw [UnitAddCircle.measure_univ]
  exact ENNReal.one_ne_top

/-- The number of levels in the box `[0, N)^d`. -/
lemma card_box_const (N : ℕ) : (box fun _ : Fin d ↦ N).card = N ^ d := by
  rw [card_box]
  simp

/-- **Measure claim for the bad set.** -/
theorem measure_badSet_le {J N : ℕ} (hJ : 0 < J) (hJN : J ∣ N) (hp2 : ∃ i, p i = 2)
    {W : Set UnitAddCircle} (hW : (act p hp).Admissible (fun _ => N) W) :
    (volume (badSet p hp J N W)).toReal ≤ 2 / J := by
  classical
  obtain ⟨i₀, hi₀⟩ := hp2
  have hbox : (box fun _ : Fin d ↦ N) = Fintype.piFinset fun _ : Fin d ↦ Finset.Ico 0 N := by
    simp only [box, Finset.range_eq_Ico]
  have hcardbad : (badIdx p J N).card
      = (∏ _i ∈ Finset.univ.erase i₀, (N - 0)) *
          (((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card * ((N - 0) / J)) := by
    rw [badIdx, hbox]
    exact card_filter_scale p hp hi₀ hJ (Nat.zero_le N) (dvd_zero J) hJN
      (fun r ↦ r = 0 ∨ r = 1)
  simp only [Nat.sub_zero] at hcardbad
  have hcf : ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card ≤ 2 := by
    have hsub : (Finset.range J).filter (fun r ↦ r = 0 ∨ r = 1) ⊆ ({0, 1} : Finset ℕ) := by
      intro r hr
      have h := (Finset.mem_filter.mp hr).2
      simpa using h
    calc ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card
        ≤ ({0, 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 2 := by decide
  have hprodN : N ^ d = N * ∏ _i ∈ Finset.univ.erase i₀, N := by
    rw [Finset.mul_prod_erase Finset.univ (fun _ : Fin d ↦ N) (Finset.mem_univ i₀)]
    simp
  have hcount : J * (badIdx p J N).card ≤ 2 * N ^ d := by
    have hdvd : J * (N / J) = N := Nat.mul_div_cancel' hJN
    rw [hcardbad, hprodN]
    calc J * ((∏ _i ∈ Finset.univ.erase i₀, N) *
          (((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card * (N / J)))
        = ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card *
            ((∏ _i ∈ Finset.univ.erase i₀, N) * (J * (N / J))) := by ring
      _ = ((Finset.range J).filter fun r ↦ r = 0 ∨ r = 1).card *
            (N * ∏ _i ∈ Finset.univ.erase i₀, N) := by rw [hdvd]; ring
      _ ≤ 2 * (N * ∏ _i ∈ Finset.univ.erase i₀, N) := Nat.mul_le_mul_right _ hcf
  have hmeas : volume (badSet p hp J N W) = ((badIdx p J N).card : ℝ≥0∞) * volume W := by
    rw [badSet]
    exact measure_levels p hp hW (by rw [badIdx]; exact Finset.filter_subset _ _)
  have hle1 : ((N : ℝ) ^ d) * (volume W).toReal ≤ 1 := by
    have h := (act p hp).card_mul_measure_le hW
    rw [card_box_const] at h
    have h2 := ENNReal.toReal_mono (volume_ne_top (Set.univ : Set UnitAddCircle)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, UnitAddCircle.measure_univ,
      ENNReal.toReal_one, Nat.cast_pow] at h2
    exact h2
  rw [hmeas, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hw0 : (0 : ℝ) ≤ (volume W).toReal := ENNReal.toReal_nonneg
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [le_div_iff₀ hJR]
  have hcountR : (J : ℝ) * ((badIdx p J N).card : ℝ) ≤ 2 * (N : ℝ) ^ d := by
    exact_mod_cast hcount
  nlinarith [mul_le_mul_of_nonneg_right hcountR hw0, hle1, hw0]

/-- **Measure claim for the good set.** -/
theorem measure_goodSet_ge {J N j₀ : ℕ} (hJ : 0 < J) (hJN : J ∣ N) (hJN' : J ≤ N)
    (hj₀ : j₀ ≤ J) (hp2 : ∃ i, p i = 2)
    {W : Set UnitAddCircle} (hW : (act p hp).Admissible (fun _ => N) W) {ε : ℝ}
    (htower : 1 - ε ≤ (volume ((act p hp).tower (fun _ => N) W)).toReal) :
    (1 - ε) * (1 - (J : ℝ) / N) ^ d * (1 - (j₀ : ℝ) / J) ≤
      (volume (goodSet p hp J N j₀ W)).toReal := by
  classical
  obtain ⟨i₀, hi₀⟩ := hp2
  have hN : 0 < N := lt_of_lt_of_le hJ hJN'
  have hgood : goodIdx p J N j₀
      = (Fintype.piFinset fun _ : Fin d ↦ Finset.Ico J N).filter fun e ↦ j₀ ≤ L p e % J := by
    ext e
    simp only [goodIdx, Finset.mem_filter, mem_box, Fintype.mem_piFinset, Finset.mem_Ico]
    exact ⟨fun h ↦ ⟨fun i ↦ ⟨h.2.1 i, h.1 i⟩, h.2.2⟩,
      fun h ↦ ⟨fun i ↦ (h.1 i).2, fun i ↦ (h.1 i).1, h.2⟩⟩
  have hcf : ((Finset.range J).filter fun r ↦ j₀ ≤ r).card = J - j₀ := by
    have hEq : (Finset.range J).filter (fun r ↦ j₀ ≤ r) = Finset.Ico j₀ J := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
    rw [hEq, Nat.card_Ico]
  have hcardgood : (goodIdx p J N j₀).card
      = (∏ _i ∈ Finset.univ.erase i₀, (N - J)) * ((J - j₀) * ((N - J) / J)) := by
    rw [hgood, card_filter_scale p hp hi₀ hJ hJN' dvd_rfl hJN (fun r ↦ j₀ ≤ r), hcf]
  have hprodNJ : (N - J) ^ d = (N - J) * ∏ _i ∈ Finset.univ.erase i₀, (N - J) := by
    rw [Finset.mul_prod_erase Finset.univ (fun _ : Fin d ↦ N - J) (Finset.mem_univ i₀)]
    simp
  have hcount : J * (goodIdx p J N j₀).card = (J - j₀) * (N - J) ^ d := by
    have hd : J * ((N - J) / J) = N - J := Nat.mul_div_cancel' (Nat.dvd_sub hJN dvd_rfl)
    rw [hcardgood, hprodNJ]
    calc J * ((∏ _i ∈ Finset.univ.erase i₀, (N - J)) * ((J - j₀) * ((N - J) / J)))
        = (J - j₀) * ((∏ _i ∈ Finset.univ.erase i₀, (N - J)) * (J * ((N - J) / J))) := by ring
      _ = (J - j₀) * ((N - J) * ∏ _i ∈ Finset.univ.erase i₀, (N - J)) := by rw [hd]; ring
  have hmeasg : volume (goodSet p hp J N j₀ W)
      = ((goodIdx p J N j₀).card : ℝ≥0∞) * volume W := by
    rw [goodSet]
    exact measure_levels p hp hW (by rw [goodIdx]; exact Finset.filter_subset _ _)
  have htowerR : 1 - ε ≤ (N : ℝ) ^ d * (volume W).toReal := by
    have h := (act p hp).measure_tower hW
    rw [card_box_const] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_pow] at htower
    exact htower
  rw [hmeasg, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hw0 : (0 : ℝ) ≤ (volume W).toReal := ENNReal.toReal_nonneg
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsub1 : (1 : ℝ) - (J : ℝ) / N = ((N - J : ℕ) : ℝ) / N := by
    rw [Nat.cast_sub hJN']
    field_simp
  have hsub2 : (1 : ℝ) - (j₀ : ℝ) / J = ((J - j₀ : ℕ) : ℝ) / J := by
    rw [Nat.cast_sub hj₀]
    field_simp
  have hcountR : (J : ℝ) * ((goodIdx p J N j₀).card : ℝ)
      = ((J - j₀ : ℕ) : ℝ) * ((N - J : ℕ) : ℝ) ^ d := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ)) hcount
  have hcardR : ((goodIdx p J N j₀).card : ℝ)
      = ((N - J : ℕ) : ℝ) ^ d * ((J - j₀ : ℕ) : ℝ) / J := by
    field_simp
    linarith [hcountR]
  rw [hsub1, hsub2, hcardR]
  have hbeta : (0 : ℝ) ≤ ((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J) := by
    positivity
  calc (1 - ε) * (((N - J : ℕ) : ℝ) / N) ^ d * (((J - j₀ : ℕ) : ℝ) / J)
      = (1 - ε) * (((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J)) := by
        rw [div_pow]
        ring
    _ ≤ ((N : ℝ) ^ d * (volume W).toReal) *
          (((N - J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d * (((J - j₀ : ℕ) : ℝ) / J)) :=
        mul_le_mul_of_nonneg_right htowerR hbeta
    _ = ((N - J : ℕ) : ℝ) ^ d * ((J - j₀ : ℕ) : ℝ) / J * (volume W).toReal := by
        field_simp

/-- The bad set is measurable. -/
lemma measurableSet_badSet {J N : ℕ} {W : Set UnitAddCircle} (hW : MeasurableSet W) :
    MeasurableSet (badSet p hp J N W) :=
  Finset.measurableSet_biUnion _ fun e _ ↦ (act p hp).measurable e hW

/-- The good set is measurable. -/
lemma measurableSet_goodSet {J N j₀ : ℕ} {W : Set UnitAddCircle} (hW : MeasurableSet W) :
    MeasurableSet (goodSet p hp J N j₀ W) :=
  Finset.measurableSet_biUnion _ fun e _ ↦ (act p hp).measurable e hW

