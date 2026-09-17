import Erdos210Ordinary.Basic

/-!
# Erdős Problem 210 — the cell count of an arrangement of lines

An *oriented line* is a pair `ℓ = (a, b)` of points, thought of as the line through `a` and `b`
oriented by the sign of `D a b ·`.  Given a family `L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)` of oriented
lines, the *sign vector* `sv L k p` of a point `p` records, for each of the first `k` lines,
whether `p` is on the positive side of that line.  The set of sign vectors realized by points off
the first `k` lines is `realized L k`; the main result is Motzkin's cell count

`(realized L k).ncard ≤ 1 + k * (k + 1) / 2`,

proved by adding one line at a time: a vector of `realized L (k+1)` is determined by its
restriction to the first `k` lines together with one bit, and the restriction can carry both bits
only if it is realized by a point *on* line `k` (`realizedOn L k`), of which there are at most
`k + 1` — the cells cut out of a single line by `k` others.
-/

namespace Erdos210

/-- the sign vector of `p` with respect to the first `k` lines of `L` (`false` beyond `k`) -/
noncomputable def sv {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : ℕ) (p : ℝ × ℝ) : Fin m → Bool :=
  fun i => if i.val < k then decide (0 < D (L i).1 (L i).2 p) else false

/-- `p` lies on none of the first `k` lines of `L`. -/
def OffLines {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : ℕ) (p : ℝ × ℝ) : Prop :=
  ∀ i : Fin m, i.val < k → D (L i).1 (L i).2 p ≠ 0

/-- the sign vectors realized by points off the first `k` lines -/
def realized {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : ℕ) : Set (Fin m → Bool) :=
  {v | ∃ p, OffLines L k p ∧ sv L k p = v}

/-- the vectors realized by points ON line `k` that are off the first `k` lines -/
def realizedOn {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : Fin m) : Set (Fin m → Bool) :=
  {v | ∃ p, OnLine (L k).1 (L k).2 p ∧ OffLines L k.val p ∧ sv L k.val p = v}

/-! ### Elementary helpers -/

private lemma sv_of_lt {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (K : ℕ) (p : ℝ × ℝ) {i : Fin m}
    (h : i.val < K) : sv L K p i = decide (0 < D (L i).1 (L i).2 p) := ite_eq_left h

private lemma sv_of_not_lt {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (K : ℕ) (p : ℝ × ℝ)
    {i : Fin m} (h : ¬ i.val < K) : sv L K p i = false := ite_eq_right h

/-- `D u v ·` is affine along the parametrisation `t ↦ a + t • (b - a)` of the line `a b`. -/
private lemma D_lineParam (u v a b : ℝ × ℝ) (t : ℝ) :
    D u v (a + t • (b - a)) = D u v a + t * (D u v b - D u v a) := by
  rw [D_affine]; ring

private lemma mul_pos_of_decide_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : decide (0 < x) = decide (0 < y)) : 0 < x * y := by
  rw [decide_eq_decide] at h
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · have hy' : ¬ (0 < y) := fun hc => absurd (h.mpr hc) (by linarith)
    exact mul_pos_of_neg_of_neg hx' (lt_of_le_of_ne (not_lt.1 hy') hy)
  · exact mul_pos hx' (h.mp hx')

private lemma decide_eq_of_mul_pos {x y : ℝ} (h : 0 < x * y) :
    decide (0 < x) = decide (0 < y) := by
  rw [decide_eq_decide]
  rcases mul_pos_iff.1 h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨fun _ => hy, fun _ => hx⟩
  · constructor <;> intro hc <;> linarith

private lemma nat_tri (k : ℕ) : k * (k + 1) / 2 + (k + 1) = (k + 1) * (k + 1 + 1) / 2 := by
  obtain ⟨q, hq⟩ := Nat.even_mul_succ_self k
  have h2 : (k + 1) * (k + 1 + 1) = (q + q) + 2 * (k + 1) := by
    rw [show (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) by ring, hq]
  rw [hq, h2]
  omega

/-! ### Finiteness -/

theorem realized_finite {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : ℕ) :
    (realized L k).Finite :=
  Set.toFinite _

/-! ### The cells cut out of one line by the previous ones -/

theorem ncard_realizedOn_le {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ))
    (hL : ∀ i, (L i).1 ≠ (L i).2) (k : Fin m) :
    (realizedOn L k).ncard ≤ k.val + 1 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin m → ℝ, ∀ i, c i = D (L i).1 (L i).2 (L k).1 := ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin m → ℝ, ∀ i,
      d i = D (L i).1 (L i).2 (L k).2 - D (L i).1 (L i).2 (L k).1 := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → Finset (Fin m), ∀ t, R t =
      Finset.univ.filter
        (fun i : Fin m => i.val < k.val ∧ d i ≠ 0 ∧ 0 < (c i + t * d i) * d i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Finset (Fin m) → (Fin m → Bool), ∀ S i, G S i =
      if i.val < k.val then
        (if d i = 0 then decide (0 < c i) else (decide (0 < d i) == decide (i ∈ S)))
      else false := ⟨_, fun _ _ => rfl⟩
  have hmem : ∀ (t : ℝ) (i : Fin m), i.val < k.val → d i ≠ 0 →
      ((i ∈ R t) ↔ 0 < (c i + t * d i) * d i) := by
    intro t i hi hdi
    rw [hR, Finset.mem_filter]
    constructor
    · rintro ⟨-, -, -, h⟩
      exact h
    · intro h
      exact ⟨Finset.mem_univ i, hi, hdi, h⟩
  -- every vector realized on line `k` is the value of `G` at some `R s`
  have hsub : realizedOn L k ⊆ G '' (Set.range R) := by
    rintro v ⟨p, hon, hoff, hsv⟩
    obtain ⟨s, rfl⟩ := exists_param_of_onLine (hL k) hon
    refine ⟨R s, ⟨s, rfl⟩, ?_⟩
    funext i
    by_cases hi : i.val < k.val
    · have hDp : D (L i).1 (L i).2 ((L k).1 + s • ((L k).2 - (L k).1)) = c i + s * d i := by
        rw [hc, hd, D_lineParam]
      have hne : c i + s * d i ≠ 0 := by
        rw [← hDp]; exact hoff i hi
      rw [hG, ite_eq_left hi, ← hsv, sv_of_lt _ _ _ hi, hDp]
      by_cases hdi : d i = 0
      · rw [ite_eq_left hdi, hdi, mul_zero, add_zero]
      · rw [ite_eq_right hdi]
        rcases lt_or_gt_of_ne hdi with hneg | hpos
        · have h1 : decide (0 < d i) = false := by simp [not_lt.2 (le_of_lt hneg)]
          have h2 : (i ∈ R s) ↔ ¬ (0 < c i + s * d i) := by
            rw [hmem s i hi hdi]
            constructor
            · intro h hc'
              nlinarith
            · intro h
              have : c i + s * d i < 0 := lt_of_le_of_ne (not_lt.1 h) hne
              nlinarith
          rw [h1, show decide (i ∈ R s) = decide (¬ (0 < c i + s * d i)) from
            decide_eq_decide.mpr h2, decide_not]
          simp
        · have h1 : decide (0 < d i) = true := by simp [hpos]
          have h2 : (i ∈ R s) ↔ (0 < c i + s * d i) := by
            rw [hmem s i hi hdi]
            constructor
            · intro h
              nlinarith
            · intro h
              exact mul_pos h hpos
          rw [h1, show decide (i ∈ R s) = decide (0 < c i + s * d i) from
            decide_eq_decide.mpr h2]
          simp
    · rw [hG, ite_eq_right hi, ← hsv, sv_of_not_lt _ _ _ hi]
  -- `R` is monotone, so its range is a chain and has at most `k + 1` members
  have hmono : ∀ t t' : ℝ, t ≤ t' → R t ⊆ R t' := by
    intro t t' htt i hi
    rw [hR, Finset.mem_filter] at hi ⊢
    obtain ⟨-, h1, h2, h3⟩ := hi
    refine ⟨Finset.mem_univ i, h1, h2, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.2 htt) (mul_self_nonneg (d i))]
  have hcardR : ∀ t : ℝ, (R t).card ≤ k.val := by
    intro t
    have hsub' : R t ⊆ Finset.univ.filter (fun i : Fin m => i.val < k.val) := by
      intro i hi
      rw [hR, Finset.mem_filter] at hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hi.2.1⟩
    refine le_trans (Finset.card_le_card hsub') ?_
    refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin m => i.val) ?_ ?_)
      (le_of_eq (Finset.card_range k.val))
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hi
      exact Finset.mem_coe.2 (Finset.mem_range.2 hi)
    · intro i _ j _ h
      exact Fin.ext h
  have hinjcard : Set.InjOn Finset.card (Set.range R) := by
    rintro S ⟨t, rfl⟩ S' ⟨t', rfl⟩ h
    rcases le_total t t' with hle | hle
    · exact Finset.eq_of_subset_of_card_le (hmono t t' hle) (le_of_eq h.symm)
    · exact (Finset.eq_of_subset_of_card_le (hmono t' t hle) (le_of_eq h)).symm
  have hcount : (Set.range R).ncard ≤ k.val + 1 := by
    refine le_trans (Set.ncard_le_ncard_of_injOn Finset.card ?_ hinjcard
      (Finset.range (k.val + 1)).finite_toSet) ?_
    · rintro S ⟨t, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (hcardR t)))
    · rw [Set.ncard_coe_finset, Finset.card_range]
  calc (realizedOn L k).ncard ≤ (G '' (Set.range R)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range R).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ k.val + 1 := hcount

/-! ### Adding one line -/

/-- If both completions of `u` by a sign at line `k` are realized, then `u` is realized by a point
on line `k`: the segment joining two witnesses crosses line `k` and stays strictly on the same side
of each earlier line. -/
private lemma realizedOn_of_pair {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ)) (k : Fin m)
    {u : Fin m → Bool} (hu : u ∈ realized L (k.val + 1)) (huk : u k = false)
    (hu' : Function.update u k true ∈ realized L (k.val + 1)) :
    u ∈ realizedOn L k := by
  obtain ⟨p, hp, hpv⟩ := hu
  obtain ⟨q, hq, hqv⟩ := hu'
  have hkk : (k : Fin m).val < k.val + 1 := Nat.lt_succ_self _
  have hDp : D (L k).1 (L k).2 p < 0 := by
    have h1 : sv L (k.val + 1) p k = false := by rw [hpv]; exact huk
    rw [sv_of_lt _ _ _ hkk] at h1
    have h2 : ¬ (0 < D (L k).1 (L k).2 p) := by simpa using h1
    exact lt_of_le_of_ne (not_lt.1 h2) (hp k hkk)
  have hDq : 0 < D (L k).1 (L k).2 q := by
    have h1 : sv L (k.val + 1) q k = true := by
      rw [hqv]; exact Function.update_self ..
    rw [sv_of_lt _ _ _ hkk] at h1
    simpa using h1
  obtain ⟨t, ht0, ht1, hon⟩ :=
    exists_cross_of_oppSide (a := (L k).1) (b := (L k).2) (mul_neg_of_neg_of_pos hDp hDq)
  have hmain : ∀ i : Fin m, i.val < k.val →
      0 < D (L i).1 (L i).2 p * D (L i).1 (L i).2 (p + t • (q - p)) := by
    intro i hi
    have hi' : i.val < k.val + 1 := Nat.lt_succ_of_lt hi
    have hik : i ≠ k := by
      intro h
      rw [h] at hi
      exact lt_irrefl _ hi
    have hup : sv L (k.val + 1) p i = sv L (k.val + 1) q i := by
      rw [hpv, hqv, Function.update_of_ne hik]
    rw [sv_of_lt _ _ _ hi', sv_of_lt _ _ _ hi'] at hup
    have hsame : SameSide (L i).1 (L i).2 p q :=
      mul_pos_of_decide_eq (hp i hi') (hq i hi') hup
    have hself : SameSide (L i).1 (L i).2 p p := mul_self_pos.2 (hp i hi')
    exact sameSide_segment hself hsame (le_of_lt ht0) (le_of_lt ht1)
  refine ⟨p + t • (q - p), hon, fun i hi => ?_, ?_⟩
  · exact right_ne_zero_of_mul (ne_of_gt (hmain i hi))
  · funext i
    by_cases hi : i.val < k.val
    · rw [sv_of_lt _ _ _ hi, ← decide_eq_of_mul_pos (hmain i hi), ← hpv,
        sv_of_lt _ _ _ (Nat.lt_succ_of_lt hi)]
    · rw [sv_of_not_lt _ _ _ hi]
      by_cases hi2 : i.val < k.val + 1
      · have hik : i = k := Fin.ext (by omega)
        rw [hik]
        exact huk.symm
      · rw [← hpv, sv_of_not_lt _ _ _ hi2]

theorem ncard_realized_succ {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ))
    (hL : ∀ i, (L i).1 ≠ (L i).2) (k : Fin m) :
    (realized L (k.val + 1)).ncard ≤ (realized L k.val).ncard + (k.val + 1) := by
  classical
  obtain ⟨E, hE⟩ : ∃ E : Set (Fin m → Bool),
      E = {v | v ∈ realized L (k.val + 1) ∧ v k = false} := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Set (Fin m → Bool),
      F = {v | v ∈ realized L (k.val + 1) ∧ v k = true} := ⟨_, rfl⟩
  have hres : ∀ x : Fin m → Bool, x k = true →
      Function.update (Function.update x k false) k true = x := by
    intro x hx
    funext i
    by_cases hi : i = k
    · rw [hi, Function.update_self, hx]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  -- split `realized L (k+1)` according to the sign at line `k`
  have hEF : realized L (k.val + 1) = E ∪ F := by
    rw [hE, hF]
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hv
      cases h : v k
      · exact Or.inl ⟨hv, rfl⟩
      · exact Or.inr ⟨hv, rfl⟩
    · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
  have hdisj : Disjoint E F := by
    rw [Set.disjoint_left]
    intro v hv hv'
    rw [hE, Set.mem_ofPred_eq] at hv
    rw [hF, Set.mem_ofPred_eq] at hv'
    have h1 : (false : Bool) = true := by rw [← hv.2]; exact hv'.2
    exact Bool.false_ne_true h1
  have hcard1 : (realized L (k.val + 1)).ncard = E.ncard + F.ncard := by
    rw [hEF, Set.ncard_union_eq hdisj]
  -- the restriction map is injective on `F`
  have hinj : Set.InjOn (fun v : Fin m → Bool => Function.update v k false) F := by
    intro v hv w hw hvw
    rw [hF, Set.mem_ofPred_eq] at hv hw
    have hvw' : Function.update v k false = Function.update w k false := hvw
    calc v = Function.update (Function.update v k false) k true := (hres v hv.2).symm
      _ = Function.update (Function.update w k false) k true := by rw [hvw']
      _ = w := hres w hw.2
  have hFcard : ((fun v : Fin m → Bool => Function.update v k false) '' F).ncard = F.ncard :=
    hinj.ncard_image
  -- both pieces land in `realized L k`
  have hsub1 : E ⊆ realized L k.val := by
    intro v hv
    rw [hE, Set.mem_ofPred_eq] at hv
    obtain ⟨⟨p, hoff, hsv⟩, hvk⟩ := hv
    refine ⟨p, fun i hi => hoff i (Nat.lt_succ_of_lt hi), ?_⟩
    funext i
    by_cases hi : i.val < k.val
    · rw [sv_of_lt _ _ _ hi, ← hsv, sv_of_lt _ _ _ (Nat.lt_succ_of_lt hi)]
    · rw [sv_of_not_lt _ _ _ hi]
      by_cases hi2 : i.val < k.val + 1
      · have hik : i = k := Fin.ext (by omega)
        rw [hik]
        exact hvk.symm
      · rw [← hsv, sv_of_not_lt _ _ _ hi2]
  have hsub2 : (fun v : Fin m → Bool => Function.update v k false) '' F ⊆ realized L k.val := by
    rintro u ⟨v, hv, huv⟩
    have huv' : Function.update v k false = u := huv
    subst huv'
    rw [hF, Set.mem_ofPred_eq] at hv
    obtain ⟨⟨p, hoff, hsv⟩, hvk⟩ := hv
    refine ⟨p, fun i hi => hoff i (Nat.lt_succ_of_lt hi), ?_⟩
    funext i
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      exact sv_of_not_lt L k.val p (lt_irrefl k.val)
    · rw [Function.update_of_ne hi]
      by_cases hi2 : i.val < k.val
      · rw [sv_of_lt _ _ _ hi2, ← hsv, sv_of_lt _ _ _ (Nat.lt_succ_of_lt hi2)]
      · have hi3 : ¬ i.val < k.val + 1 := by
          intro hc
          exact hi (Fin.ext (by omega))
        rw [sv_of_not_lt _ _ _ hi2, ← hsv, sv_of_not_lt _ _ _ hi3]
  -- the overlap is realized on line `k`
  have hsub3 : E ∩ (fun v : Fin m → Bool => Function.update v k false) '' F ⊆ realizedOn L k := by
    rintro u ⟨huE, v, hv, huv⟩
    rw [hE, Set.mem_ofPred_eq] at huE
    rw [hF, Set.mem_ofPred_eq] at hv
    have huv' : Function.update v k false = u := huv
    refine realizedOn_of_pair L k huE.1 huE.2 ?_
    rw [← huv', hres v hv.2]
    exact hv.1
  have key : E.ncard + F.ncard ≤ (realized L k.val).ncard + (realizedOn L k).ncard := by
    rw [← hFcard, ← Set.ncard_union_add_ncard_inter E
      ((fun v : Fin m → Bool => Function.update v k false) '' F)]
    exact Nat.add_le_add (Set.ncard_le_ncard (Set.union_subset hsub1 hsub2) (Set.toFinite _))
      (Set.ncard_le_ncard hsub3 (Set.toFinite _))
  calc (realized L (k.val + 1)).ncard = E.ncard + F.ncard := hcard1
    _ ≤ (realized L k.val).ncard + (realizedOn L k).ncard := key
    _ ≤ (realized L k.val).ncard + (k.val + 1) :=
        Nat.add_le_add_left (ncard_realizedOn_le L hL k) _

/-! ### Motzkin's bound -/

theorem ncard_realized_le {m : ℕ} (L : Fin m → (ℝ × ℝ) × (ℝ × ℝ))
    (hL : ∀ i, (L i).1 ≠ (L i).2) (k : ℕ) (hk : k ≤ m) :
    (realized L k).ncard ≤ 1 + k * (k + 1) / 2 := by
  induction k with
  | zero =>
      have hsub : realized L 0 ⊆ {fun _ => false} := by
        rintro v ⟨p, -, hsv⟩
        have hv : v = fun _ => false := by
          rw [← hsv]
          funext i
          exact sv_of_not_lt _ _ _ (Nat.not_lt_zero _)
        exact hv
      calc (realized L 0).ncard ≤ ({fun _ => false} : Set (Fin m → Bool)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
        _ ≤ 1 + 0 * (0 + 1) / 2 := by norm_num
  | succ n ih =>
      have hn : n ≤ m := Nat.le_of_succ_le hk
      have hnm : n < m := hk
      have key := ncard_realized_succ L hL ⟨n, hnm⟩
      calc (realized L (n + 1)).ncard ≤ (realized L n).ncard + (n + 1) := key
        _ ≤ (1 + n * (n + 1) / 2) + (n + 1) := Nat.add_le_add_right (ih hn) _
        _ = 1 + (n + 1) * (n + 1 + 1) / 2 := by rw [add_assoc, nat_tri n]

end Erdos210
