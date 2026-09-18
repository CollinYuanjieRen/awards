import Jsp990.Defs

/-!
# JSP-000990 / Erdős #1185 — density of the counterexample set

Abstract counting module.  For a modulus `L = 8 * bm * bm` with `bm = 2 ^ e` (`e ≥ 8`) and an odd
`T`, the set of `n` whose "phase" `(n * n * T) % L` lies in `[0, L/16)` is periodic with period `L`
and contains at least `L / 32` elements of every period; consequently it has at least `N / 64`
elements in `[1, N]` once `N ≥ 2 * L`.
-/

open Finset

namespace Erdos1185

/-- `n` is *good* for `(L, T)` when its phase `(n * n * T) % L` lies in the window `[0, L/16)`. -/
def good (L T n : ℕ) : Prop := (n * n * T) % L < L / 16

instance decidableGood (L T n : ℕ) : Decidable (good L T n) :=
  inferInstanceAs (Decidable ((n * n * T) % L < L / 16))

/-- The set of good numbers in `[1, N]`. -/
def A (L T N : ℕ) : Finset ℕ := (Icc 1 N).filter (good L T)

/-! ### Arithmetic helpers -/

private lemma mod_mul_add_of_lt {D P s a : ℕ} (hs : s < D) (hP : 0 < P) :
    (D * a + s) % (D * P) = D * (a % P) + s := by
  obtain ⟨d, m, hm, rfl⟩ : ∃ d m, m < P ∧ a = P * d + m :=
    ⟨a / P, a % P, Nat.mod_lt _ hP, (Nat.div_add_mod a P).symm⟩
  have hmod : (P * d + m) % P = m := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hm
  rw [hmod]
  have key : D * (P * d + m) + s = (D * m + s) + D * P * d := by ring
  rw [key, Nat.add_mul_mod_self_left]
  refine Nat.mod_eq_of_lt ?_
  calc D * m + s < D * m + D := by omega
    _ = D * (m + 1) := by ring
    _ ≤ D * P := Nat.mul_le_mul le_rfl hm

private lemma mul_add_lt_mul_iff {D s r c : ℕ} (hs : s < D) : D * r + s < D * c ↔ r < c := by
  constructor
  · intro h
    by_contra hrc
    have hrc' : c ≤ r := Nat.le_of_not_lt hrc
    have : D * c ≤ D * r := Nat.mul_le_mul le_rfl hrc'
    omega
  · intro h
    calc D * r + s < D * r + D := by omega
      _ = D * (r + 1) := by ring
      _ ≤ D * c := Nat.mul_le_mul le_rfl h

/-! ### Counting an arithmetic progression of residues -/

/-- If `a` is invertible mod `P`, then exactly `c` of the residues `(q + a * k) % P`, `k < P`,
are smaller than `c`. -/
private lemma card_filter_mod_lt {P c q a : ℕ} (hP : 0 < P) (hc : c ≤ P)
    (hcop : Nat.Coprime a P) :
    #((range P).filter (fun k => (q + a * k) % P < c)) = c := by
  have hinj : Set.InjOn (fun k => (q + a * k) % P) (range P) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have h1 : q + a * x ≡ q + a * y [MOD P] := hxy
    have h2 : a * x ≡ a * y [MOD P] := Nat.ModEq.add_left_cancel' q h1
    have h3 : x ≡ y [MOD P] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime, Nat.gcd_comm] using hcop) h2
    calc x = x % P := (Nat.mod_eq_of_lt hx).symm
      _ = y % P := h3
      _ = y := Nat.mod_eq_of_lt hy
  have himg : (range P).image (fun k => (q + a * k) % P) = range P := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact mem_range.mpr (Nat.mod_lt _ hP)
    · rw [Finset.card_image_of_injOn hinj]
  have hfl : (range P).filter (fun r => r < c) = range c := by
    ext x; simp only [mem_filter, mem_range]; omega
  calc #((range P).filter (fun k => (q + a * k) % P < c))
      = #(((range P).filter (fun k => (q + a * k) % P < c)).image
          (fun k => (q + a * k) % P)) := by
        rw [Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    _ = #(((range P).image (fun k => (q + a * k) % P)).filter (fun r => r < c)) := by
        rw [Finset.filter_image]
    _ = #((range P).filter (fun r => r < c)) := by rw [himg]
    _ = c := by rw [hfl, card_range]

private lemma card_filter_mod_lt_two {P c q a : ℕ} (hP : 0 < P) (hc : c ≤ P)
    (hcop : Nat.Coprime a P) :
    2 * c ≤ #((range (2 * P)).filter (fun k => (q + a * k) % P < c)) := by
  have hshift : ∀ k : ℕ, (q + a * (k + P)) % P = (q + a * k) % P := by
    intro k
    have h : q + a * (k + P) = (q + a * k) + a * P := by ring
    rw [h, Nat.add_mul_mod_self_right]
  have hsub : ((range P).filter (fun k => (q + a * k) % P < c)) ∪
      (((range P).filter (fun k => (q + a * k) % P < c)).image (fun x => x + P)) ⊆
      (range (2 * P)).filter (fun k => (q + a * k) % P < c) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_filter, mem_range] at h ⊢
      exact ⟨by omega, h.2⟩
    · simp only [Finset.mem_image, Finset.mem_filter, mem_range] at h
      obtain ⟨y, ⟨hy1, hy2⟩, rfl⟩ := h
      simp only [Finset.mem_filter, mem_range]
      exact ⟨by omega, by rw [hshift y]; exact hy2⟩
  have hdisj : Disjoint ((range P).filter (fun k => (q + a * k) % P < c))
      (((range P).filter (fun k => (q + a * k) % P < c)).image (fun x => x + P)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, mem_range] at hx
    simp only [Finset.mem_image, Finset.mem_filter, mem_range] at hx'
    obtain ⟨y, ⟨hy1, _⟩, hxy⟩ := hx'
    omega
  have hc1 : #((range P).filter (fun k => (q + a * k) % P < c)) = c :=
    card_filter_mod_lt hP hc hcop
  have hc2 : #(((range P).filter (fun k => (q + a * k) % P < c)).image (fun x => x + P)) = c := by
    rw [Finset.card_image_of_injective _ (add_left_injective P), hc1]
  calc 2 * c = c + c := by ring
    _ = #(((range P).filter (fun k => (q + a * k) % P < c)) ∪
          (((range P).filter (fun k => (q + a * k) % P < c)).image (fun x => x + P))) := by
        rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]
    _ ≤ _ := Finset.card_le_card hsub

/-! ### Periodicity -/

lemma good_add_mul (L T n q : ℕ) : good L T (n + L * q) ↔ good L T n := by
  have h : (n + L * q) * (n + L * q) * T = n * n * T + L * (2 * n * q * T + L * (q * q * T)) := by
    ring
  simp only [good, h, Nat.add_mul_mod_self_left]

/-- The good set is periodic with period `L`. -/
theorem good_periodic (L T n : ℕ) : good L T (n + L) ↔ good L T n := by
  simpa using good_add_mul L T n 1

/-! ### The count in one period -/

/-- For a fixed odd `u < bm` and any `e'`, at least `bm / 16` of the `k < bm` give a good
`n = bm * (8 * k + e') + u`. -/
lemma card_good_k (bm T e : ℕ) {u e' : ℕ} (he : 8 ≤ e) (hbm : bm = 2 ^ e) (hT : T % 2 = 1)
    (hu : u % 2 = 1) (hulm : u < bm) :
    bm / 16 ≤ #((range bm).filter (fun k => good (8 * bm * bm) T (bm * (8 * k + e') + u))) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 8 := ⟨e - 8, by omega⟩
  obtain ⟨r, hrpos, hpow, hbmr⟩ : ∃ r, 0 < r ∧ 128 * r = 2 ^ (f + 7) ∧ bm = 256 * r :=
    ⟨2 ^ f, pow_pos (by norm_num) f, by ring, by rw [hbm]; ring⟩
  subst hbmr
  have hgoal : 256 * r / 16 = 2 * (8 * r) := by omega
  rw [hgoal]
  -- coprimality of the multiplier
  have hcop : Nat.Coprime (u * T) (128 * r) := by
    rw [hpow]
    refine Nat.Coprime.pow_right _ ?_
    have hnd : ¬ (2 ∣ u * T) := by
      rw [Nat.Prime.dvd_mul Nat.prime_two]
      rintro (h | h) <;> omega
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm
  set C : ℕ := ((256 * r) * (256 * r) * e' * e' + 2 * (256 * r) * e' * u + u * u) * T with hCdef
  set D : ℕ := 4096 * r with hDdef
  have hD : 0 < D := by rw [hDdef]; omega
  have hs : C % D < D := Nat.mod_lt _ hD
  have hCq : D * (C / D) + C % D = C := Nat.div_add_mod C D
  have key : ∀ k : ℕ, good (8 * (256 * r) * (256 * r)) T ((256 * r) * (8 * k + e') + u)
      ↔ (C / D + u * T * k) % (128 * r) < 8 * r := by
    intro k
    have hsplit : D * (C / D + u * T * k) + C % D = C + D * (u * T * k) := by
      rw [Nat.mul_add]; omega
    have hid : ((256 * r) * (8 * k + e') + u) * ((256 * r) * (8 * k + e') + u) * T
        = (D * (C / D + u * T * k) + C % D)
          + (8 * (256 * r) * (256 * r)) * (8 * k * k * T + 2 * k * e' * T) := by
      rw [hsplit, hCdef, hDdef]; ring
    have hLDP : 8 * (256 * r) * (256 * r) = D * (128 * r) := by rw [hDdef]; ring
    have hL16 : D * (128 * r) = 16 * (D * (8 * r)) := by rw [hDdef]; ring
    simp only [good, hid]
    rw [Nat.add_mul_mod_self_left, hLDP, mod_mul_add_of_lt hs (by omega), hL16,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 16)]
    exact mul_add_lt_mul_iff hs
  simp only [key]
  have hmain := card_filter_mod_lt_two (P := 128 * r) (c := 8 * r) (q := C / D) (a := u * T)
    (by omega) (by omega) hcop
  have h2P : 2 * (128 * r) = 256 * r := by ring
  rw [h2P] at hmain
  exact hmain

/-- **Period count**: in every period `[0, L)` there are at least `L / 32` good numbers. -/
theorem card_good_period (bm T e : ℕ) (he : 8 ≤ e) (hbm : bm = 2 ^ e) (hT : T % 2 = 1) :
    (8 * bm * bm) / 32 ≤ #((range (8 * bm * bm)).filter (good (8 * bm * bm) T)) := by
  have hbmpos : 0 < bm := by rw [hbm]; exact pow_pos (by norm_num) e
  have h1 : #(((range (bm / 2) ×ˢ range 8) ×ˢ range bm).filter
        (fun p => good (8 * bm * bm) T (bm * (8 * p.2 + p.1.2) + (2 * p.1.1 + 1))))
      ≤ #((range (8 * bm * bm)).filter (good (8 * bm * bm) T)) := by
    refine Finset.card_le_card_of_injOn
      (fun p => bm * (8 * p.2 + p.1.2) + (2 * p.1.1 + 1)) ?_ ?_
    · rintro ⟨⟨j, e'⟩, k⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, mem_range] at hp
      obtain ⟨⟨⟨hj, he'⟩, hk⟩, hg⟩ := hp
      simp only [Finset.mem_coe, Finset.mem_filter, mem_range]
      refine ⟨?_, hg⟩
      calc bm * (8 * k + e') + (2 * j + 1) < bm * (8 * k + e') + bm := by omega
        _ = bm * (8 * k + e' + 1) := by ring
        _ ≤ bm * (8 * bm) := Nat.mul_le_mul le_rfl (by omega)
        _ = 8 * bm * bm := by ring
    · rintro ⟨⟨j, e'⟩, k⟩ hp ⟨⟨j', e''⟩, k'⟩ hp' hEq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, mem_range] at hp hp'
      obtain ⟨⟨⟨hj, he'⟩, hk⟩, -⟩ := hp
      obtain ⟨⟨⟨hj', he''⟩, hk'⟩, -⟩ := hp'
      simp only at hEq
      have hmod := congrArg (fun x => x % bm) hEq
      simp only [Nat.mul_add_mod] at hmod
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      have hjj : j = j' := by omega
      subst hjj
      have hcancel : bm * (8 * k + e') = bm * (8 * k' + e'') := Nat.add_right_cancel hEq
      have hke : 8 * k + e' = 8 * k' + e'' := Nat.eq_of_mul_eq_mul_left hbmpos hcancel
      obtain ⟨rfl, rfl⟩ : k = k' ∧ e' = e'' := by omega
      rfl
  have h2 : (bm / 2) * 8 * (bm / 16) ≤ #(((range (bm / 2) ×ˢ range 8) ×ˢ range bm).filter
        (fun p => good (8 * bm * bm) T (bm * (8 * p.2 + p.1.2) + (2 * p.1.1 + 1)))) := by
    rw [Finset.card_filter, Finset.sum_product]
    have hb : ∀ p ∈ (range (bm / 2) ×ˢ range 8), bm / 16 ≤
        ∑ k ∈ range bm, (if good (8 * bm * bm) T (bm * (8 * k + p.2) + (2 * p.1 + 1))
          then 1 else 0) := by
      rintro ⟨j, e'⟩ hp
      simp only [Finset.mem_product, mem_range] at hp
      simp only
      rw [← Finset.card_filter]
      exact card_good_k bm T e he hbm hT (by omega) (by omega)
    have hsum := Finset.card_nsmul_le_sum (range (bm / 2) ×ˢ range 8) _ (bm / 16) hb
    simpa [Finset.card_product, smul_eq_mul] using hsum
  have h3 : (8 * bm * bm) / 32 ≤ (bm / 2) * 8 * (bm / 16) := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 8 := ⟨e - 8, by omega⟩
    obtain ⟨r, hrpos, hbmr⟩ : ∃ r, 0 < r ∧ bm = 256 * r :=
      ⟨2 ^ f, pow_pos (by norm_num) f, by rw [hbm]; ring⟩
    subst hbmr
    have e1 : 256 * r / 2 = 128 * r := by omega
    have e2 : 256 * r / 16 = 16 * r := by omega
    have e3 : 8 * (256 * r) * (256 * r) = 32 * (16384 * (r * r)) := by ring
    have e4 : 128 * r * 8 * (16 * r) = 16384 * (r * r) := by ring
    rw [e1, e2, e3, e4, Nat.mul_div_cancel_left _ (by norm_num : 0 < 32)]
  exact h3.trans (h2.trans h1)

/-! ### From one period to `[1, N]` -/

private lemma card_good_Ico (L T q : ℕ) :
    #((Ico (q * L) (q * L + L)).filter (good L T)) = #((range L).filter (good L T)) := by
  rw [← Finset.card_image_of_injective ((range L).filter (good L T)) (add_left_injective (q * L))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico, mem_range]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hg⟩
    refine ⟨x - q * L, ⟨by omega, ?_⟩, by omega⟩
    have hxx : x = (x - q * L) + L * q := by rw [Nat.mul_comm L q]; omega
    rw [hxx] at hg
    exact (good_add_mul L T (x - q * L) q).mp hg
  · rintro ⟨y, ⟨hy, hg⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show y + q * L = y + L * q by ring]
    exact (good_add_mul L T y q).mpr hg

private lemma card_good_range_mul (L T q : ℕ) :
    #((range (q * L)).filter (good L T)) = q * #((range L).filter (good L T)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hr : range ((q + 1) * L) = range (q * L) ∪ Ico (q * L) (q * L + L) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _)]
      congr 1
      ring
    have hdisj : Disjoint ((range (q * L)).filter (good L T))
        ((Ico (q * L) (q * L + L)).filter (good L T)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, mem_range, Finset.mem_Ico] at hx hx'
      omega
    rw [hr, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih, card_good_Ico]
    ring

/-- **Interval count**: for `N ≥ 2 L` the good set has at least `N / 64` elements in `[1, N]`. -/
theorem card_A_ge (bm T e : ℕ) (he : 8 ≤ e) (hbm : bm = 2 ^ e) (hT : T % 2 = 1)
    (N : ℕ) (hN : 2 * (8 * bm * bm) ≤ N) :
    ((N : ℝ) / 64) ≤ (#(A (8 * bm * bm) T N) : ℝ) := by
  have hG0 := card_good_period bm T e he hbm hT
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 8 := ⟨e - 8, by omega⟩
  obtain ⟨r, hrpos, hbmr⟩ : ∃ r, 0 < r ∧ bm = 256 * r :=
    ⟨2 ^ f, pow_pos (by norm_num) f, by rw [hbm]; ring⟩
  subst hbmr
  set L : ℕ := 8 * (256 * r) * (256 * r) with hLdef
  set G : ℕ := #((range L).filter (good L T)) with hGdef
  have hLval : L = 32 * (16384 * (r * r)) := by rw [hLdef]; ring
  have hL32 : L / 32 = 16384 * (r * r) := by
    rw [hLval, Nat.mul_div_cancel_left _ (by norm_num : 0 < 32)]
  have hG : 16384 * (r * r) ≤ G := by rw [← hL32]; exact hG0
  have hL0 : 0 < L := by rw [hLval]; positivity
  have hN2 : 2 * L ≤ N := hN
  have hNbig : 192 ≤ N := by
    have : 1 ≤ r * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hLval] at hN2
    omega
  set Q : ℕ := N / L with hQdef
  have hQ2 : 2 ≤ Q := (Nat.le_div_iff_mul_le hL0).mpr hN2
  have hQL : Q * L ≤ N := Nat.div_mul_le_self N L
  have hNlt : N < (Q + 1) * L := by
    have h1 : L * Q + N % L = N := Nat.div_add_mod N L
    have h2 : N % L < L := Nat.mod_lt _ hL0
    calc N = L * Q + N % L := h1.symm
      _ < L * Q + L := Nat.add_lt_add_left h2 _
      _ = (Q + 1) * L := by ring
  -- the good numbers in the first `Q` periods, minus `0`, sit inside `A`
  have hsub : ((range (Q * L)).filter (good L T)).erase 0 ⊆ A L T N := by
    intro n hn
    rw [Finset.mem_erase, Finset.mem_filter, mem_range] at hn
    rw [A, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hn.2.2⟩
  have hcard : Q * G - 1 ≤ #(A L T N) := by
    have hp : #((range (Q * L)).filter (good L T)) - 1
        ≤ #(((range (Q * L)).filter (good L T)).erase 0) := Finset.pred_card_le_card_erase
    rw [card_good_range_mul, ← hGdef] at hp
    exact hp.trans (Finset.card_le_card hsub)
  -- now the real arithmetic
  have hGpos : 1 ≤ G := by
    have : 1 ≤ r * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hQG1 : 1 ≤ Q * G := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hLG : (L : ℝ) ≤ 32 * (G : ℝ) := by
    have : (L : ℕ) ≤ 32 * G := by rw [hLval]; omega
    exact_mod_cast this
  have hQLr : (Q : ℝ) * L ≤ N := by exact_mod_cast hQL
  have hNltr : (N : ℝ) < ((Q : ℝ) + 1) * L := by exact_mod_cast hNlt
  have hQ2r : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hL0r : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  have hNbigr : (192 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbig
  have hA : (L : ℝ) ≤ (Q : ℝ) * L / 2 := by nlinarith
  have hB : (Q : ℝ) * L ≤ 32 * ((Q : ℝ) * G) := by nlinarith
  have hreal : (N : ℝ) / 64 ≤ (Q : ℝ) * (G : ℝ) - 1 := by linarith
  have hcast : ((Q * G - 1 : ℕ) : ℝ) = (Q : ℝ) * (G : ℝ) - 1 := by
    rw [Nat.cast_sub hQG1, Nat.cast_mul, Nat.cast_one]
  calc (N : ℝ) / 64 ≤ (Q : ℝ) * (G : ℝ) - 1 := hreal
    _ = ((Q * G - 1 : ℕ) : ℝ) := hcast.symm
    _ ≤ (#(A L T N) : ℝ) := by exact_mod_cast hcard

end Erdos1185
