import Proof.Ramsey

/-!
# Erdős problem #1029 — Erdős's 1947 counting lower bound

We prove the classical lower bound `R(k) > 2^{k/2}` by Erdős's counting argument, with no
probability theory: a red/blue colouring of `K_N` is a subset `F` of the `C(N,2)` edges (the
red ones), a `k`-set `S` is *bad* for `F` when all edges inside `S` are red or all are blue,
and for each `S` at most `2 · 2^{C(N,2) − C(k,2)}` of the `2^{C(N,2)}` colourings are bad.
If `C(N,k) · 2 · 2^{C(N,2) − C(k,2)} < 2^{C(N,2)}` some colouring has no bad `k`-set.

Not claimed here: the question of Erdős problem #1029 itself (whether `R(k)/(k·2^{k/2}) → ∞`),
which is open, and the asymptotic constants `(1+o(1))/(√2 e)` and Spencer's `√2/e`.
-/

namespace Erdos1029

open SimpleGraph

section Counting

variable {N : ℕ}

/-- The edges of the complete graph spanned by a set `S` of vertices. -/
def edgesOn (S : Finset (Fin N)) : Finset (Sym2 (Fin N)) :=
  S.offDiag.image (Function.uncurry Sym2.mk)

/-- Membership in `edgesOn S`: the edges inside `S` are the pairs of distinct vertices of `S`. -/
theorem mem_edgesOn {S : Finset (Fin N)} {x y : Fin N} :
    s(x, y) ∈ edgesOn S ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  classical
  simp only [edgesOn, Finset.mem_image, Finset.mem_offDiag, Function.uncurry_apply_pair,
    Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, he⟩
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, hab⟩
    · exact ⟨hb, ha, fun hc => hab hc.symm⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨x, y, ⟨hx, hy, hxy⟩, rfl⟩

/-- `edgesOn` is monotone. -/
theorem edgesOn_mono {S T : Finset (Fin N)} (h : S ⊆ T) : edgesOn S ⊆ edgesOn T := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgesOn] at he ⊢
    exact ⟨h he.1, h he.2.1, he.2.2⟩

/-- A set of `k` vertices spans `C(k, 2)` edges. -/
theorem card_edgesOn (S : Finset (Fin N)) : (edgesOn S).card = S.card.choose 2 := by
  classical
  exact Sym2.card_image_offDiag S

/-- The colouring attached to a set `F` of red edges: `F` is the edge set of the red graph. -/
def redGraph (F : Finset (Sym2 (Fin N))) : SimpleGraph (Fin N) :=
  SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin N)))

/-- A red `k`-clique on `S` means that every edge inside `S` is red. -/
theorem edgesOn_subset_of_isNClique {F : Finset (Sym2 (Fin N))} {S : Finset (Fin N)} {k : ℕ}
    (h : (redGraph F).IsNClique k S) : edgesOn S ⊆ F := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgesOn] at he
    obtain ⟨hx, hy, hxy⟩ := he
    have hadj := h.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    rw [redGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    exact_mod_cast hadj.1

/-- A blue `k`-clique on `S` means that no edge inside `S` is red. -/
theorem disjoint_of_isNClique_compl {F : Finset (Sym2 (Fin N))} {S : Finset (Fin N)} {k : ℕ}
    (h : (redGraph F)ᶜ.IsNClique k S) : Disjoint (edgesOn S) F := by
  classical
  rw [Finset.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    intro he heF
    rw [mem_edgesOn] at he
    obtain ⟨hx, hy, hxy⟩ := he
    have hadj := h.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    rw [SimpleGraph.compl_adj] at hadj
    refine hadj.2 ?_
    rw [redGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨by exact_mod_cast heF, hxy⟩

/-- Erdős's counting bound: if `C(N, k) · 2 · 2^{C(N,2) − C(k,2)} < 2^{C(N,2)}` then `N < R(k)`. -/
theorem lt_R_of_count (k N : ℕ) (hkN : k ≤ N)
    (h : N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2) < 2 ^ (N.choose 2)) : N < R k := by
  classical
  have hcc : k.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 hkN
  have hsharp : N.choose k * 2 < 2 ^ (k.choose 2) := by
    have hsplit : 2 ^ (N.choose 2) = 2 ^ (k.choose 2) * 2 ^ (N.choose 2 - k.choose 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at h
    exact Nat.lt_of_mul_lt_mul_right h
  set E : Finset (Sym2 (Fin N)) := edgesOn (Finset.univ : Finset (Fin N)) with hEdef
  have hEcard : E.card = N.choose 2 := by
    rw [hEdef, card_edgesOn, Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ S : Finset (Fin N), edgesOn S ⊆ E := fun S =>
    edgesOn_mono (Finset.subset_univ S)
  set bad : Finset (Fin N) → Finset (Finset (Sym2 (Fin N))) := fun S =>
    Finset.Icc (edgesOn S) E ∪ (E \ edgesOn S).powerset with hbaddef
  have hbadcard : ∀ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
      (bad S).card ≤ 2 * 2 ^ (N.choose 2 - k.choose 2) := by
    intro S hS
    rw [Finset.mem_powersetCard_univ] at hS
    have h1 : (Finset.Icc (edgesOn S) E).card = 2 ^ (N.choose 2 - k.choose 2) := by
      rw [Finset.card_Icc_finset (hsub S), hEcard, card_edgesOn, hS]
    have h2 : ((E \ edgesOn S).powerset).card = 2 ^ (N.choose 2 - k.choose 2) := by
      rw [Finset.card_powerset, Finset.card_sdiff_of_subset (hsub S), hEcard, card_edgesOn, hS]
    calc (bad S).card
        ≤ (Finset.Icc (edgesOn S) E).card + ((E \ edgesOn S).powerset).card :=
          Finset.card_union_le _ _
      _ = 2 * 2 ^ (N.choose 2 - k.choose 2) := by rw [h1, h2]; ring
  have hlt : ((Finset.powersetCard k (Finset.univ : Finset (Fin N))).biUnion bad).card
      < E.powerset.card := by
    rw [Finset.card_powerset, hEcard]
    calc ((Finset.powersetCard k (Finset.univ : Finset (Fin N))).biUnion bad).card
        ≤ ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)), (bad S).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
            2 * 2 ^ (N.choose 2 - k.choose 2) := Finset.sum_le_sum hbadcard
      _ = N.choose k * (2 * 2 ^ (N.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ = N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2) := by ring
      _ < 2 ^ (k.choose 2) * 2 ^ (N.choose 2 - k.choose 2) :=
          (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num : (0:ℕ) < 2))).mpr hsharp
      _ = 2 ^ (N.choose 2) := by
          rw [← pow_add]
          congr 1
          omega
  obtain ⟨F, hFmem, hFbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_powerset] at hFmem
  have hFnot : ∀ S : Finset (Fin N), S.card = k → F ∉ bad S := by
    intro S hS hmem
    exact hFbad (Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard_univ.mpr hS, hmem⟩)
  have hgood : IsGood (redGraph F) k k := by
    constructor
    · intro S hS
      refine hFnot S hS.2 ?_
      rw [hbaddef]
      exact Finset.mem_union_left _
        (Finset.mem_Icc.mpr ⟨edgesOn_subset_of_isNClique hS, hFmem⟩)
    · intro S hS
      refine hFnot S hS.2 ?_
      rw [hbaddef]
      exact Finset.mem_union_right _ (Finset.mem_powerset.mpr
        (Finset.subset_sdiff.mpr ⟨hFmem, (disjoint_of_isNClique_compl hS).symm⟩))
  exact lt_ramsey_of_isGood hgood

end Counting

/-- Sharp form of the counting bound: `C(N,k) · 2 < 2^{C(k,2)}` and `k ≤ N` give `N < R(k)`. -/
theorem lt_R_of_choose_lt (k N : ℕ) (hkN : k ≤ N) (h : N.choose k * 2 < 2 ^ (k.choose 2)) :
    N < R k := by
  refine lt_R_of_count k N hkN ?_
  have hcc : k.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 hkN
  calc N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2)
      < 2 ^ (k.choose 2) * 2 ^ (N.choose 2 - k.choose 2) :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num : (0:ℕ) < 2))).mpr h
    _ = 2 ^ (N.choose 2) := by
        rw [← pow_add]
        congr 1
        omega

/-- `R(k) ≥ k` for `k ≥ 1` (fewer than `k` vertices contain no `K_k`). -/
theorem le_R (k : ℕ) (hk : 1 ≤ k) : k ≤ R k := by
  have hcard : Fintype.card (Fin (k - 1)) < k := by
    rw [Fintype.card_fin]
    omega
  have hgood : IsGood (⊥ : SimpleGraph (Fin (k - 1))) k k :=
    ⟨SimpleGraph.cliqueFree_of_card_lt hcard, SimpleGraph.cliqueFree_of_card_lt hcard⟩
  have hlt := lt_ramsey_of_isGood hgood
  show k ≤ ramsey k k
  omega

section Sqrt

/-- `2 · C(k, 2) + k = k²`. -/
theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have hexp : (j + 1) * (j + 1) = j * j + 2 * j + 1 := by ring
    rw [hexp, Nat.choose_succ_succ, Nat.choose_one_right, show Nat.succ 1 = 2 from rfl]
    omega

/-- `2^{k+2} < (k!)²` for `k ≥ 3`. -/
theorem two_pow_lt_factorial_sq (k : ℕ) (hk : 3 ≤ k) : 2 ^ (k + 2) < (Nat.factorial k) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k _ ih =>
    have h1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := rfl
    have h2 : 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
    have h3 : ((k + 1) * Nat.factorial k) ^ 2 = (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := by ring
    have h4 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    calc 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := h2
      _ < 2 * (Nat.factorial k) ^ 2 := by omega
      _ ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := Nat.mul_le_mul_right _ h4
      _ = Nat.factorial (k + 1) ^ 2 := by rw [h1, h3]

/-- The counting hypothesis holds for every `N` with `N² ≤ 2^k`, when `k ≥ 3`. -/
theorem choose_mul_two_lt (k N : ℕ) (hk : 3 ≤ k) (hN : N ^ 2 ≤ 2 ^ k) :
    N.choose k * 2 < 2 ^ (k.choose 2) := by
  have hE : 2 * k.choose 2 + k = k * k := two_mul_choose_two k
  have hfac : 0 < (Nat.factorial k) ^ 2 := Nat.pow_pos (Nat.factorial_pos k)
  have h1 : Nat.factorial k * N.choose k ≤ N ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow N k
  have hA : (Nat.factorial k) ^ 2 * (N.choose k) ^ 2 ≤ 2 ^ (k * k) := by
    calc (Nat.factorial k) ^ 2 * (N.choose k) ^ 2
        = (Nat.factorial k * N.choose k) ^ 2 := by ring
      _ ≤ (N ^ k) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (N ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hN k
      _ = 2 ^ (k * k) := by rw [← pow_mul]
  have hB : (N.choose k) ^ 2 * 4 < 2 ^ (2 * k.choose 2) := by
    refine Nat.lt_of_mul_lt_mul_left (a := (Nat.factorial k) ^ 2) ?_
    calc (Nat.factorial k) ^ 2 * ((N.choose k) ^ 2 * 4)
        = ((Nat.factorial k) ^ 2 * (N.choose k) ^ 2) * 4 := by ring
      _ ≤ 2 ^ (k * k) * 4 := Nat.mul_le_mul_right _ hA
      _ = 2 ^ (k + 2) * 2 ^ (2 * k.choose 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
          congr 1
          omega
      _ < (Nat.factorial k) ^ 2 * 2 ^ (2 * k.choose 2) :=
          (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num : (0:ℕ) < 2))).mpr
            (two_pow_lt_factorial_sq k hk)
  refine (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp ?_
  calc (N.choose k * 2) ^ 2 = (N.choose k) ^ 2 * 4 := by ring
    _ < 2 ^ (2 * k.choose 2) := hB
    _ = (2 ^ (k.choose 2)) ^ 2 := by rw [← pow_mul, Nat.mul_comm]

/-- Erdős 1947: `R(k)² > 2^k` for `k ≥ 3`, i.e. `R(k) > 2^{k/2}`. -/
theorem two_pow_lt_R_sq (k : ℕ) (hk : 3 ≤ k) : 2 ^ k < R k ^ 2 := by
  have hN2 : (Nat.sqrt (2 ^ k)) ^ 2 ≤ 2 ^ k := Nat.sqrt_le' _
  have hlt : 2 ^ k < (Nat.sqrt (2 ^ k) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hNR : Nat.sqrt (2 ^ k) < R k := by
    by_cases hkN : k ≤ Nat.sqrt (2 ^ k)
    · refine lt_R_of_count k _ hkN ?_
      have hcc : k.choose 2 ≤ (Nat.sqrt (2 ^ k)).choose 2 := Nat.choose_le_choose 2 hkN
      calc (Nat.sqrt (2 ^ k)).choose k * 2
            * 2 ^ ((Nat.sqrt (2 ^ k)).choose 2 - k.choose 2)
          < 2 ^ (k.choose 2) * 2 ^ ((Nat.sqrt (2 ^ k)).choose 2 - k.choose 2) :=
            (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num : (0:ℕ) < 2))).mpr
              (choose_mul_two_lt k _ hk hN2)
        _ = 2 ^ ((Nat.sqrt (2 ^ k)).choose 2) := by
            rw [← pow_add]
            congr 1
            omega
    · have hkR := le_R k (by omega)
      omega
  calc 2 ^ k < (Nat.sqrt (2 ^ k) + 1) ^ 2 := hlt
    _ ≤ R k ^ 2 := Nat.pow_le_pow_left hNR 2

end Sqrt

section RealBound

/-- The quantitative counting bound: `⌊k·2^{(k−1)/2}/(2e)⌋ < R(k)` for `k ≥ 3`. -/
theorem floor_lt_R (k : ℕ) (hk : 3 ≤ k) :
    ⌊(k : ℝ) * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) / (2 * Real.exp 1)⌋₊ < R k := by
  have hk0 : (0:ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  set A : ℝ := (2 : ℝ) ^ (((k : ℝ) - 1) / 2) with hAdef
  have hA0 : 0 < A := by
    rw [hAdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  set x : ℝ := (k : ℝ) * A / (2 * Real.exp 1) with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    positivity
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  by_cases hkN : k ≤ N
  · refine lt_R_of_choose_lt k N hkN ?_
    have hfac : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hkk : (0:ℝ) < (k : ℝ) ^ k := pow_pos hk0 k
    have hNnn : (0:ℝ) ≤ (N : ℝ) ^ k := by positivity
    have step1 : ((N.choose k : ℕ) : ℝ) ≤ (N : ℝ) ^ k / (Nat.factorial k : ℝ) :=
      Nat.choose_le_pow_div k N
    have step2 : ((k : ℝ)) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (k : ℝ) :=
      Real.pow_div_factorial_le_exp (k : ℝ) (le_of_lt hk0) k
    have hkfk : ((k : ℝ)) ^ k ≤ Real.exp (k : ℝ) * (Nat.factorial k : ℝ) :=
      (div_le_iff₀ hfac).mp step2
    have step3 : (N : ℝ) ^ k / (Nat.factorial k : ℝ)
        ≤ ((N : ℝ) ^ k * Real.exp (k : ℝ)) / (k : ℝ) ^ k := by
      rw [div_le_div_iff₀ hfac hkk]
      have hmul := mul_le_mul_of_nonneg_left hkfk hNnn
      linarith
    have step4 : ((N : ℝ) ^ k * Real.exp (k : ℝ)) / (k : ℝ) ^ k
        = ((N : ℝ) * Real.exp 1 / (k : ℝ)) ^ k := by
      rw [div_pow, mul_pow, Real.exp_one_pow]
    have hstep : (N : ℝ) * Real.exp 1 / (k : ℝ) ≤ A / 2 := by
      have h2 : x * Real.exp 1 / (k : ℝ) = A / 2 := by
        rw [hxdef]
        field_simp
      have h1 : (N : ℝ) * Real.exp 1 / (k : ℝ) ≤ x * Real.exp 1 / (k : ℝ) := by gcongr
      linarith
    have hnn : (0:ℝ) ≤ (N : ℝ) * Real.exp 1 / (k : ℝ) := by positivity
    have step5 : ((N : ℝ) * Real.exp 1 / (k : ℝ)) ^ k ≤ (A / 2) ^ k :=
      pow_le_pow_left₀ hnn hstep k
    have hc2 : ((k : ℝ) - 1) / 2 * (k : ℝ) = ((k.choose 2 : ℕ) : ℝ) := by
      have h' : 2 * ((k.choose 2 : ℕ) : ℝ) + (k : ℝ) = (k : ℝ) * (k : ℝ) := by
        exact_mod_cast two_mul_choose_two k
      have h'' : ((k : ℝ) - 1) / 2 * (k : ℝ) = ((k : ℝ) * (k : ℝ) - (k : ℝ)) / 2 := by ring
      rw [h'']
      linarith
    have hAk : A ^ k = (2 : ℝ) ^ (k.choose 2) := by
      rw [hAdef, ← Real.rpow_natCast ((2 : ℝ) ^ (((k : ℝ) - 1) / 2)) k,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), hc2, Real.rpow_natCast]
    have h2k : (8:ℝ) ≤ (2 : ℝ) ^ k := by
      have h1 : (2:ℕ) ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have h2 : (((2:ℕ) ^ 3 : ℕ) : ℝ) ≤ (((2:ℕ) ^ k : ℕ) : ℝ) := by exact_mod_cast h1
      norm_num at h2
      exact h2
    have hpos2 : (0:ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
    have hreal : ((N.choose k : ℕ) : ℝ) * 2 < (2 : ℝ) ^ (k.choose 2) := by
      have hb : ((N.choose k : ℕ) : ℝ) ≤ (A / 2) ^ k := by
        calc ((N.choose k : ℕ) : ℝ) ≤ (N : ℝ) ^ k / (Nat.factorial k : ℝ) := step1
          _ ≤ ((N : ℝ) ^ k * Real.exp (k : ℝ)) / (k : ℝ) ^ k := step3
          _ = ((N : ℝ) * Real.exp 1 / (k : ℝ)) ^ k := step4
          _ ≤ (A / 2) ^ k := step5
      calc ((N.choose k : ℕ) : ℝ) * 2 ≤ (A / 2) ^ k * 2 := by linarith
        _ = (2 : ℝ) ^ (k.choose 2) * (2 / (2 : ℝ) ^ k) := by
            rw [div_pow, hAk]
            ring
        _ < (2 : ℝ) ^ (k.choose 2) * 1 := by
            refine mul_lt_mul_of_pos_left ?_ hpos2
            rw [div_lt_one (by positivity)]
            linarith
        _ = (2 : ℝ) ^ (k.choose 2) := mul_one _
    exact_mod_cast hreal
  · have hkR := le_R k (by omega)
    omega

/-- Explicit form of `k·2^{k/2} ≪ R(k)`: for every `k`, `k · 2^{k/2} ≤ 2√2·e·(R(k) + 1)`. -/
theorem mul_two_pow_half_le (k : ℕ) :
    (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * Real.sqrt 2 * Real.exp 1 * ((R k : ℝ) + 1) := by
  have he2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hs2 : (1:ℝ) ≤ Real.sqrt 2 := by
    have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
    simp only [Real.sqrt_one] at h
    exact h
  have hR0 : (0:ℝ) ≤ (R k : ℝ) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have h1 : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
    have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 := by
      have hmono : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by linarith)
      rwa [Real.rpow_one] at hmono
    have hLHS : (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 4 := by nlinarith
    have a2 : (4:ℝ) ≤ 2 * Real.sqrt 2 * Real.exp 1 := by nlinarith
    nlinarith
  · have hk0 : (0:ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hfl := floor_lt_R k hk
    have hxlt : (k : ℝ) * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) / (2 * Real.exp 1) < (R k : ℝ) + 1 := by
      have h1 := Nat.lt_floor_add_one ((k : ℝ) * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) / (2 * Real.exp 1))
      have h2 : ((⌊(k : ℝ) * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) / (2 * Real.exp 1)⌋₊ : ℕ) : ℝ)
          ≤ (R k : ℝ) := by exact_mod_cast le_of_lt hfl
      linarith
    have hkA : (k : ℝ) * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) < 2 * Real.exp 1 * ((R k : ℝ) + 1) := by
      rw [div_lt_iff₀ (by positivity)] at hxlt
      linarith
    have hsplit : (2 : ℝ) ^ ((k : ℝ) / 2) = Real.sqrt 2 * (2 : ℝ) ^ (((k : ℝ) - 1) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring
    rw [hsplit]
    have hs0 : (0:ℝ) < Real.sqrt 2 := by linarith
    have hmul := mul_lt_mul_of_pos_left hkA hs0
    nlinarith [hmul]

end RealBound

end Erdos1029
