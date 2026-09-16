import Mathlib
import Proof.Defs
import Proof.Model
import Proof.Counting
import Proof.Estimates

/-!
# The deterministic counting argument

Fix a good choice function `f`, `D ≥ 1`, and a `D`-balanced subgraph `H` of `graphOf f` with
`m` vertices, `d` = minimum degree inside `H` (so every degree is at most `D d`).  Every edge of
`H` joins an `A`-vertex to a block vertex; split the edges by the size of that block:

* small blocks (`bsize ≤ m / (64 D)`): at most `m / (4 D)` vertices in total, hence at most
  `m d / 4` incident edges;
* middle blocks (`m / (64 D) < bsize < m · 2 ^ rpar m`): at most `8 (rpar m + log₂(64 D) + 1)`
  blocks, each meeting at most `|A ∩ V(H)| ≤ m` edges of `H`;
* large blocks: fewer than `m · rpar m` edges, by goodness.

Since `2 e(H) = ∑ deg ≥ m d`, this yields `e(H) ≤ 18 m (rpar m + log₂(64 D) + 2)`.
-/

open SimpleGraph Finset

namespace Erdos803

/-- A geometric bound in `ℕ`: `∑_{k < K} ⌊M / 2 ^ k⌋ ≤ 2 M`. -/
private lemma sum_range_div_two_pow_le_aux (K M : ℕ) :
    ∑ k ∈ Finset.range K, M / 2 ^ k ≤ 2 * M := by
  induction K generalizing M with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ k : ℕ, M / 2 ^ (k + 1) = M / 2 / 2 ^ k := by
      intro k
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    simp only [h, pow_zero, Nat.div_one]
    have := ih (M / 2)
    omega

/-- The tail bound `∑_{i ∈ [a, b]} ⌊N / 2 ^ i⌋ ≤ 2 ⌊N / 2 ^ a⌋`. -/
private lemma sum_Icc_div_two_pow_le (N a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, N / 2 ^ i ≤ 2 * (N / 2 ^ a) := by
  have hIco : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (b + 1 - a), N / 2 ^ (a + k) = N / 2 ^ a / 2 ^ k := by
    intro k _
    rw [pow_add, Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl hterm]
  exact sum_range_div_two_pow_le_aux _ _

/-- At most `R + log₂(64 D) + 1` indices `i` satisfy `m / (64 D) < n / 2 ^ i < m · 2 ^ R`. -/
private lemma card_mid_le (n m R : ℕ) {D : ℝ} (hD : 1 ≤ D) (hm : 1 ≤ m) (I : Finset ℕ)
    (hI : ∀ i ∈ I, (m : ℝ) / (64 * D) < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) :
    (I.card : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) + 1 := by
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  have hcnn : 0 ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by nlinarith)
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have h0 : I.min' hne ∈ I := I.min'_mem hne
    have h1 : I.max' hne ∈ I := I.max'_mem hne
    set i₀ : ℕ := I.min' hne with hi₀
    set i₁ : ℕ := I.max' hne with hi₁
    have hsub : I ⊆ Finset.Icc i₀ i₁ := fun i hi =>
      Finset.mem_Icc.mpr ⟨I.min'_le i hi, I.le_max' i hi⟩
    have hle : i₀ ≤ i₁ := I.min'_le _ h1
    have hcard : I.card ≤ i₁ - i₀ + 1 := by
      have h := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h
      omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hup : (m : ℝ) * 2 ^ i₁ < 64 * D * n := by
      have h := (hI i₁ h1).1
      have hcast : ((n / 2 ^ i₁ : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ i₁ : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at hcast
      have h2 : (m : ℝ) / (64 * D) < (n : ℝ) / 2 ^ i₁ := lt_of_lt_of_le h hcast
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h2
      linarith
    have hlow : (n : ℝ) < (m : ℝ) * 2 ^ R * 2 ^ i₀ := by
      have h := (hI i₀ h0).2
      have hq : 0 < 2 ^ i₀ := Nat.two_pow_pos i₀
      have hnat : n < m * 2 ^ R * 2 ^ i₀ := by
        calc n < n / 2 ^ i₀ * 2 ^ i₀ + 2 ^ i₀ := Nat.lt_div_mul_add hq
          _ = (n / 2 ^ i₀ + 1) * 2 ^ i₀ := by ring
          _ ≤ m * 2 ^ R * 2 ^ i₀ := Nat.mul_le_mul_right _ (by omega)
      exact_mod_cast hnat
    have hkey : (2 : ℝ) ^ (i₁ - i₀) < 64 * D * 2 ^ R := by
      have hpow : (2 : ℝ) ^ i₁ = 2 ^ (i₁ - i₀) * 2 ^ i₀ := by
        rw [← pow_add]
        congr 1
        omega
      have hp0 : (0 : ℝ) < (2 : ℝ) ^ i₀ := by positivity
      have h2 : (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) < 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) := by
        calc (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) = (m : ℝ) * 2 ^ i₁ := by rw [hpow]
          _ < 64 * D * n := hup
          _ < 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) := by nlinarith
      have hmul : (0 : ℝ) < (m : ℝ) * 2 ^ i₀ := by positivity
      rw [show (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) = 2 ^ (i₁ - i₀) * ((m : ℝ) * 2 ^ i₀) by ring,
        show 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) = 64 * D * 2 ^ R * ((m : ℝ) * 2 ^ i₀) by
          ring] at h2
      exact lt_of_mul_lt_mul_right h2 hmul.le
    have hlog : ((i₁ - i₀ : ℕ) : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) := by
      have hmono : Real.logb 2 ((2 : ℝ) ^ (i₁ - i₀)) ≤ Real.logb 2 (64 * D * 2 ^ R) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hkey.le
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
        Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one] at hmono
      linarith
    have hcastI : (I.card : ℝ) ≤ ((i₁ - i₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    linarith

/-- Block vertices in blocks of size at most `m / (64 D)` number at most `m / (4 D)`. -/
private lemma card_small_le {n m : ℕ} {D : ℝ} (hD : 1 ≤ D) (Bs : Finset (BVertex n))
    (hBs : ∀ b ∈ Bs, ((bsize n b.1 : ℕ) : ℝ) ≤ (m : ℝ) / (64 * D)) :
    (Bs.card : ℝ) ≤ (m : ℝ) / (4 * D) := by
  classical
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  set S : ℝ := (m : ℝ) / (64 * D) with hS
  have hSnn : 0 ≤ S := by positivity
  set SI : Finset ℕ := (Finset.Icc 4 (top n)).filter (fun i => ((n / 2 ^ i : ℕ) : ℝ) ≤ S) with hSI
  have hSImem : ∀ i : ℕ, i ∈ SI ↔ i ∈ Finset.Icc 4 (top n) ∧ ((n / 2 ^ i : ℕ) : ℝ) ≤ S := by
    intro i
    rw [hSI, Finset.mem_filter]
  set SmallIdx : Finset (BlockIdx n) := Finset.univ.filter (fun p => (p.1 : ℕ) ∈ SI) with hSmall
  have hsub : Bs ⊆ SmallIdx.sigma (fun p => (Finset.univ : Finset (Fin (bsize n p)))) := by
    intro b hb
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hSmall, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hSImem _).mpr ⟨b.1.1.2, hBs b hb⟩⟩
  have hcard : Bs.card ≤ ∑ p ∈ SmallIdx, bsize n p := by
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sigma]
    simp
  have hmaps : ∀ p ∈ SmallIdx, (p.1 : ℕ) ∈ SI := by
    intro p hp
    rw [hSmall, Finset.mem_filter] at hp
    exact hp.2
  have hfib8 : ∀ i : ℕ, (SmallIdx.filter fun p => (p.1 : ℕ) = i).card ≤ 8 := by
    intro i
    have hb : (SmallIdx.filter fun p => (p.1 : ℕ) = i).card
        ≤ (Finset.univ : Finset (Fin 8)).card := by
      refine Finset.card_le_card_of_injOn Prod.snd
        (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun p hp p' hp' h => ?_)
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      exact Prod.ext (Subtype.ext (hp.2.trans hp'.2.symm)) h
    simpa using hb
  have hsum : ∑ p ∈ SmallIdx, bsize n p ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => bsize n p), Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hbody : ∀ p ∈ SmallIdx.filter (fun p => (p.1 : ℕ) = i), bsize n p = n / 2 ^ i := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [bsize, hp.2]
    rw [Finset.sum_congr rfl hbody, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hfib8 i)
  have hcard2 : Bs.card ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := le_trans hcard hsum
  rcases SI.eq_empty_or_nonempty with hempty | hne
  · rw [hempty] at hcard2
    simp only [Finset.sum_empty, Nat.mul_zero, Nat.le_zero] at hcard2
    rw [hcard2, Nat.cast_zero]
    positivity
  · have h0 : SI.min' hne ∈ SI := SI.min'_mem hne
    set i₀ : ℕ := SI.min' hne with hi₀
    have h0' : ((n / 2 ^ i₀ : ℕ) : ℝ) ≤ S := ((hSImem i₀).mp h0).2
    have hsubI : SI ⊆ Finset.Icc i₀ (top n) := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨SI.min'_le i hi, (Finset.mem_Icc.mp ((hSImem i).mp hi).1).2⟩
    have hgeom : ∑ i ∈ SI, n / 2 ^ i ≤ 2 * (n / 2 ^ i₀) :=
      le_trans (Finset.sum_le_sum_of_subset hsubI) (sum_Icc_div_two_pow_le _ _ _)
    have hfin : Bs.card ≤ 16 * (n / 2 ^ i₀) :=
      calc Bs.card ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := hcard2
        _ ≤ 8 * (2 * (n / 2 ^ i₀)) := Nat.mul_le_mul_left 8 hgeom
        _ = 16 * (n / 2 ^ i₀) := by ring
    have hfinR : (Bs.card : ℝ) ≤ 16 * ((n / 2 ^ i₀ : ℕ) : ℝ) := by exact_mod_cast hfin
    have hgoal : (16 : ℝ) * S = (m : ℝ) / (4 * D) := by
      rw [hS]
      field_simp
      ring
    linarith

/-- Alon's counting bound: a `D`-balanced subgraph `H` of the graph of a good choice function
has at most `18 m (rpar m + log₂ (64 D) + 2)` edges, where `m` is its number of vertices. -/
theorem edges_le_of_good {n : ℕ} {f : Choice n} (hf : Good f) (_hn : 2 ^ 40 ≤ n) {D : ℝ}
    (hD : 1 ≤ D) (H : (graphOf f).Subgraph) (hH : Balanced D H) :
    (H.edgeSet.ncard : ℝ) ≤
      18 * H.verts.ncard * (rpar H.verts.ncard + Real.logb 2 (64 * D) + 2) := by
  classical
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  have hcnn : 0 ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by nlinarith)
  set m : ℕ := H.verts.ncard with hm_def
  set R : ℕ := rpar m with hR_def
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · have hV : H.verts = ∅ := by
      refine (Set.ncard_eq_zero (Set.toFinite _)).mp ?_
      rw [← hm_def]
      exact hm0
    have hE : H.edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        rw [Subgraph.mem_edgeSet] at he
        have hu : u ∈ H.verts := H.edge_vert he
        rw [hV] at hu
        exact hu
    rw [hE, Set.ncard_empty, hm0]
    norm_num
  -- the two sides of the bipartition, inside `H`
  set VH : Finset (Vtx n) := H.verts.toFinite.toFinset with hVH_def
  have hVHcard : VH.card = m := by
    rw [hm_def, hVH_def]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  set A' : Finset (Fin n) := Finset.univ.filter (fun a => Sum.inl a ∈ H.verts) with hA'_def
  set BH : Finset (BVertex n) := Finset.univ.filter (fun b => Sum.inr b ∈ H.verts) with hBH_def
  have hA'mem : ∀ a : Fin n, a ∈ A' ↔ Sum.inl a ∈ H.verts := by
    intro a
    rw [hA'_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hBHmem : ∀ b : BVertex n, b ∈ BH ↔ Sum.inr b ∈ H.verts := by
    intro b
    rw [hBH_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hA'card : A'.card ≤ m := by
    rw [← hVHcard]
    refine Finset.card_le_card_of_injOn Sum.inl (fun a ha => ?_) (fun _ _ _ _ h => by simpa using h)
    rw [Finset.mem_coe, hVH_def, Set.Finite.mem_toFinset]
    exact (hA'mem a).1 (Finset.mem_coe.mp ha)
  have hBHcard : BH.card ≤ m := by
    rw [← hVHcard]
    refine Finset.card_le_card_of_injOn Sum.inr (fun b hb => ?_) (fun _ _ _ _ h => by simpa using h)
    rw [Finset.mem_coe, hVH_def, Set.Finite.mem_toFinset]
    exact (hBHmem b).1 (Finset.mem_coe.mp hb)
  -- the edges of `H`, presented as pairs
  set P : Finset (Fin n × BVertex n) :=
    (A' ×ˢ BH).filter (fun ab => H.Adj (Sum.inl ab.1) (Sum.inr ab.2)) with hP_def
  have hPmem : ∀ ab : Fin n × BVertex n,
      ab ∈ P ↔ ab.1 ∈ A' ∧ ab.2 ∈ BH ∧ H.Adj (Sum.inl ab.1) (Sum.inr ab.2) := by
    intro ab
    rw [hP_def, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hedges : H.edgeSet.ncard = P.card := by
    have hinj : Function.Injective
        (fun ab : Fin n × BVertex n => s(Sum.inl ab.1, Sum.inr ab.2)) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
        exact Prod.ext h1 h2
      · exact absurd h1 (by simp)
    have himg : H.edgeSet
        = (fun ab : Fin n × BVertex n => s(Sum.inl ab.1, Sum.inr ab.2)) '' (P : Set _) := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        constructor
        · intro he
          rw [Subgraph.mem_edgeSet] at he
          have hs := H.adj_sub he
          rcases u with a | b <;> rcases v with a' | b'
          · exact absurd hs (graphOf_not_adj_inl_inl f a a')
          · refine ⟨(a, b'), ?_, rfl⟩
            rw [Finset.mem_coe, hPmem]
            exact ⟨(hA'mem a).2 (H.edge_vert he), (hBHmem b').2 (H.edge_vert he.symm), he⟩
          · refine ⟨(a', b), ?_, Sym2.eq_swap⟩
            rw [Finset.mem_coe, hPmem]
            exact ⟨(hA'mem a').2 (H.edge_vert he.symm), (hBHmem b).2 (H.edge_vert he), he.symm⟩
          · exact absurd hs (graphOf_not_adj_inr_inr f b b')
        · rintro ⟨ab, hab, heq⟩
          rw [← heq]
          exact ((hPmem ab).1 (Finset.mem_coe.mp hab)).2.2
    rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  -- split the pairs according to the size of the block
  set S : ℝ := (m : ℝ) / (64 * D) with hS_def
  set Bs : Finset (BVertex n) := BH.filter (fun b => ((bsize n b.1 : ℕ) : ℝ) ≤ S) with hBs_def
  set Bl : Finset (BVertex n) := BH.filter (fun b => m * 2 ^ R ≤ bsize n b.1) with hBl_def
  set Ps : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) with hPs_def
  set Pl : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => m * 2 ^ R ≤ bsize n ab.2.1) with hPl_def
  set Pm : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => ¬ (((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) ∧ ¬ (m * 2 ^ R ≤ bsize n ab.2.1))
    with hPm_def
  have hBsmem : ∀ b : BVertex n, b ∈ Bs ↔ b ∈ BH ∧ ((bsize n b.1 : ℕ) : ℝ) ≤ S := by
    intro b
    rw [hBs_def, Finset.mem_filter]
  have hBlmem : ∀ b : BVertex n, b ∈ Bl ↔ b ∈ BH ∧ m * 2 ^ R ≤ bsize n b.1 := by
    intro b
    rw [hBl_def, Finset.mem_filter]
  have hPsmem : ∀ ab : Fin n × BVertex n,
      ab ∈ Ps ↔ ab ∈ P ∧ ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S := by
    intro ab
    rw [hPs_def, Finset.mem_filter]
  have hPlmem : ∀ ab : Fin n × BVertex n,
      ab ∈ Pl ↔ ab ∈ P ∧ m * 2 ^ R ≤ bsize n ab.2.1 := by
    intro ab
    rw [hPl_def, Finset.mem_filter]
  have hPmmem : ∀ ab : Fin n × BVertex n, ab ∈ Pm ↔ ab ∈ P ∧
      ¬ (((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) ∧ ¬ (m * 2 ^ R ≤ bsize n ab.2.1) := by
    intro ab
    rw [hPm_def, Finset.mem_filter]
  have hsplit : P.card ≤ Ps.card + Pm.card + Pl.card := by
    have hsub : P ⊆ Ps ∪ Pm ∪ Pl := by
      intro ab hab
      by_cases h1 : ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hPsmem ab).mpr ⟨hab, h1⟩))
      · by_cases h2 : m * 2 ^ R ≤ bsize n ab.2.1
        · exact Finset.mem_union_right _ ((hPlmem ab).mpr ⟨hab, h2⟩)
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ ((hPmmem ab).mpr ⟨hab, h1, h2⟩))
    calc P.card ≤ (Ps ∪ Pm ∪ Pl).card := Finset.card_le_card hsub
      _ ≤ (Ps ∪ Pm).card + Pl.card := Finset.card_union_le _ _
      _ ≤ Ps.card + Pm.card + Pl.card := by
          have := Finset.card_union_le Ps Pm
          omega
  -- (1) large blocks: goodness of `f`
  have hcrossmem : ∀ (B' : Finset (BVertex n)) (ab : Fin n × BVertex n),
      ab ∈ crossEdges f A' B' ↔ (ab.1 ∈ A' ∧ ab.2 ∈ B') ∧ f ab.1 ab.2.1 = ab.2.2 := by
    intro B' ab
    simp only [crossEdges, Finset.mem_filter, Finset.mem_product]
  have hPlcard : Pl.card ≤ m * R := by
    have hBlcard : Bl.card ≤ m := by
      refine le_trans (Finset.card_le_card ?_) hBHcard
      intro b hb
      exact ((hBlmem b).mp hb).1
    have hBlsub : Bl ⊆ largeB n m := by
      intro b hb
      simp only [largeB, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hR_def]
      exact ((hBlmem b).mp hb).2
    have hPlsub : Pl ⊆ crossEdges f A' Bl := by
      intro ab hab
      obtain ⟨habP, hlarge⟩ := (hPlmem ab).mp hab
      obtain ⟨h1, h2, h3⟩ := (hPmem ab).1 habP
      refine (hcrossmem Bl ab).mpr ⟨⟨h1, (hBlmem ab.2).mpr ⟨h2, hlarge⟩⟩, ?_⟩
      obtain ⟨a, p, c⟩ := ab
      exact (graphOf_adj_inl_inr f a p c).mp (H.adj_sub h3)
    by_cases hmn : m ≤ n
    · exact le_of_lt (lt_of_le_of_lt (Finset.card_le_card hPlsub)
        (hf m hm1 hmn A' hA'card Bl hBlsub hBlcard))
    · have hBlempty : Bl = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        obtain ⟨-, hlarge⟩ := (hBlmem b).mp hb
        have h1 : bsize n b.1 ≤ n := Nat.div_le_self _ _
        have h2 : m * 1 ≤ m * 2 ^ R := Nat.mul_le_mul_left m Nat.one_le_two_pow
        rw [mul_one] at h2
        exact hmn (le_trans (le_trans h2 hlarge) h1)
      have hPlempty : Pl = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ab hab
        have h := (hcrossmem Bl ab).mp (hPlsub hab)
        rw [hBlempty] at h
        exact absurd h.1.2 (Finset.notMem_empty _)
      simp [hPlempty]
  -- (2) middle blocks: few indices, each meeting at most `|A'|` pairs
  set MI : Finset ℕ := (Finset.Icc 4 (top n)).filter
    (fun i => S < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) with hMI_def
  have hMImem : ∀ i : ℕ, i ∈ MI ↔ i ∈ Finset.Icc 4 (top n) ∧
      (S < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) := by
    intro i
    rw [hMI_def, Finset.mem_filter]
  set MidIdx : Finset (BlockIdx n) :=
    Finset.univ.filter (fun p => (p.1 : ℕ) ∈ MI) with hMid_def
  have hMidmem : ∀ p : BlockIdx n, p ∈ MidIdx ↔ (p.1 : ℕ) ∈ MI := by
    intro p
    rw [hMid_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hPmfib : ∀ ab ∈ Pm, ab.2.1 ∈ MidIdx := by
    intro ab hab
    obtain ⟨-, h1, h2⟩ := (hPmmem ab).mp hab
    exact (hMidmem _).mpr ((hMImem _).mpr ⟨ab.2.1.1.2, not_le.mp h1, not_le.mp h2⟩)
  have hPmcard : Pm.card ≤ MidIdx.card * A'.card := by
    rw [Finset.card_eq_sum_card_fiberwise hPmfib]
    calc ∑ p ∈ MidIdx, (Pm.filter fun ab => ab.2.1 = p).card
        ≤ ∑ _p ∈ MidIdx, A'.card := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          refine Finset.card_le_card_of_injOn Prod.fst (fun ab hab => ?_)
            (fun ab hab ab' hab' hfst => ?_)
          · rw [Finset.mem_coe, Finset.mem_filter] at hab
            exact Finset.mem_coe.mpr ((hPmem ab).1 ((hPmmem ab).mp hab.1).1).1
          · rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
            obtain ⟨habP, hq⟩ := hab
            obtain ⟨habP', hq'⟩ := hab'
            obtain ⟨a, q, c⟩ := ab
            obtain ⟨a', q', c'⟩ := ab'
            have hcc : c = f a q :=
              ((graphOf_adj_inl_inr f a q c).mp
                (H.adj_sub ((hPmem _).1 ((hPmmem _).mp habP).1).2.2)).symm
            have hcc' : c' = f a' q' :=
              ((graphOf_adj_inl_inr f a' q' c').mp
                (H.adj_sub ((hPmem _).1 ((hPmmem _).mp habP').1).2.2)).symm
            have haa : a = a' := hfst
            have hqq : q = q' := hq.trans hq'.symm
            subst hcc
            subst hcc'
            subst haa
            subst hqq
            rfl
      _ = MidIdx.card * A'.card := by rw [Finset.sum_const, smul_eq_mul]
  have hMidcard : MidIdx.card ≤ 8 * MI.card := by
    have hfib : ∀ p ∈ MidIdx, (p.1 : ℕ) ∈ MI := fun p hp => (hMidmem p).mp hp
    rw [Finset.card_eq_sum_card_fiberwise hfib]
    calc ∑ i ∈ MI, (MidIdx.filter fun p => (p.1 : ℕ) = i).card
        ≤ ∑ _i ∈ MI, 8 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hb : (MidIdx.filter fun p => (p.1 : ℕ) = i).card
              ≤ (Finset.univ : Finset (Fin 8)).card := by
            refine Finset.card_le_card_of_injOn Prod.snd
              (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun p hp p' hp' h => ?_)
            rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
            exact Prod.ext (Subtype.ext (hp.2.trans hp'.2.symm)) h
          simpa using hb
      _ = 8 * MI.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hMIcard : (MI.card : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) + 1 := by
    refine card_mid_le n m R hD hm1 MI (fun i hi => ?_)
    obtain ⟨-, h1, h2⟩ := (hMImem i).mp hi
    exact ⟨hS_def ▸ h1, h2⟩
  -- (3) small blocks: few vertices, each of controlled degree
  have hVHne : VH.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := Finset.exists_min_image VH (sdeg H) hVHne
  have hPsfib : ∀ ab ∈ Ps, ab.2 ∈ Bs := by
    intro ab hab
    obtain ⟨habP, hsmall⟩ := (hPsmem ab).mp hab
    exact (hBsmem ab.2).mpr ⟨((hPmem ab).1 habP).2.1, hsmall⟩
  have hPscard : Ps.card ≤ ∑ b ∈ Bs, sdeg H (Sum.inr b) := by
    rw [Finset.card_eq_sum_card_fiberwise hPsfib]
    refine Finset.sum_le_sum (fun b _ => ?_)
    have hfin : (H.neighborSet (Sum.inr b)).Finite := Set.toFinite _
    have hcardeq : sdeg H (Sum.inr b) = hfin.toFinset.card := by
      rw [sdeg, Set.ncard_eq_toFinset_card _ hfin]
    rw [hcardeq]
    refine Finset.card_le_card_of_injOn (fun ab => Sum.inl ab.1) (fun ab hab => ?_)
      (fun ab hab ab' hab' hEq => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hab
      obtain ⟨habPs, habb⟩ := hab
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Subgraph.mem_neighborSet, ← habb]
      exact (((hPmem ab).1 ((hPsmem ab).mp habPs).1).2.2).symm
    · rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
      simp only [Sum.inl.injEq] at hEq
      exact Prod.ext hEq (hab.2.trans hab'.2.symm)
  have hBscard : (Bs.card : ℝ) ≤ (m : ℝ) / (4 * D) := by
    refine card_small_le hD Bs (fun b hb => ?_)
    rw [← hS_def]
    exact ((hBsmem b).mp hb).2
  have hPssmall : (Ps.card : ℝ) ≤ (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ)) := by
    have h1 : (Ps.card : ℝ) ≤ ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := by
      calc (Ps.card : ℝ) ≤ ((∑ b ∈ Bs, sdeg H (Sum.inr b) : ℕ) : ℝ) := by exact_mod_cast hPscard
        _ = ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := by push_cast; rfl
    have h2 : ∀ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) ≤ D * (sdeg H v₀ : ℝ) := by
      intro b hb
      refine hH _ ((hBHmem b).1 ((hBsmem b).mp hb).1) v₀ ?_
      rw [hVH_def, Set.Finite.mem_toFinset] at hv₀mem
      exact hv₀mem
    calc (Ps.card : ℝ) ≤ ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := h1
      _ ≤ ∑ _b ∈ Bs, D * (sdeg H v₀ : ℝ) := Finset.sum_le_sum h2
      _ = (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- (4) the handshake bound
  have hdeg : m * sdeg H v₀ ≤ 2 * H.edgeSet.ncard := by
    have h := Finset.card_nsmul_le_sum VH (sdeg H) (sdeg H v₀) hv₀min
    rw [smul_eq_mul, hVHcard, hVH_def, sum_sdeg H] at h
    exact h
  -- assembly
  have hMnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have he : (H.edgeSet.ncard : ℝ) = (P.card : ℝ) := by rw [hedges]
  have hsplitR : (P.card : ℝ) ≤ (Ps.card : ℝ) + (Pm.card : ℝ) + (Pl.card : ℝ) := by
    exact_mod_cast hsplit
  have hPsR : (Ps.card : ℝ) ≤ (m : ℝ) * (sdeg H v₀ : ℝ) / 4 := by
    have h1 : (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ))
        ≤ ((m : ℝ) / (4 * D)) * (D * (sdeg H v₀ : ℝ)) :=
      mul_le_mul_of_nonneg_right hBscard (by positivity)
    have h2 : ((m : ℝ) / (4 * D)) * (D * (sdeg H v₀ : ℝ)) = (m : ℝ) * (sdeg H v₀ : ℝ) / 4 := by
      field_simp
    linarith
  have hPmR : (Pm.card : ℝ) ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) * (m : ℝ) := by
    have h1 : (Pm.card : ℝ) ≤ (MidIdx.card : ℝ) * (A'.card : ℝ) := by exact_mod_cast hPmcard
    have h3 : (MidIdx.card : ℝ) ≤ 8 * (MI.card : ℝ) := by exact_mod_cast hMidcard
    have h2 : (MidIdx.card : ℝ) ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) := by linarith
    have h4 : (A'.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hA'card
    have h5 : (MidIdx.card : ℝ) * (A'.card : ℝ)
        ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) * (m : ℝ) :=
      mul_le_mul h2 h4 (Nat.cast_nonneg _) (by positivity)
    linarith
  have hPlR : (Pl.card : ℝ) ≤ (m : ℝ) * (R : ℝ) := by exact_mod_cast hPlcard
  have hdegR : (m : ℝ) * (sdeg H v₀ : ℝ) ≤ 2 * (H.edgeSet.ncard : ℝ) := by exact_mod_cast hdeg
  have hMc : (0 : ℝ) ≤ (m : ℝ) * Real.logb 2 (64 * D) := mul_nonneg hMnn hcnn
  nlinarith [he, hsplitR, hPsR, hPmR, hPlR, hdegR, hMnn, hMc, hRnn]

end Erdos803
