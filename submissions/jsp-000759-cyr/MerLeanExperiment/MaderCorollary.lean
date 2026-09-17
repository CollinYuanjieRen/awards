import Mathlib
import MerLeanExperiment.Defs
import MerLeanExperiment.EdgeMenger
import MerLeanExperiment.MaderTheorem

/-!
# Corollaries of Mader's Satz 1

* `edge_rails_of_bollobas_erdos`: the affirmative answer to Erdős problem #915 under the
  edge-disjoint reading — every graph with exactly `1 + n(m-1)` vertices and exactly
  `1 + n·C(m,2)` edges has two vertices joined by `m` edge-disjoint paths.
* `edgeRailNumber_eq`: `ℓ_m(n) = ⌊m(n-1)/2⌋ + 1` for `2 ≤ m ≤ n` (Mader's Korollar).  The
  lower bound is witnessed by a *bi-wheel*: one universal vertex joined to a near-`(m-2)`-regular
  circulant-plus-matching graph on the remaining `n - 1` vertices.
-/

universe u

namespace Erdos915

open SimpleGraph Finset

variable {V : Type*}

/-! ## Elementary closure properties of `HasEdgeRails` -/

/-- Edge-disjoint paths survive passing to a supergraph. -/
theorem hasEdgeRails_mono {H G : SimpleGraph V} {m : ℕ} (h : H ≤ G) :
    HasEdgeRails H m → HasEdgeRails G m := by
  rintro ⟨u, v, huv, p, hp, hd⟩
  refine ⟨u, v, huv, fun i ↦ (p i).mapLe h, fun i ↦ ?_, fun i j hij e he ↦ ?_⟩
  · exact (Walk.isPath_mapLe h).mpr (hp i)
  · rw [Walk.edges_mapLe_eq_edges] at he ⊢
    exact hd i j hij e he

/-- If at most one vertex of `G` has degree at least `m`, then `G` has no `m` edge-disjoint
paths between two vertices: the two endpoints of such a family both have degree at least `m`. -/
theorem not_hasEdgeRails_of_degree_lt [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} {a : V}
    (h : ∀ x : V, m ≤ G.degree x → x = a) : ¬ HasEdgeRails G m := by
  rintro ⟨u, v, huv, p, hp, hd⟩
  have hr : G.IsEdgeReachable m u v := isEdgeReachable_of_edgeDisjointPaths ⟨p, hp, hd⟩
  have hu : m ≤ G.degree u := hr.le_degree huv
  have hv : m ≤ G.degree v := hr.symm.le_degree huv.symm
  exact huv ((h u hu).trans (h v hv).symm)

/-! ## The Bollobás–Erdős question, edge-disjoint reading -/

/-- `2 · C(m,2) = m (m-1)`. -/
lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
    cases k with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel]
      ring

/-- **Erdős #915, edge-disjoint reading: true for every `m ≥ 2`.**  A graph with exactly
`1 + n(m-1)` vertices and exactly `1 + n·C(m,2)` edges has two vertices joined by `m`
edge-disjoint paths. -/
theorem edge_rails_of_bollobas_erdos {m n : ℕ} (hm2 : 2 ≤ m) (hn : 1 ≤ n) {V : Type u}
    [Fintype V] (G : SimpleGraph V) (hV : Fintype.card V = 1 + n * (m - 1))
    (hE : G.edgeSet.ncard = 1 + n * m.choose 2) : HasEdgeRails G m := by
  classical
  refine mader_edge_rails hm2 G ?_ ?_
  · rw [hV]
    have h : m - 1 ≤ n * (m - 1) := Nat.le_mul_of_pos_left _ hn
    omega
  · have hsub : 1 + n * (m - 1) - 1 = n * (m - 1) := by omega
    rw [hV, hE, hsub]
    have e1 : m * (n * (m - 1)) = n * (2 * m.choose 2) := by
      rw [two_mul_choose_two]; ring
    have e2 : n * (2 * m.choose 2) = 2 * (n * m.choose 2) := by ring
    omega

/-- The membership half of Mader's Korollar: `⌊m(n-1)/2⌋ + 1` edges force `m` edge-disjoint
paths between two vertices. -/
theorem hasEdgeRails_of_le_card_edges (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (V : Type)
    [Fintype V] (G : SimpleGraph V) (hcard : Fintype.card V = n)
    (hE : m * (n - 1) / 2 + 1 ≤ G.edgeSet.ncard) : HasEdgeRails G m := by
  classical
  refine mader_edge_rails hm G (by omega) ?_
  rw [hcard]
  have h1 : m * (n - 1) ≤ 2 * (m * (n - 1) / 2) + 1 := by omega
  omega

/-! ## The sharpness example: a bi-wheel -/

section Rim

variable {N q r : ℕ}

/-- The symmetric jump set `{±1, …, ±q}` of `ZMod N`. -/
def jumps (N q : ℕ) : Finset (ZMod N) :=
  (Finset.Icc 1 q).image (fun k : ℕ ↦ (k : ZMod N)) ∪
    (Finset.Icc 1 q).image (fun k : ℕ ↦ -(k : ZMod N))

/-- Membership in `jumps`. -/
lemma mem_jumps {a : ZMod N} :
    a ∈ jumps N q ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ (a = (k : ZMod N) ∨ a = -(k : ZMod N)) := by
  simp only [jumps, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (⟨k, ⟨h1, h2⟩, rfl⟩ | ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨k, h1, h2, Or.inl rfl⟩
    · exact ⟨k, h1, h2, Or.inr rfl⟩
  · rintro ⟨k, h1, h2, rfl | rfl⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩

/-- `jumps` is symmetric. -/
lemma neg_mem_jumps {a : ZMod N} (h : a ∈ jumps N q) : -a ∈ jumps N q := by
  rw [mem_jumps] at h ⊢
  obtain ⟨k, h1, h2, hk | hk⟩ := h
  · exact ⟨k, h1, h2, Or.inr (by rw [hk])⟩
  · exact ⟨k, h1, h2, Or.inl (by rw [hk, neg_neg])⟩

/-- Small natural numbers inject into `ZMod N`. -/
lemma natCast_inj_of_lt [NeZero N] {a b : ℕ} (ha : a < N) (hb : b < N)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

/-- A positive natural number below `N` is nonzero in `ZMod N`. -/
lemma natCast_ne_zero_of_lt [NeZero N] {a : ℕ} (h0 : 0 < a) (h : a < N) :
    (a : ZMod N) ≠ 0 := by
  intro hc
  rw [ZMod.natCast_eq_zero_iff] at hc
  exact absurd (Nat.le_of_dvd h0 hc) (by omega)

/-- `0` is not a jump. -/
lemma zero_notMem_jumps [NeZero N] (hq : 2 * q < N) : (0 : ZMod N) ∉ jumps N q := by
  rw [mem_jumps]
  rintro ⟨k, h1, h2, hk⟩
  have hkN : k < N := by omega
  have hk0 : (k : ZMod N) ≠ 0 := natCast_ne_zero_of_lt h1 hkN
  rcases hk with hk | hk
  · exact hk0 hk.symm
  · exact hk0 (by rw [← neg_eq_zero, ← hk])

/-- A natural number strictly between `q` and `N - q` is not a jump. -/
lemma natCast_notMem_jumps [NeZero N] {t : ℕ} (h1 : q < t) (h2 : t + q < N) :
    (t : ZMod N) ∉ jumps N q := by
  rw [mem_jumps]
  rintro ⟨k, hk1, hk2, hk⟩
  have htN : t < N := by omega
  have hkN : k < N := by omega
  rcases hk with hk | hk
  · exact absurd (natCast_inj_of_lt htN hkN hk) (by omega)
  · have hz : ((t + k : ℕ) : ZMod N) = 0 := by
      push_cast
      rw [hk]
      ring
    have h0 : 0 < t + k := by omega
    have h1' : t + k < N := by omega
    exact natCast_ne_zero_of_lt h0 h1' hz

/-- The jump set has `2q` elements. -/
lemma card_jumps [NeZero N] (hq : 2 * q < N) : (jumps N q).card = 2 * q := by
  have hinj1 : Set.InjOn (fun k : ℕ ↦ (k : ZMod N)) (Finset.Icc 1 q) := by
    intro a ha b hb hab
    rw [Finset.coe_Icc, Set.mem_Icc] at ha hb
    exact natCast_inj_of_lt (by omega) (by omega) hab
  have hinj2 : Set.InjOn (fun k : ℕ ↦ -(k : ZMod N)) (Finset.Icc 1 q) := by
    intro a ha b hb hab
    exact hinj1 ha hb (neg_injective hab)
  have hdisj : Disjoint ((Finset.Icc 1 q).image (fun k : ℕ ↦ (k : ZMod N)))
      ((Finset.Icc 1 q).image (fun k : ℕ ↦ -(k : ZMod N))) := by
    rw [Finset.disjoint_left]
    rintro a ha hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨k1, hk1, rfl⟩ := ha
    obtain ⟨k2, hk2, hk⟩ := hb
    rw [Finset.mem_Icc] at hk1 hk2
    have hz : ((k1 + k2 : ℕ) : ZMod N) = 0 := by
      push_cast
      rw [← hk]
      ring
    have h0 : 0 < k1 + k2 := by omega
    have h1' : k1 + k2 < N := by omega
    exact natCast_ne_zero_of_lt h0 h1' hz
  rw [jumps, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
    Finset.card_image_of_injOn hinj2, Nat.card_Icc]
  omega

/-- Jump membership is decidable. -/
instance decidableMemJumps (N q : ℕ) : DecidablePred (· ∈ (↑(jumps N q) : Set (ZMod N))) :=
  fun a ↦ decidable_of_iff (a ∈ jumps N q) (by simp)

/-- The matching relation pairing `i` with `i + r` for the `r` vertices whose value lies in
`[N - 2r, N - 2r + r)`. -/
def matchRel (N r : ℕ) : ZMod N → ZMod N → Prop := fun i j ↦
  N - 2 * r ≤ i.val ∧ i.val < r + (N - 2 * r) ∧ j.val = i.val + r

instance decidableMatchRel (N r : ℕ) : DecidableRel (matchRel N r) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The rim of the bi-wheel: a circulant of degree `2q` together with a matching covering the
`2r` vertices with value at least `N - 2r`. -/
def rim (N q r : ℕ) : SimpleGraph (ZMod N) :=
  circulantGraph (↑(jumps N q) : Set (ZMod N)) ⊔ SimpleGraph.fromRel (matchRel N r)

instance decidableRimAdj (N q r : ℕ) : DecidableRel (rim N q r).Adj := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

/-- Adjacency in the circulant part. -/
lemma circ_adj [NeZero N] (hq : 2 * q < N) {u v : ZMod N} :
    (circulantGraph (↑(jumps N q) : Set (ZMod N))).Adj u v ↔ v - u ∈ jumps N q := by
  rw [circulantGraph_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · have hn := neg_mem_jumps (a := u - v) (by simpa using h)
      rwa [neg_sub] at hn
    · simpa using h
  · intro h
    refine ⟨?_, Or.inr (by simpa using h)⟩
    rintro rfl
    exact zero_notMem_jumps hq (by simpa using h)

/-- The neighbours of `v` in the circulant part are `v + s` for the jumps `s`. -/
lemma circ_degree [NeZero N] (hq : 2 * q < N) (v : ZMod N) :
    (circulantGraph (↑(jumps N q) : Set (ZMod N))).degree v = 2 * q := by
  rw [← card_neighborFinset_eq_degree]
  have hnb : (circulantGraph (↑(jumps N q) : Set (ZMod N))).neighborFinset v
      = (jumps N q).image (fun a ↦ v + a) := by
    ext u
    rw [mem_neighborFinset, circ_adj hq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨u - v, h, by ring⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  rw [hnb, Finset.card_image_of_injective _ (add_right_injective v), card_jumps hq]

/-- The matching partner of `v`. -/
def partner (N r : ℕ) (v : ZMod N) : ZMod N :=
  if v.val < r + (N - 2 * r) then ((v.val + r : ℕ) : ZMod N) else ((v.val - r : ℕ) : ZMod N)

/-- The matching has at most one edge at each vertex. -/
lemma match_neighborFinset_subset [NeZero N] (v : ZMod N) :
    (SimpleGraph.fromRel (matchRel N r)).neighborFinset v ⊆ {partner N r v} := by
  intro w hw
  rw [mem_neighborFinset, SimpleGraph.fromRel_adj] at hw
  obtain ⟨-, h | h⟩ := hw
  · obtain ⟨-, h2, h3⟩ := h
    rw [Finset.mem_singleton, partner, ite_eq_left h2, ← ZMod.natCast_zmod_val w, h3]
  · obtain ⟨h1, h2, h3⟩ := h
    have hnot : ¬ (v.val < r + (N - 2 * r)) := by omega
    rw [Finset.mem_singleton, partner, ite_eq_right hnot, ← ZMod.natCast_zmod_val w]
    congr 1
    omega

/-- Each vertex has matching degree at most one. -/
lemma match_degree_le [NeZero N] (v : ZMod N) :
    (SimpleGraph.fromRel (matchRel N r)).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree]
  simpa using Finset.card_le_card (match_neighborFinset_subset (r := r) v)

/-- Every vertex with value at least `N - 2r` is matched. -/
lemma match_degree_pos [NeZero N] (hr1 : 0 < r) (hr2 : 2 * r ≤ N) (hr3 : N < 2 * r + 2)
    {v : ZMod N} (hv : N - 2 * r ≤ v.val) :
    1 ≤ (SimpleGraph.fromRel (matchRel N r)).degree v := by
  rw [← card_neighborFinset_eq_degree, Finset.one_le_card]
  refine ⟨partner N r v, ?_⟩
  rw [mem_neighborFinset, SimpleGraph.fromRel_adj]
  have hvN : v.val < N := ZMod.val_lt v
  by_cases hc : v.val < r + (N - 2 * r)
  · have hlt : v.val + r < N := by omega
    have hpv : (partner N r v).val = v.val + r := by
      rw [partner, ite_eq_left hc, ZMod.val_cast_of_lt hlt]
    refine ⟨fun hcc ↦ ?_, Or.inl ⟨hv, hc, hpv⟩⟩
    have h2 : v.val = (partner N r v).val := congrArg ZMod.val hcc
    omega
  · have hlt : v.val - r < N := by omega
    have hpv : (partner N r v).val = v.val - r := by
      rw [partner, ite_eq_right hc, ZMod.val_cast_of_lt hlt]
    refine ⟨fun hcc ↦ ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · have h2 : v.val = (partner N r v).val := congrArg ZMod.val hcc
      omega
    · rw [hpv]; omega
    · rw [hpv]; omega
    · rw [hpv]; omega

/-- A matching edge shifts the value by exactly `r`. -/
lemma match_adj_diff [NeZero N] {v w : ZMod N}
    (h : (SimpleGraph.fromRel (matchRel N r)).Adj v w) :
    w - v = (r : ZMod N) ∨ v - w = (r : ZMod N) := by
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · left
    have hw : w = v + (r : ZMod N) := by
      rw [← ZMod.natCast_zmod_val w, h.2.2, Nat.cast_add, ZMod.natCast_zmod_val]
    rw [hw]
    ring
  · right
    have hv : v = w + (r : ZMod N) := by
      rw [← ZMod.natCast_zmod_val v, h.2.2, Nat.cast_add, ZMod.natCast_zmod_val]
    rw [hv]
    ring

/-- The neighbourhood of a vertex in the rim splits into the circulant and matching parts. -/
lemma rim_neighborFinset [NeZero N] (v : ZMod N) :
    (rim N q r).neighborFinset v
      = (circulantGraph (↑(jumps N q) : Set (ZMod N))).neighborFinset v ∪
        (SimpleGraph.fromRel (matchRel N r)).neighborFinset v := by
  ext w
  simp only [Finset.mem_union, mem_neighborFinset]
  exact Iff.rfl

/-- The circulant and matching parts share no edge at a vertex. -/
lemma rim_neighbor_disjoint [NeZero N] (hq : 2 * q < N) (hqr : q < r) (hrN : r + q < N)
    (v : ZMod N) :
    Disjoint ((circulantGraph (↑(jumps N q) : Set (ZMod N))).neighborFinset v)
      ((SimpleGraph.fromRel (matchRel N r)).neighborFinset v) := by
  rw [Finset.disjoint_right]
  intro w hw hw'
  rw [mem_neighborFinset] at hw hw'
  have hj : w - v ∈ jumps N q := (circ_adj hq).mp hw'
  rcases match_adj_diff hw with h | h
  · exact natCast_notMem_jumps hqr hrN (h ▸ hj)
  · have hneg : -(w - v) = (r : ZMod N) := by rw [neg_sub]; exact h
    exact natCast_notMem_jumps hqr hrN (hneg ▸ neg_mem_jumps hj)

/-- Every rim degree is at most `2q + 1`. -/
lemma rim_degree_le [NeZero N] (hq : 2 * q < N) (v : ZMod N) :
    (rim N q r).degree v ≤ 2 * q + 1 := by
  rw [← card_neighborFinset_eq_degree, rim_neighborFinset]
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, circ_degree hq]
  exact Nat.add_le_add_left (match_degree_le v) _

/-- The rim has at least `N·2q + 2r` in its degree sum. -/
lemma sum_rim_degree_ge [NeZero N] (hq : 2 * q < N) (hr1 : 0 < r) (hr2 : 2 * r ≤ N)
    (hr3 : N < 2 * r + 2) (hqr : q < r) :
    N * (2 * q) + 2 * r ≤ ∑ v : ZMod N, (rim N q r).degree v := by
  have hrN : r + q < N := by omega
  have hsplit : ∀ v : ZMod N, (rim N q r).degree v
      = 2 * q + (SimpleGraph.fromRel (matchRel N r)).degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, rim_neighborFinset,
      Finset.card_union_of_disjoint (rim_neighbor_disjoint hq hqr hrN v),
      card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, circ_degree hq]
  have hle : (Finset.univ.filter (fun v : ZMod N ↦ N - 2 * r ≤ v.val)).card
      ≤ ∑ v : ZMod N, (SimpleGraph.fromRel (matchRel N r)).degree v := by
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    by_cases hv : N - 2 * r ≤ v.val
    · rw [ite_eq_left hv]
      exact match_degree_pos hr1 hr2 hr3 hv
    · rw [ite_eq_right hv]
      exact Nat.zero_le _
  have hsub : (Finset.univ.filter (fun v : ZMod N ↦ ¬ (N - 2 * r ≤ v.val)))
      ⊆ (Finset.range (N - 2 * r)).image (fun k : ℕ ↦ (k : ZMod N)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨v.val, Finset.mem_range.mpr (by omega), ZMod.natCast_zmod_val v⟩
  have h3 : ((Finset.range (N - 2 * r)).image (fun k : ℕ ↦ (k : ZMod N))).card ≤ N - 2 * r :=
    le_trans Finset.card_image_le (by rw [Finset.card_range])
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod N))) (fun v : ZMod N ↦ N - 2 * r ≤ v.val)
  rw [Finset.card_univ, ZMod.card] at h2
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  omega

/-- The relation defining the bi-wheel. -/
def biwheelRel (N q r : ℕ) : Option (ZMod N) → Option (ZMod N) → Prop
  | some i, some j => (rim N q r).Adj i j
  | some _, none => True
  | none, _ => False

instance decidableBiwheelRel (N q r : ℕ) : DecidableRel (biwheelRel N q r) := by
  intro a b
  match a, b with
  | some i, some j => exact inferInstanceAs (Decidable ((rim N q r).Adj i j))
  | some _, none => exact inferInstanceAs (Decidable True)
  | none, _ => exact inferInstanceAs (Decidable False)

/-- **The bi-wheel**: one universal vertex joined to every vertex of the rim. -/
def biwheel (N q r : ℕ) : SimpleGraph (Option (ZMod N)) :=
  SimpleGraph.fromRel (biwheelRel N q r)

instance decidableBiwheelAdj (N q r : ℕ) : DecidableRel (biwheel N q r).Adj := fun a b ↦
  decidable_of_iff _ (SimpleGraph.fromRel_adj (biwheelRel N q r) a b).symm

/-- Adjacency of two rim vertices in the bi-wheel. -/
@[simp] lemma biwheel_adj_some_some (i j : ZMod N) :
    (biwheel N q r).Adj (some i) (some j) ↔ (rim N q r).Adj i j := by
  rw [biwheel, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨fun hc ↦ h.ne (Option.some.inj hc), Or.inl h⟩

/-- Every rim vertex is adjacent to the hub. -/
@[simp] lemma biwheel_adj_some_none (i : ZMod N) :
    (biwheel N q r).Adj (some i) none := by
  rw [biwheel, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl trivial⟩

/-- The hub is adjacent to every rim vertex. -/
@[simp] lemma biwheel_adj_none_some (j : ZMod N) :
    (biwheel N q r).Adj none (some j) := (biwheel_adj_some_none j).symm

/-- The hub has degree `N`. -/
lemma degree_biwheel_none [NeZero N] :
    (biwheel N q r).degree (none : Option (ZMod N)) = N := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_option]
  have hnn : ¬ (biwheel N q r).Adj (none : Option (ZMod N)) none := (biwheel N q r).irrefl
  simp only [hnn, ite_false, biwheel_adj_none_some, ite_true, zero_add, Finset.sum_const,
    Finset.card_univ, ZMod.card, smul_eq_mul, Nat.mul_one]

/-- A rim vertex has bi-wheel degree one more than its rim degree. -/
lemma degree_biwheel_some [NeZero N] (i : ZMod N) :
    (biwheel N q r).degree (some i) = (rim N q r).degree i + 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_option]
  simp only [biwheel_adj_some_none, ite_true, biwheel_adj_some_some]
  rw [← Finset.card_filter, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree,
    Nat.add_comm]

/-- The degree sum of the bi-wheel. -/
lemma sum_degree_biwheel [NeZero N] :
    ∑ p : Option (ZMod N), (biwheel N q r).degree p
      = 2 * N + ∑ v : ZMod N, (rim N q r).degree v := by
  rw [Fintype.sum_option, degree_biwheel_none]
  simp only [degree_biwheel_some]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
    Nat.mul_one]
  omega

/-- With `r = 0` the matching is empty. -/
lemma match_degree_zero [NeZero N] (v : ZMod N) :
    (SimpleGraph.fromRel (matchRel N 0)).degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_neighborFinset, SimpleGraph.fromRel_adj] at hw
  rcases hw with ⟨-, h | h⟩ <;> · obtain ⟨h1, h2, -⟩ := h; omega

/-- With `r = 0` the rim is the plain circulant, of degree `2q`. -/
lemma rim_degree_zero [NeZero N] (hq : 2 * q < N) (v : ZMod N) :
    (rim N q 0).degree v = 2 * q := by
  rw [← card_neighborFinset_eq_degree, rim_neighborFinset]
  have hempty : (SimpleGraph.fromRel (matchRel N 0)).neighborFinset v = ∅ := by
    rw [← Finset.card_eq_zero, card_neighborFinset_eq_degree, match_degree_zero]
  rw [hempty, Finset.union_empty, card_neighborFinset_eq_degree, circ_degree hq]

/-- Choice of rim parameters realising max degree `d` and degree sum at least `N·d - 1`. -/
lemma exists_rim_params (N d : ℕ) [NeZero N] (hd : d + 1 ≤ N) :
    ∃ q r : ℕ, (∀ v : ZMod N, (rim N q r).degree v ≤ d) ∧
      N * d ≤ (∑ v : ZMod N, (rim N q r).degree v) + 1 := by
  set q : ℕ := d / 2 with hqdef
  have hqN : 2 * q < N := by omega
  by_cases hpar : d % 2 = 0
  · have hdq : 2 * q = d := by omega
    refine ⟨q, 0, fun v ↦ ?_, ?_⟩
    · rw [rim_degree_zero hqN v]; omega
    · have hsum : ∑ v : ZMod N, (rim N q 0).degree v = N * (2 * q) := by
        simp only [rim_degree_zero hqN]
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
      rw [hsum, hdq]
      omega
  · have hdq : 2 * q + 1 = d := by omega
    set r : ℕ := N / 2 with hrdef
    have hr1 : 0 < r := by omega
    have hr2 : 2 * r ≤ N := by omega
    have hr3 : N < 2 * r + 2 := by omega
    have hqr : q < r := by omega
    refine ⟨q, r, fun v ↦ ?_, ?_⟩
    · have h := rim_degree_le (q := q) (r := r) hqN v
      omega
    · have h := sum_rim_degree_ge hqN hr1 hr2 hr3 hqr
      have e : N * (2 * q) + N = N * d := by rw [← hdq]; ring
      omega

end Rim

/-! ## Mader's Korollar -/

/-- `ℓ_m(n) = ⌊m(n-1)/2⌋ + 1` for `2 ≤ m ≤ n` (Mader 1973, Korollar). -/
theorem edgeRailNumber_eq (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    IsLeast {k : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n → k ≤ G.edgeSet.ncard → HasEdgeRails G m}
      (m * (n - 1) / 2 + 1) := by
  constructor
  · intro V _ G hcard hE
    exact hasEdgeRails_of_le_card_edges m n hm hmn V G hcard hE
  · intro b hb
    by_contra hlt
    rw [Nat.not_le] at hlt
    set N : ℕ := n - 1 with hNdef
    have hN1 : 1 ≤ N := by omega
    have hNZ : NeZero N := ⟨by omega⟩
    obtain ⟨q, r, hdeg, hsum⟩ := exists_rim_params N (m - 2) (by omega)
    have hcard : Fintype.card (Option (ZMod N)) = n := by
      rw [Fintype.card_option, ZMod.card]
      omega
    have hdegs : ∀ x : Option (ZMod N), m ≤ (biwheel N q r).degree x → x = none := by
      rintro (_ | i) hx
      · rfl
      · rw [degree_biwheel_some] at hx
        have h := hdeg i
        omega
    have hno : ¬ HasEdgeRails (biwheel N q r) m := not_hasEdgeRails_of_degree_lt hdegs
    have h2E : 2 * (biwheel N q r).edgeSet.ncard
        = 2 * N + ∑ v : ZMod N, (rim N q r).degree v := by
      rw [ncard_edgeSet_eq, ← (biwheel N q r).sum_degrees_eq_twice_card_edges,
        sum_degree_biwheel]
    have hm2 : m - 2 + 2 = m := by omega
    have hmN : N * (m - 2) + 2 * N = m * N := by
      calc N * (m - 2) + 2 * N = (m - 2 + 2) * N := by ring
        _ = m * N := by rw [hm2]
    have hble : b ≤ (biwheel N q r).edgeSet.ncard := by omega
    exact hno (hb (Option (ZMod N)) (biwheel N q r) hcard hble)

end Erdos915
