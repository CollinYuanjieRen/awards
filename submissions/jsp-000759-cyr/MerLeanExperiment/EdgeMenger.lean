import Mathlib
import MerLeanExperiment.Defs

/-!
# Menger's theorem, edge form

Mathlib (rev `1fe0a51a`) knows `SimpleGraph.IsEdgeReachable` but not the edge form of Menger's
theorem.  This file supplies it for finite simple graphs, via the Ford–Fulkerson argument
specialised to unit capacities: a *flow* is a finite set `F` of darts containing no dart together
with its reverse, whose excess vanishes away from the two terminals.  A flow of maximum excess at
`u` admits no residual augmenting path, so the residually reachable set yields an edge cut whose
size is exactly that excess; conversely a flow of excess `k` decomposes into `k` edge-disjoint
`u`–`v` walks, which one straightens into paths with `SimpleGraph.Walk.bypass`.
-/

namespace Erdos915

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- `k` pairwise edge-disjoint `u`–`v` paths. -/
def EdgeDisjointPaths (G : SimpleGraph V) (u v : V) (k : ℕ) : Prop :=
  ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧ ∀ i j, i ≠ j → ∀ e ∈ (p i).edges, e ∉ (p j).edges

section Flow

variable [DecidableEq V]

/-- The number of darts of `F` leaving `x`. -/
def outDegree (F : Finset G.Dart) (x : V) : ℕ := (F.filter fun d ↦ d.fst = x).card

/-- The number of darts of `F` entering `x`. -/
def inDegree (F : Finset G.Dart) (x : V) : ℕ := (F.filter fun d ↦ d.snd = x).card

/-- The excess of `F` at `x`: darts leaving `x` minus darts entering `x`. -/
def excess (F : Finset G.Dart) (x : V) : ℤ := (outDegree F x : ℤ) - (inDegree F x : ℤ)

/-- The empty flow has zero excess everywhere. -/
@[simp] theorem excess_empty (x : V) : excess (∅ : Finset G.Dart) x = 0 := by
  simp [excess, outDegree, inDegree]

/-- Inserting a new dart raises the excess at its tail and lowers it at its head. -/
theorem excess_insert {F : Finset G.Dart} {d : G.Dart} (hd : d ∉ F) (x : V) :
    excess (insert d F) x =
      excess F x + (if d.fst = x then 1 else 0) - (if d.snd = x then 1 else 0) := by
  have hnot : ∀ p : G.Dart → Prop, ∀ _ : DecidablePred p, d ∉ F.filter p := by
    intro p _ hc
    exact hd (Finset.filter_subset _ _ hc)
  have hout : outDegree (insert d F) x = outDegree F x + if d.fst = x then 1 else 0 := by
    unfold outDegree
    rw [Finset.filter_insert]
    split <;> rename_i h
    · rw [Finset.card_insert_of_notMem (hnot _ _)]
    · simp
  have hin : inDegree (insert d F) x = inDegree F x + if d.snd = x then 1 else 0 := by
    unfold inDegree
    rw [Finset.filter_insert]
    split <;> rename_i h
    · rw [Finset.card_insert_of_notMem (hnot _ _)]
    · simp
  simp only [excess, hout, hin, Nat.cast_add]
  split <;> split <;> push_cast <;> ring

/-- Erasing a dart lowers the excess at its tail and raises it at its head. -/
theorem excess_erase {F : Finset G.Dart} {d : G.Dart} (hd : d ∈ F) (x : V) :
    excess (F.erase d) x =
      excess F x - (if d.fst = x then 1 else 0) + (if d.snd = x then 1 else 0) := by
  have h := excess_insert (F := F.erase d) (d := d) (Finset.notMem_erase d F) x
  rw [Finset.insert_erase hd] at h
  omega

omit [DecidableEq V] in
/-- A walk whose darts are dart-by-dart witnessed by a relation on vertices. -/
theorem exists_walk_darts {P : G.Dart → Prop} {a b : V}
    (h : Relation.ReflTransGen (fun x y ↦ ∃ d : G.Dart, d.fst = x ∧ d.snd = y ∧ P d) a b) :
    ∃ p : G.Walk a b, ∀ d ∈ p.darts, P d := by
  induction h with
  | refl => exact ⟨Walk.nil, by simp⟩
  | @tail c e _ hce ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨d, hd1, hd2, hdP⟩ := hce
      have hadj : G.Adj c e := by rw [← hd1, ← hd2]; exact d.adj
      have hde : (⟨(c, e), hadj⟩ : G.Dart) = d := Dart.ext _ _ (Prod.ext_iff.mpr ⟨hd1, hd2⟩).symm
      refine ⟨p.concat hadj, fun d' hd' ↦ ?_⟩
      rw [Walk.darts_concat, List.concat_eq_append, List.mem_append] at hd'
      rcases hd' with hd' | hd'
      · exact hp _ hd'
      · rw [List.mem_singleton] at hd'
        subst hd'
        rw [hde]
        exact hdP

/-- A path whose darts all satisfy `P`, extracted from a chain of `P`-darts. -/
theorem exists_isPath_darts {P : G.Dart → Prop} {a b : V}
    (h : Relation.ReflTransGen (fun x y ↦ ∃ d : G.Dart, d.fst = x ∧ d.snd = y ∧ P d) a b) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ d ∈ p.darts, P d := by
  obtain ⟨p, hp⟩ := exists_walk_darts h
  exact ⟨p.bypass, p.bypass_isPath, fun d hd ↦ hp d (p.darts_bypass_subset_darts hd)⟩

/-- Augmenting a flow along a residual path raises the excess at its start by one. -/
theorem exists_augment {a b : V} (p : G.Walk a b) :
    p.IsPath → ∀ F : Finset G.Dart, (∀ d ∈ F, d.symm ∉ F) → (∀ d ∈ p.darts, d ∉ F) →
      ∃ F' : Finset G.Dart, (∀ d ∈ F', d.symm ∉ F') ∧
        ∀ x, excess F' x = excess F x + (if a = x then 1 else 0) - (if b = x then 1 else 0) := by
  induction p with
  | nil => exact fun _ F hF _ ↦ ⟨F, hF, fun x ↦ by simp⟩
  | @cons a c b hadj q ih =>
      intro hp F hF hpF
      rw [Walk.cons_isPath_iff] at hp
      set d₀ : G.Dart := ⟨(a, c), hadj⟩ with hd₀
      have e1 : d₀.fst = a := by rw [hd₀]
      have e2 : d₀.snd = c := by rw [hd₀]
      have e3 : d₀.symm.fst = c := by rw [hd₀]; rfl
      have e4 : d₀.symm.snd = a := by rw [hd₀]; rfl
      have hmem : d₀ ∈ (Walk.cons hadj q).darts := by rw [hd₀, Walk.darts_cons]; exact .head _
      have hd₀F : d₀ ∉ F := hpF d₀ hmem
      have hqF : ∀ d ∈ q.darts, d ∉ F := fun d hd ↦
        hpF d (by rw [Walk.darts_cons]; exact .tail _ hd)
      have hne : ∀ d ∈ q.darts, d ≠ d₀ := by
        rintro d hd rfl
        exact hp.2 (e1 ▸ q.dart_fst_mem_support_of_mem_darts hd)
      obtain ⟨F₁, hF₁, hF₁exc, hF₁q⟩ :
          ∃ F₁ : Finset G.Dart, (∀ d ∈ F₁, d.symm ∉ F₁) ∧
            (∀ x, excess F₁ x = excess F x + (if a = x then 1 else 0)
              - (if c = x then 1 else 0)) ∧ (∀ d ∈ q.darts, d ∉ F₁) := by
        by_cases hsym : d₀.symm ∈ F
        · refine ⟨F.erase d₀.symm, fun d hd ↦ ?_, fun x ↦ ?_, fun d hd hc ↦ ?_⟩
          · exact fun hc ↦ hF d (Finset.mem_of_mem_erase hd) (Finset.mem_of_mem_erase hc)
          · rw [excess_erase hsym x, e3, e4]; ring
          · exact hqF d hd (Finset.mem_of_mem_erase hc)
        · refine ⟨insert d₀ F, fun d hd ↦ ?_, fun x ↦ ?_, fun d hd hc ↦ ?_⟩
          · rcases Finset.mem_insert.mp hd with rfl | hd'
            · simp only [Finset.mem_insert, not_or]
              exact ⟨Dart.symm_ne _, hsym⟩
            · simp only [Finset.mem_insert, not_or]
              exact ⟨fun hc ↦ hsym (hc ▸ hd'), hF _ hd'⟩
          · rw [excess_insert hd₀F x, e1, e2]
          · rcases Finset.mem_insert.mp hc with rfl | hc'
            · exact hne _ hd rfl
            · exact hqF d hd hc'
      obtain ⟨F', hF', hexc⟩ := ih hp.1 F₁ hF₁ hF₁q
      refine ⟨F', hF', fun x ↦ ?_⟩
      rw [hexc x, hF₁exc x]
      ring

/-- Deleting the darts of a path from a flow lowers the excess at its start by one. -/
theorem exists_remove {a b : V} (p : G.Walk a b) :
    p.IsPath → ∀ F : Finset G.Dart, (∀ d ∈ p.darts, d ∈ F) →
      ∃ F' : Finset G.Dart, F' ⊆ F ∧ (∀ d ∈ p.darts, d ∉ F') ∧
        ∀ x, excess F' x = excess F x - (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
  induction p with
  | nil => exact fun _ F _ ↦ ⟨F, le_rfl, by simp, fun x ↦ by simp⟩
  | @cons a c b hadj q ih =>
      intro hp F hpF
      rw [Walk.cons_isPath_iff] at hp
      set d₀ : G.Dart := ⟨(a, c), hadj⟩ with hd₀
      have e1 : d₀.fst = a := by rw [hd₀]
      have e2 : d₀.snd = c := by rw [hd₀]
      have hmem : d₀ ∈ (Walk.cons hadj q).darts := by rw [hd₀, Walk.darts_cons]; exact .head _
      have hd₀F : d₀ ∈ F := hpF d₀ hmem
      have hne : ∀ d ∈ q.darts, d ≠ d₀ := by
        rintro d hd rfl
        exact hp.2 (e1 ▸ q.dart_fst_mem_support_of_mem_darts hd)
      have hq : ∀ d ∈ q.darts, d ∈ F.erase d₀ := fun d hd ↦
        Finset.mem_erase.mpr ⟨hne d hd, hpF d (by rw [Walk.darts_cons]; exact .tail _ hd)⟩
      obtain ⟨F', hsub, hout, hexc⟩ := ih hp.1 (F.erase d₀) hq
      refine ⟨F', hsub.trans (Finset.erase_subset _ _), fun d hd ↦ ?_, fun x ↦ ?_⟩
      · rw [Walk.darts_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact fun hc ↦ (Finset.notMem_erase d₀ F) (hsub hc)
        · exact hout d hd
      · rw [hexc x, excess_erase hd₀F x, e1, e2]
        ring

/-- Summing the excess over a set of vertices counts the darts crossing its boundary. -/
theorem sum_excess (F : Finset G.Dart) (R : Finset V) :
    ∑ x ∈ R, excess F x =
      ((F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∉ R).card : ℤ) -
        ((F.filter fun d ↦ d.fst ∉ R ∧ d.snd ∈ R).card : ℤ) := by
  have hout : ∑ x ∈ R, outDegree F x = (F.filter fun d ↦ d.fst ∈ R).card := by
    have hmaps : Set.MapsTo (fun d : G.Dart ↦ d.fst) ↑(F.filter fun d ↦ d.fst ∈ R) ↑R :=
      fun d hd ↦ Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    unfold outDegree
    congr 1
    rw [Finset.filter_filter]
    exact (Finset.filter_congr fun d _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hx, h⟩⟩).symm
  have hin : ∑ x ∈ R, inDegree F x = (F.filter fun d ↦ d.snd ∈ R).card := by
    have hmaps : Set.MapsTo (fun d : G.Dart ↦ d.snd) ↑(F.filter fun d ↦ d.snd ∈ R) ↑R :=
      fun d hd ↦ Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    unfold inDegree
    congr 1
    rw [Finset.filter_filter]
    exact (Finset.filter_congr fun d _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hx, h⟩⟩).symm
  have h1 : (F.filter fun d ↦ d.fst ∈ R).card
      = (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∈ R).card
        + (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∉ R).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := F.filter fun d ↦ d.fst ∈ R)
      (p := fun d ↦ d.snd ∈ R), Finset.filter_filter, Finset.filter_filter]
  have h2 : (F.filter fun d ↦ d.snd ∈ R).card
      = (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∈ R).card
        + (F.filter fun d ↦ d.fst ∉ R ∧ d.snd ∈ R).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := F.filter fun d ↦ d.snd ∈ R)
      (p := fun d ↦ d.fst ∈ R), Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact congrArg Finset.card (Finset.filter_congr fun d _ ↦ and_comm)
    · exact congrArg Finset.card (Finset.filter_congr fun d _ ↦ and_comm)
  simp only [excess, Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum, hout, hin, h1, h2]
  push_cast
  ring

/-- A flow of excess at least `n` at `u` carries `n` pairwise edge-disjoint `u`–`v` walks. -/
theorem exists_edgeDisjoint_walks [Fintype V] {u v : V} (huv : u ≠ v) :
    ∀ (n : ℕ) (F : Finset G.Dart), (∀ d ∈ F, d.symm ∉ F) →
      (∀ x, x ≠ u → x ≠ v → excess F x = 0) → (n : ℤ) ≤ excess F u →
        ∃ q : Fin n → G.Walk u v, (∀ i, ∀ d ∈ (q i).darts, d ∈ F) ∧
          ∀ i j, i ≠ j → ∀ e ∈ (q i).edges, e ∉ (q j).edges := by
  intro n
  induction n with
  | zero => exact fun F _ _ _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
      intro F hFanti hFcons hval
      have hreach : Relation.ReflTransGen
          (fun x y ↦ ∃ d : G.Dart, d.fst = x ∧ d.snd = y ∧ d ∈ F) u v := by
        by_contra hcon
        classical
        set R : Finset V := Finset.univ.filter
          (fun x ↦ Relation.ReflTransGen
            (fun x y ↦ ∃ d : G.Dart, d.fst = x ∧ d.snd = y ∧ d ∈ F) u x) with hR
        have huR : u ∈ R := by
          simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Relation.ReflTransGen.refl
        have hvR : v ∉ R := by simpa [hR] using hcon
        have hclosed : (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∉ R) = ∅ := by
          ext d
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hdF hfst hsnd
          simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hfst hsnd
          exact hsnd (hfst.tail ⟨d, rfl, rfl, hdF⟩)
        have hsum := sum_excess F R
        rw [hclosed] at hsum
        have hsingle : ∑ x ∈ R, excess F x = excess F u :=
          Finset.sum_eq_single_of_mem u huR fun x hx hne ↦
            hFcons x hne fun hc ↦ hvR (hc ▸ hx)
        rw [hsingle] at hsum
        simp only [Finset.card_empty, Nat.cast_zero, zero_sub] at hsum
        have : (0 : ℤ) ≤ ((F.filter fun d ↦ d.fst ∉ R ∧ d.snd ∈ R).card : ℤ) := Int.natCast_nonneg _
        push_cast at hval
        omega
      obtain ⟨p, hp, hpd⟩ := exists_isPath_darts hreach
      obtain ⟨F', hsub, hout, hexc⟩ := exists_remove p hp F hpd
      have hF'anti : ∀ d ∈ F', d.symm ∉ F' := fun d hd hc ↦ hFanti d (hsub hd) (hsub hc)
      have hF'cons : ∀ x, x ≠ u → x ≠ v → excess F' x = 0 := by
        intro x hxu hxv
        rw [hexc x, hFcons x hxu hxv]
        simp [Ne.symm hxu, Ne.symm hxv]
      have hF'val : (n : ℤ) ≤ excess F' u := by
        have h0 : excess F' u = excess F u - 1 := by
          rw [hexc u]
          simp [Ne.symm huv]
        push_cast at hval
        omega
      obtain ⟨q', hq'1, hq'2⟩ := ih F' hF'anti hF'cons hF'val
      have hdisj : ∀ w : G.Walk u v, (∀ d ∈ w.darts, d ∈ F') → ∀ e ∈ p.edges, e ∉ w.edges := by
        intro w hw e hep hew
        rw [Walk.edges_eq_map_darts, List.mem_map] at hep hew
        obtain ⟨d, hd, rfl⟩ := hep
        obtain ⟨d', hd', hdd'⟩ := hew
        rcases (dart_edge_eq_iff d' d).mp hdd' with rfl | rfl
        · exact hout d' hd (hw d' hd')
        · exact hFanti d (hpd d hd) (hsub (hw d.symm hd'))
      refine ⟨Fin.cons p q', ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => simpa using hpd
        | succ i => simpa using fun d hd ↦ hsub (hq'1 i d hd)
      · intro i
        induction i using Fin.cases with
        | zero =>
            intro j
            induction j using Fin.cases with
            | zero => exact fun h ↦ absurd rfl h
            | succ j => exact fun _ ↦ by simpa using hdisj (q' j) (hq'1 j)
        | succ i =>
            intro j
            induction j using Fin.cases with
            | zero =>
                intro _ e he hc
                simp only [Fin.cons_zero, Fin.cons_succ] at he hc
                exact hdisj (q' i) (hq'1 i) e hc he
            | succ j =>
                intro hij
                simp only [Fin.cons_succ]
                exact hq'2 i j fun h ↦ hij (by rw [h])

end Flow

/-- Edge-disjoint paths survive the deletion of fewer than `k` edges: the easy half of
Menger's theorem. -/
theorem isEdgeReachable_of_edgeDisjointPaths {u v : V} {k : ℕ}
    (h : EdgeDisjointPaths G u v k) : G.IsEdgeReachable k u v := by
  classical
  obtain ⟨p, _, hdisj⟩ := h
  intro s hs
  have hfin : s.Finite := Set.finite_of_encard_le_coe (le_of_lt hs)
  by_contra hcon
  have hmeet : ∀ i : Fin k, ∃ e ∈ (p i).edges, e ∈ s := by
    intro i
    by_contra hc
    exact hcon ((p i).toDeleteEdges s fun e he hes ↦ hc ⟨e, he, hes⟩).reachable
  choose e he1 he2 using hmeet
  have hle : (Finset.univ : Finset (Fin k)).card ≤ hfin.toFinset.card := by
    refine Finset.card_le_card_of_injOn e (fun i _ ↦ hfin.mem_toFinset.mpr (he2 i)) ?_
    intro i _ j _ hij
    by_contra hne
    exact hdisj i j hne (e i) (he1 i) (hij ▸ he1 j)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  rw [hfin.encard_eq_coe_toFinset_card] at hs
  exact absurd (by exact_mod_cast hs) (not_lt.mpr hle)

/-- Menger's theorem, edge form: if `u` and `v` survive the deletion of any `k - 1` edges then
there are `k` pairwise edge-disjoint `u`–`v` paths. -/
theorem edgeDisjointPaths_of_isEdgeReachable [Fintype V] [DecidableRel G.Adj] {u v : V}
    (huv : u ≠ v) {k : ℕ} (h : G.IsEdgeReachable k u v) : EdgeDisjointPaths G u v k := by
  classical
  set 𝓕 : Finset (Finset G.Dart) := Finset.univ.filter
    (fun F ↦ (∀ d ∈ F, d.symm ∉ F) ∧ ∀ x, x ≠ u → x ≠ v → excess F x = 0) with h𝓕
  have hne : 𝓕.Nonempty := ⟨∅, by simp [h𝓕]⟩
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image 𝓕 (fun F ↦ excess F u) hne
  rw [h𝓕, Finset.mem_filter] at hFmem
  obtain ⟨-, hFanti, hFcons⟩ := hFmem
  have hkey : (k : ℤ) ≤ excess F u := by
    by_contra hlt
    rw [not_le] at hlt
    set R : Finset V := Finset.univ.filter
      (fun x ↦ Relation.ReflTransGen
        (fun x y ↦ ∃ d : G.Dart, d.fst = x ∧ d.snd = y ∧ d ∉ F) u x) with hR
    have huR : u ∈ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    have hvR : v ∉ R := by
      intro hv
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨q, hq, hqd⟩ := exists_isPath_darts hv
      obtain ⟨F', hF'anti, hF'exc⟩ := exists_augment q hq F hFanti hqd
      have hF'mem : F' ∈ 𝓕 := by
        rw [h𝓕, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hF'anti, fun x hxu hxv ↦ ?_⟩
        rw [hF'exc x, hFcons x hxu hxv]
        simp [Ne.symm hxu, Ne.symm hxv]
      have h0 : excess F' u = excess F u + 1 := by
        rw [hF'exc u]
        simp [Ne.symm huv]
      have hmax := hFmax F' hF'mem
      rw [h0] at hmax
      omega
    have hcross : ∀ (x y : V) (hxy : G.Adj x y), x ∈ R → y ∉ R →
        (⟨(x, y), hxy⟩ : G.Dart) ∈ F := by
      intro x y hxy hx hy
      by_contra hc
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hy (hx.tail ⟨⟨(x, y), hxy⟩, rfl, rfl, hc⟩)
    have hnoin : (F.filter fun d ↦ d.fst ∉ R ∧ d.snd ∈ R) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hdF hfst hsnd
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hfst hsnd
      exact hfst (hsnd.tail ⟨d.symm, rfl, rfl, hFanti d hdF⟩)
    have hsum := sum_excess F R
    rw [hnoin] at hsum
    have hsingle : ∑ x ∈ R, excess F x = excess F u :=
      Finset.sum_eq_single_of_mem u huR fun x hx hne ↦ hFcons x hne fun hc ↦ hvR (hc ▸ hx)
    rw [hsingle] at hsum
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero] at hsum
    set S : Finset (Sym2 V) := (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∉ R).image Dart.edge with hS
    have hScard : (S.card : ℤ) < k := by
      have hle : S.card ≤ (F.filter fun d ↦ d.fst ∈ R ∧ d.snd ∉ R).card := by
        rw [hS]; exact Finset.card_image_le
      have : (S.card : ℤ) ≤ excess F u := by rw [hsum]; exact_mod_cast hle
      omega
    obtain ⟨w⟩ := h (s := (↑S : Set (Sym2 V)))
      (by rw [Set.encard_coe_eq_coe_finsetCard]; exact_mod_cast hScard)
    have key : ∀ {x y : V}, (G.deleteEdges (↑S : Set (Sym2 V))).Walk x y → x ∈ R → y ∈ R := by
      intro x y w
      induction w with
      | nil => exact id
      | @cons x c y hadj q ihw =>
          intro hx
          refine ihw ?_
          by_contra hc
          rw [deleteEdges_adj] at hadj
          refine hadj.2 (Finset.mem_coe.mpr ?_)
          rw [hS]
          exact Finset.mem_image.mpr ⟨⟨(x, c), hadj.1⟩,
            Finset.mem_filter.mpr ⟨hcross x c hadj.1 hx hc, hx, hc⟩, rfl⟩
    exact hvR (key w huR)
  obtain ⟨q, _, hq2⟩ := exists_edgeDisjoint_walks huv k F hFanti hFcons hkey
  refine ⟨fun i ↦ (q i).bypass, fun i ↦ (q i).bypass_isPath, fun i j hij e he hc ↦ ?_⟩
  exact hq2 i j hij e ((q i).edges_bypass_subset_edges he) ((q j).edges_bypass_subset_edges hc)

/-- `HasEdgeRails G m` is exactly the existence of two distinct `m`-edge-reachable vertices. -/
theorem hasEdgeRails_iff_exists_isEdgeReachable [Fintype V] [DecidableRel G.Adj] (m : ℕ) :
    HasEdgeRails G m ↔ ∃ u v, u ≠ v ∧ G.IsEdgeReachable m u v := by
  constructor
  · rintro ⟨u, v, huv, p, hp, hd⟩
    exact ⟨u, v, huv, isEdgeReachable_of_edgeDisjointPaths ⟨p, hp, hd⟩⟩
  · rintro ⟨u, v, huv, h⟩
    obtain ⟨p, hp, hd⟩ := edgeDisjointPaths_of_isEdgeReachable huv h
    exact ⟨u, v, huv, p, hp, hd⟩

end Erdos915
