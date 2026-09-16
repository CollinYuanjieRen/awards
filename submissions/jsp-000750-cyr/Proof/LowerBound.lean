import Proof.Defs

/-!
# Erdős Problem 902: Erdős's lower bound `2^(n+1) - 1 ≤ f n` (Erdős 1963)

Let `r` be a tournament on a finite type `V` with the `(n+1)`-domination property.  The in-degrees
`indeg v = #{u | r u v}` sum to the number of unordered pairs, so some vertex `v` has
`2 · indeg v ≤ card V - 1`.  Its in-neighbourhood `I = {u | r u v}` carries a tournament with the
`n`-domination property: an `n`-set `S ⊆ I` together with `v` is an `(n+1)`-set, dominated by some
`w`; since `w` beats `v`, `w ∈ I`.  By induction `2^(n+1) - 1 ≤ card I`, hence
`card V ≥ 2 · card I + 1 ≥ 2^(n+2) - 1`.  The base case `n = 0` only needs a vertex.
-/

open Finset

namespace Erdos902

variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]

/-- In-degree of `v`: the number of vertices beating `v`. -/
def indeg (v : V) : ℕ := (univ.filter fun u => r u v).card

/-- Out-degree of `v`: the number of vertices beaten by `v`. -/
def outdeg (v : V) : ℕ := (univ.filter fun u => r v u).card

omit [DecidableEq V] in
theorem sum_indeg_eq_sum_outdeg : ∑ v, indeg r v = ∑ v, outdeg r v := by
  simp only [indeg, outdeg, Finset.card_filter]
  exact Finset.sum_comm

theorem indeg_add_outdeg (hr : IsTournament r) (v : V) :
    indeg r v + outdeg r v = Fintype.card V - 1 := by
  have hdisj : Disjoint (univ.filter fun u => r u v) (univ.filter fun u => r v u) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun u huv hvu => hr.asymm huv hvu
  have hunion : ((univ.filter fun u => r u v) ∪ univ.filter fun u => r v u)
      = univ.erase v := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    exact ⟨fun h => h.elim (fun h => hr.ne_of_rel h) fun h => (hr.ne_of_rel h).symm,
      fun hne => hr.total hne⟩
  rw [indeg, outdeg, ← Finset.card_union_of_disjoint hdisj, hunion,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-- Some vertex has in-degree at most `(card V - 1) / 2`. -/
theorem exists_two_mul_indeg_le (hr : IsTournament r) [Nonempty V] :
    ∃ v, 2 * indeg r v ≤ Fintype.card V - 1 := by
  have hsum : ∑ v : V, 2 * indeg r v ≤ ∑ _v : V, (Fintype.card V - 1) := by
    have hrw : ∑ v : V, 2 * indeg r v = ∑ v : V, (indeg r v + outdeg r v) := by
      simp only [two_mul, Finset.sum_add_distrib, sum_indeg_eq_sum_outdeg]
    rw [hrw]
    exact Finset.sum_le_sum fun v _ => le_of_eq (indeg_add_outdeg r hr v)
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨v, hv⟩

/-- The in-neighbourhood of `v` as a subtype. -/
abbrev InNbhd (v : V) : Type _ := {u : V // r u v}

/-- The restriction of `r` to the in-neighbourhood of `v`. -/
def restrict (v : V) (a b : InNbhd r v) : Prop := r a.1 b.1

instance (v : V) : DecidableRel (restrict r v) := fun a b => inferInstanceAs (Decidable (r a.1 b.1))

omit [DecidableEq V] in
theorem card_inNbhd (v : V) : Fintype.card (InNbhd r v) = indeg r v := by
  rw [indeg, Fintype.card_subtype]

omit [Fintype V] [DecidableEq V] [DecidableRel r] in
theorem isTournament_restrict (hr : IsTournament r) (v : V) : IsTournament (restrict r v) := by
  exact ⟨fun a => hr.1 a.1, fun a b hab => hr.2 a.1 b.1 fun h => hab (Subtype.ext h)⟩

/-- Every vertex has in-degree at least `n` when the `(n+1)`-domination property holds: otherwise
the in-neighbourhood `I` of `v` together with `v` extends to an `(n+1)`-set `S`, whose dominator
beats `v`, hence lies in `I ⊆ S`, contradicting that it lies outside `S`. -/
theorem le_indeg_of_hasProperty (hr : IsTournament r) {n : ℕ} (hn : HasProperty r (n + 1))
    (v : V) : n ≤ indeg r v := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  rw [indeg] at hlt
  have hvI : v ∉ univ.filter fun u => r u v := by
    simp [hr.irrefl v]
  have hcard : (insert v (univ.filter fun u => r u v)).card ≤ n + 1 := by
    rw [Finset.card_insert_of_notMem hvI]
    omega
  have hnV : n + 1 ≤ Fintype.card V := by
    obtain ⟨S, hS⟩ := hn.1
    calc n + 1 = S.card := hS.symm
      _ ≤ Fintype.card V := Finset.card_le_univ S
  obtain ⟨S, hSsub, -, hScard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ _) hcard (by simpa using hnV)
  obtain ⟨hw1, hw2⟩ := (hn.2 S hScard).choose_spec
  have hwv : r (hn.2 S hScard).choose v :=
    hw2 v (hSsub (Finset.mem_insert_self v (univ.filter fun u => r u v)))
  exact hw1 (hSsub (Finset.mem_insert_of_mem (by simpa using hwv)))

/-- The in-neighbourhood of any vertex inherits the property with `n` lowered by one. -/
theorem hasProperty_restrict (hr : IsTournament r) {n : ℕ} (hn : HasProperty r (n + 1)) (v : V) :
    HasProperty (restrict r v) n := by
  refine ⟨?_, ?_⟩
  · have hcard : n ≤ (univ : Finset (InNbhd r v)).card := by
      rw [Finset.card_univ, card_inNbhd]
      exact le_indeg_of_hasProperty r hr hn v
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨S, hS⟩
  · intro S hS
    have hvS : v ∉ S.map (Function.Embedding.subtype fun u => r u v) := by
      intro hmem
      obtain ⟨a, -, ha⟩ := Finset.mem_map.1 hmem
      have hav : r a.1 v := a.2
      rw [show (a : V) = v from ha] at hav
      exact hr.irrefl v hav
    have hT : (insert v (S.map (Function.Embedding.subtype fun u => r u v))).card = n + 1 := by
      rw [Finset.card_insert_of_notMem hvS, Finset.card_map, hS]
    obtain ⟨w, hw1, hw2⟩ := hn.2 _ hT
    have hwv : r w v := hw2 v (Finset.mem_insert_self v _)
    refine ⟨⟨w, hwv⟩, fun hmem => hw1 (Finset.mem_insert_of_mem ?_), fun a ha => ?_⟩
    · exact Finset.mem_map_of_mem _ hmem
    · exact hw2 a.1 (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ ha))

/-- Auxiliary form of the lower bound, stated so that the induction on `n` can change the vertex
type to an in-neighbourhood. -/
private theorem two_pow_sub_one_le_card_aux (n : ℕ) : ∀ (W : Type*) [Fintype W] [DecidableEq W]
    (s : W → W → Prop) [DecidableRel s], IsTournament s → HasProperty s n →
    2 ^ (n + 1) - 1 ≤ Fintype.card W := by
  induction n with
  | zero =>
    intro W _ _ s _ _ hn
    obtain ⟨w, -⟩ := hn.2 ∅ Finset.card_empty
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨w⟩
    have hp : 2 ^ (0 + 1) - 1 = 1 := by norm_num
    omega
  | succ n ih =>
    intro W _ _ s _ hs hn
    have hne : Nonempty W := by
      obtain ⟨T, hT⟩ := hn.1
      obtain ⟨w, -⟩ := Finset.card_pos.1 (by omega : 0 < T.card)
      exact ⟨w⟩
    obtain ⟨v, hv⟩ := exists_two_mul_indeg_le s hs
    have hsub : 2 ^ (n + 1) - 1 ≤ Fintype.card (InNbhd s v) :=
      ih (InNbhd s v) (restrict s v) (isTournament_restrict s hs v)
        (hasProperty_restrict s hs hn v)
    rw [card_inNbhd] at hsub
    have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.2 hne
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
    omega

/-- **Erdős (1963).** A tournament with the `n`-domination property has at least `2^(n+1) - 1`
vertices. -/
theorem two_pow_sub_one_le_card (hr : IsTournament r) {n : ℕ} (hn : HasProperty r n) :
    2 ^ (n + 1) - 1 ≤ Fintype.card V := by
  exact two_pow_sub_one_le_card_aux n V r hr hn

end Erdos902
