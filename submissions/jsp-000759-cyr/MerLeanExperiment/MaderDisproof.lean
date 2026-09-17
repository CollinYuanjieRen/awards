import MerLeanExperiment.CounterexampleFive

/-!
# Mader's counterexamples: the vertex-disjoint Bollobás–Erdős conjecture fails for all `m ≥ 5`

Mader (1973), p. 228–229, disproves the Bollobás–Erdős assertion in its internally
vertex-disjoint reading for every `m ≥ 5`.  This file transcribes his construction in the
shape that makes the counts come out *exactly* on the conjectured values, so that no padding
or edge deletion is needed.

## The graph

Write `m = k + 3` with `k ≥ 3`.  A *block* is `K_{k+2}` with a star removed: `StarBlock s r`
has a centre, `s` leaves (not joined to the centre) and `r` further vertices, everything else
being joined.  The graph `maderGraph k` has

* an apex `A`, joined to every vertex except the two blocking vertices;
* two blocking vertices `x₀, x₁`, joined to each other and to all clique vertices;
* a clique `H = {h₀, …, h_{k-1}}` on `k` vertices;
* for each `i` a *gadget* `StarBlock 1 k` (that is `K_{k+2}` minus one edge), whose two
  *ports* (its centre and its unique leaf) are joined to `h i`; like every non-blocking vertex,
  all gadget vertices are also joined to the apex `A`, and to nothing else outside the gadget;
* one *padding* block `StarBlock (k-3) 4`, i.e. `K_{k+2}` minus a star with `k - 3` edges.

Counting gives `|V| = k² + 4k + 5 = 1 + n(m-1)` and `|E| = (k³ + 7k² + 16k + 14)/2 =
1 + n·C(m,2)` with `n = m - 1 = k + 2`, which are exactly the Bollobás–Erdős values.

## Why there is no `m`-rail

Only the apex (degree `k² + 4k + 2`) and the clique vertices (degree `k + 4 = m + 1`) have
degree `≥ m`; every other vertex has degree at most `k + 2 = m - 1`, so by
`card_le_degree_of_rails` both endpoints of an `m`-rail lie in `{A} ∪ H`.  For each such pair
there is a separator of `m - 2` vertices meeting the interior of every connecting path of
length `≥ 2`:

* `h i, h j` (`i ≠ j`) are separated by `(H \ {h i, h j}) ∪ {x₀, x₁, A}`, because the only
  neighbours of `h i` outside it lie in the `i`-th gadget, which is attached to the rest of
  the graph only through `h i` and `A`;
* `h i` and `A` are separated by `(H \ {h i}) ∪ {ports of gadget i}`, because the blocking
  vertices `x₀, x₁` are *not* joined to `A` and lead back only into `H`.

`card_le_of_hitting_set` then bounds the size of any internally disjoint family by
`(m - 2) + 1 = m - 1`.

The case `m = 5` is the Sørensen–Thomassen witness of `MerLeanExperiment.CounterexampleFive`
(for `m = 5` the surplus of Mader's family vanishes).  The generic lemmas
`card_le_degree_of_rails`, `card_le_of_hitting_set` and `length_le_one_or_interior_mem` are
reused from that file.
-/

namespace Erdos915

open SimpleGraph Finset

/-- Rails in a subgraph are rails in the ambient graph (closure lemma L1): deleting edges
never creates internally disjoint paths. -/
theorem hasVertexRails_mono_of_le {V : Type*} {G H : SimpleGraph V} (hle : H ≤ G) {m : ℕ}
    (h : HasVertexRails H m) : HasVertexRails G m := by
  obtain ⟨u, v, huv, p, hinj, hpath, hdisj⟩ := h
  have hid : Function.Injective (SimpleGraph.Hom.ofLE hle) := fun a b hab ↦ hab
  refine ⟨u, v, huv, fun i ↦ (p i).mapLe hle, fun i j hij ↦ ?_,
    fun i ↦ (hpath i).mapLe hle, fun i j hij w hw hw' ↦ ?_⟩
  · exact hinj (SimpleGraph.Walk.map_injective_of_injective hid u v hij)
  · refine hdisj i j hij w ?_ ?_
    · simpa [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.support_map] using hw
    · simpa [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.support_map] using hw'

/-- Vertices of the block `K_{1+s+r}` minus the star joining the centre `none` to the `s`
leaves `some (Sum.inl j)`; the remaining `r` vertices are `some (Sum.inr j)`. -/
abbrev StarBlock (s r : ℕ) : Type := Option (Fin s ⊕ Fin r)

/-- Adjacency inside a star block: all pairs of distinct vertices except centre–leaf. -/
def starAdj {s r : ℕ} : StarBlock s r → StarBlock s r → Bool
  | none, none => false
  | none, some (Sum.inl _) => false
  | none, some (Sum.inr _) => true
  | some (Sum.inl _), none => false
  | some (Sum.inr _), none => true
  | some a, some b => decide (a ≠ b)

/-- The *ports* of a star block are its centre and its leaves. -/
def isPort {s r : ℕ} : StarBlock s r → Bool
  | some (Sum.inr _) => false
  | _ => true

/-- `starAdj` is symmetric. -/
theorem starAdj_comm {s r : ℕ} (u v : StarBlock s r) : starAdj u v = starAdj v u := by
  rcases u with _ | (a | a) <;> rcases v with _ | (b | b) <;>
    simp [starAdj, ne_comm]

/-- `starAdj` is irreflexive. -/
theorem starAdj_irrefl {s r : ℕ} (u : StarBlock s r) : starAdj u u = false := by
  rcases u with _ | (a | a) <;> simp [starAdj]

/-- The vertex type of Mader's graph with parameter `k` (so `m = k + 3`): an apex, two
blocking vertices, `k` clique vertices each carrying a gadget block, and one padding block. -/
abbrev MVertex (k : ℕ) : Type :=
  Option (Fin 2) ⊕ (Fin k × Option (StarBlock 1 k)) ⊕ StarBlock (k - 3) 4

namespace MVertex

/-- The apex vertex. -/
abbrev apex {k : ℕ} : MVertex k := Sum.inl none

/-- The two blocking vertices, adjacent to each other and to all clique vertices. -/
abbrev xv {k : ℕ} (a : Fin 2) : MVertex k := Sum.inl (some a)

/-- The `i`-th clique vertex. -/
abbrev hv {k : ℕ} (i : Fin k) : MVertex k := Sum.inr (Sum.inl (i, none))

/-- The vertex `u` of the gadget block hanging at the `i`-th clique vertex. -/
abbrev gv {k : ℕ} (i : Fin k) (u : StarBlock 1 k) : MVertex k := Sum.inr (Sum.inl (i, some u))

/-- The vertex `u` of the padding block. -/
abbrev pv {k : ℕ} (u : StarBlock (k - 3) 4) : MVertex k := Sum.inr (Sum.inr u)

end MVertex

open MVertex

/-- Adjacency of Mader's graph. -/
def mAdj (k : ℕ) : MVertex k → MVertex k → Bool
  | Sum.inl none, Sum.inl _ => false
  | Sum.inl (some _), Sum.inl none => false
  | Sum.inl (some a), Sum.inl (some b) => decide (a ≠ b)
  | Sum.inl none, Sum.inr (Sum.inl _) => true
  | Sum.inl (some _), Sum.inr (Sum.inl (_, none)) => true
  | Sum.inl (some _), Sum.inr (Sum.inl (_, some _)) => false
  | Sum.inl none, Sum.inr (Sum.inr _) => true
  | Sum.inl (some _), Sum.inr (Sum.inr _) => false
  | Sum.inr (Sum.inl _), Sum.inl none => true
  | Sum.inr (Sum.inl (_, none)), Sum.inl (some _) => true
  | Sum.inr (Sum.inl (_, some _)), Sum.inl (some _) => false
  | Sum.inr (Sum.inr _), Sum.inl none => true
  | Sum.inr (Sum.inr _), Sum.inl (some _) => false
  | Sum.inr (Sum.inl (i, none)), Sum.inr (Sum.inl (j, none)) => decide (i ≠ j)
  | Sum.inr (Sum.inl (i, none)), Sum.inr (Sum.inl (j, some u)) => decide (i = j) && isPort u
  | Sum.inr (Sum.inl (i, some u)), Sum.inr (Sum.inl (j, none)) => decide (i = j) && isPort u
  | Sum.inr (Sum.inl (i, some u)), Sum.inr (Sum.inl (j, some v)) => decide (i = j) && starAdj u v
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => false
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr u), Sum.inr (Sum.inr v) => starAdj u v

/-- `mAdj` is symmetric. -/
theorem mAdj_comm {k : ℕ} (v w : MVertex k) : mAdj k v w = mAdj k w v := by
  rcases v with (_ | a) | (⟨i, _ | u⟩ | u) <;> rcases w with (_ | b) | (⟨j, _ | t⟩ | t) <;>
    simp [mAdj, starAdj_comm, eq_comm]

/-- `mAdj` is irreflexive. -/
theorem mAdj_irrefl {k : ℕ} (v : MVertex k) : mAdj k v v = false := by
  rcases v with (_ | a) | (⟨i, _ | u⟩ | u) <;> simp [mAdj, starAdj_irrefl]

/-- Mader's graph with parameter `k`; the rail parameter is `m = k + 3`. -/
def maderGraph (k : ℕ) : SimpleGraph (MVertex k) where
  Adj v w := mAdj k v w
  symm := ⟨fun v w h ↦ by simpa [mAdj_comm w v] using h⟩
  loopless := ⟨fun v h ↦ by simp [mAdj_irrefl v] at h⟩

/-- Adjacency in `maderGraph k` is decidable. -/
instance maderGraph_decidableAdj (k : ℕ) : DecidableRel (maderGraph k).Adj := fun v w ↦
  inferInstanceAs (Decidable (mAdj k v w = true))

/-- Adjacency in `maderGraph` is `mAdj`. -/
@[simp] theorem maderGraph_adj {k : ℕ} (v w : MVertex k) :
    (maderGraph k).Adj v w ↔ mAdj k v w = true := Iff.rfl

/-- The number of vertices of `maderGraph k`. -/
theorem card_mVertex {k : ℕ} (hk : 3 ≤ k) : Fintype.card (MVertex k) = k * k + 4 * k + 5 := by
  simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  cases Nat.exists_eq_add_of_le hk with
  | intro c hc => subst hc; ring_nf; omega

/-- Degrees in `maderGraph` computed as a sum of indicators. -/
theorem degree_eq_sum {k : ℕ} (v : MVertex k) :
    (maderGraph k).degree v = ∑ w : MVertex k, if mAdj k v w = true then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]
  rfl

/-- Counting the elements of a fintype different from a given one. -/
theorem sum_ite_ne_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, (if a ≠ x then 1 else 0) = Fintype.card α - 1 := by
  rw [← Finset.card_filter, Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ]

/-- Counting the elements of a fintype different from a given one, as a `0`/`1` sum. -/
theorem sum_ite_eq_zero {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, (if a = x then 0 else 1) = Fintype.card α - 1 := by
  rw [← sum_ite_ne_one a]
  exact Finset.sum_congr rfl fun x _ ↦ by split <;> simp_all

/-- Counting the elements of a fintype equal to a given one. -/
theorem sum_ite_eq_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, (if a = x then 1 else 0) = 1 := by
  simp

/-- The degree of the apex. -/
theorem degree_apex {k : ℕ} (hk : 3 ≤ k) :
    (maderGraph k).degree (apex : MVertex k) = k * k + 4 * k + 2 := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj]
  have h3 : k - 3 + 4 = k + 1 := by omega
  simp [h3]
  ring

/-- The degree of a blocking vertex. -/
theorem degree_xv {k : ℕ} (a : Fin 2) : (maderGraph k).degree (xv a) = k + 1 := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj]
  fin_cases a <;> simp <;> omega

/-- The degree of a clique vertex. -/
theorem degree_hv {k : ℕ} (i : Fin k) : (maderGraph k).degree (hv i) = k + 4 := by
  rw [degree_eq_sum]
  have hk : 0 < k := i.pos
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort]
  simp [Finset.sum_add_distrib, sum_ite_eq_zero]
  omega

/-- The degree of a gadget vertex. -/
theorem degree_gv {k : ℕ} (i : Fin k) (u : StarBlock 1 k) :
    (maderGraph k).degree (gv i u) = k + 2 := by
  have hk : 0 < k := i.pos
  rw [degree_eq_sum]
  have hj : ∀ j : Fin 1, j = 0 := fun j ↦ Subsingleton.elim _ _
  rcases u with _ | (j | j)
  · simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
      starAdj, Bool.and_eq_true, decide_eq_true_eq, ite_and, 
      ite_true]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
    omega
  · rw [hj j]
    simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
      starAdj, Bool.and_eq_true, decide_eq_true_eq, ite_and, 
      ite_true]
    simp [Finset.sum_add_distrib]
    omega
  · simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
      starAdj, Bool.and_eq_true, decide_eq_true_eq, ite_and, 
      ite_true]
    simp [Finset.sum_add_distrib, sum_ite_eq_zero]
    omega

/-- The degree of the centre of the padding block. -/
theorem degree_pv_centre {k : ℕ} :
    (maderGraph k).degree (pv (none : StarBlock (k - 3) 4)) = 5 := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
    starAdj]
  simp

/-- The degree of a leaf of the padding block. -/
theorem degree_pv_leaf {k : ℕ} (hk : 3 ≤ k) (j : Fin (k - 3)) :
    (maderGraph k).degree (pv (some (Sum.inl j) : StarBlock (k - 3) 4)) = k + 1 := by
  have hpos : 0 < k - 3 := j.pos
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
    starAdj]
  simp [sum_ite_eq_zero]
  omega

/-- The degree of a non-leaf, non-centre vertex of the padding block. -/
theorem degree_pv_other {k : ℕ} (hk : 3 ≤ k) (j : Fin 4) :
    (maderGraph k).degree (pv (some (Sum.inr j) : StarBlock (k - 3) 4)) = k + 2 := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, mAdj, isPort,
    starAdj]
  simp [sum_ite_eq_zero]
  omega

/-- The degree sum of `maderGraph k`. -/
theorem sum_degrees {k : ℕ} (hk : 3 ≤ k) :
    ∑ v : MVertex k, (maderGraph k).degree v = k ^ 3 + 7 * k ^ 2 + 16 * k + 14 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [degree_apex hk, degree_xv, degree_hv, degree_gv, degree_pv_centre,
    degree_pv_leaf hk, degree_pv_other hk]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, 
    smul_eq_mul]
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 3 := ⟨k - 3, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-! ## Separators -/

/-- The separator cutting two distinct clique vertices apart. -/
def sepHH {k : ℕ} (i j : Fin k) : Finset (MVertex k) :=
  insert apex (insert (xv 0) (insert (xv 1)
    (((Finset.univ.erase i).erase j).image (fun l ↦ (hv l : MVertex k)))))

/-- The separator cutting a clique vertex from the apex. -/
def sepHA {k : ℕ} (i : Fin k) : Finset (MVertex k) :=
  insert (gv i none) (insert (gv i (some (Sum.inl 0)))
    ((Finset.univ.erase i).image (fun l ↦ (hv l : MVertex k))))

/-- Membership in `sepHH`. -/
theorem mem_sepHH {k : ℕ} {i j : Fin k} {w : MVertex k} :
    w ∈ sepHH i j ↔
      w = apex ∨ w = xv 0 ∨ w = xv 1 ∨ ∃ l, l ≠ i ∧ l ≠ j ∧ w = hv l := by
  simp only [sepHH, Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
    and_true]
  constructor
  · rintro (h | h | h | ⟨l, ⟨hl1, hl2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨l, hl2, hl1, rfl⟩))
  · rintro (h | h | h | ⟨l, hl1, hl2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨l, ⟨hl2, hl1⟩, rfl⟩))

/-- Membership in `sepHA`. -/
theorem mem_sepHA {k : ℕ} {i : Fin k} {w : MVertex k} :
    w ∈ sepHA i ↔
      w = gv i none ∨ w = gv i (some (Sum.inl 0)) ∨ ∃ l, l ≠ i ∧ w = hv l := by
  simp only [sepHA, Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
    and_true]
  constructor
  · rintro (h | h | ⟨l, hl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l, hl, rfl⟩)
  · rintro (h | h | ⟨l, hl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l, hl, rfl⟩)

/-- `sepHH` has at most `k + 1` elements. -/
theorem card_sepHH {k : ℕ} {i j : Fin k} (hij : i ≠ j) : (sepHH i j).card ≤ k + 1 := by
  have himg : (((Finset.univ.erase i).erase j).image
      (fun l ↦ (hv l : MVertex k))).card ≤ k - 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hk : 2 ≤ k := by
    have h1 : 1 < Fintype.card (Fin k) := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨i, j, hij⟩⟩
    rw [Fintype.card_fin] at h1
    omega
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Finset.card_insert_le _ _) 1) 1) ?_
  omega

/-- `sepHA` has at most `k + 1` elements. -/
theorem card_sepHA {k : ℕ} (i : Fin k) : (sepHA i).card ≤ k + 1 := by
  have himg : ((Finset.univ.erase i).image (fun l ↦ (hv l : MVertex k))).card ≤ k - 1 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hk : 1 ≤ k := i.pos
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
  omega

/-- The two-colouring separating the `j`-th clique vertex and its gadget from the rest. -/
def sideHH {k : ℕ} (j : Fin k) : MVertex k → Bool
  | Sum.inr (Sum.inl (l, _)) => decide (l = j)
  | _ => false

/-- The two-colouring separating the `i`-th clique vertex and the blocking vertices from the
apex side. -/
def sideHA {k : ℕ} (i : Fin k) : MVertex k → Bool
  | Sum.inl none => false
  | Sum.inl (some _) => true
  | Sum.inr (Sum.inl (l, none)) => decide (l = i)
  | Sum.inr (Sum.inl (_, some _)) => false
  | Sum.inr (Sum.inr _) => false

/-- The cut condition for `sepHH`. -/
theorem cut_sepHH {k : ℕ} {i j : Fin k} (x y : MVertex k)
    (hadj : (maderGraph k).Adj x y) (hx : x ∉ sepHH i j) (hy : y ∉ sepHH i j)
    (hne : s(x, y) ≠ s((hv i : MVertex k), hv j)) : sideHH j x = sideHH j y := by
  simp only [mem_sepHH, not_or, not_exists, not_and] at hx hy
  rcases x with (_ | a) | (⟨a, _ | u⟩ | u) <;> rcases y with (_ | b) | (⟨b, _ | t⟩ | t) <;>
    simp_all [sideHH, mAdj]
  · fin_cases a <;> simp_all
  · fin_cases b <;> simp_all
  · have ha : a = i ∨ a = j := by
      by_contra h
      push Not at h
      exact hx a h.1 h.2 rfl
    have hb : b = i ∨ b = j := by
      by_contra h
      push Not at h
      exact hy b h.1 h.2 rfl
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- The ports of a gadget block are its centre and its unique leaf. -/
theorem isPort_cases {k : ℕ} (u : StarBlock 1 k) (h : isPort u = true) :
    u = none ∨ u = some (Sum.inl 0) := by
  rcases u with _ | (c | c)
  · exact Or.inl rfl
  · exact Or.inr (by rw [Subsingleton.elim c 0])
  · simp [isPort] at h

/-- The cut condition for `sepHA`. -/
theorem cut_sepHA {k : ℕ} {i : Fin k} (x y : MVertex k)
    (hadj : (maderGraph k).Adj x y) (hx : x ∉ sepHA i) (hy : y ∉ sepHA i)
    (hne : s(x, y) ≠ s((hv i : MVertex k), apex)) : sideHA i x = sideHA i y := by
  have hone : ∀ c : Fin 1, c = 0 := fun c ↦ Subsingleton.elim _ _
  revert hadj hx hy hne
  rcases x with (_ | a) | (⟨a, _ | (_ | (c | c))⟩ | u) <;>
    rcases y with (_ | b) | (⟨b, _ | (_ | (d | d))⟩ | t) <;>
    simp [mem_sepHA, sideHA, mAdj, isPort, starAdj, hone] <;> (try intros) <;> simp_all

/-! ## No `m`-rails -/

/-- Every vertex other than the apex and the clique vertices has degree at most `m - 1`. -/
theorem degree_lt {k : ℕ} (hk : 3 ≤ k) {v : MVertex k} (h1 : v ≠ apex)
    (h2 : ∀ i, v ≠ hv i) : (maderGraph k).degree v < k + 3 := by
  rcases v with (_ | a) | (⟨a, _ | u⟩ | u)
  · exact absurd rfl h1
  · rw [degree_xv]; omega
  · exact absurd rfl (h2 a)
  · rw [degree_gv]; omega
  · rcases u with _ | (j | j)
    · rw [degree_pv_centre]; omega
    · rw [degree_pv_leaf hk]; omega
    · rw [degree_pv_other hk]; omega

/-- A separator of at most `m - 2` vertices rules out an `m`-rail. -/
theorem no_rails_of_separator {k : ℕ} {u v : MVertex k} (S : Finset (MVertex k))
    (side : MVertex k → Bool) (hcard : S.card ≤ k + 1) (hu : u ∉ S) (hv : v ∉ S)
    (hside : side u ≠ side v)
    (hcut : ∀ x y : MVertex k, (maderGraph k).Adj x y → x ∉ S → y ∉ S →
      s(x, y) ≠ s(u, v) → side x = side y)
    (p : Fin (k + 3) → (maderGraph k).Walk u v) (hinj : Function.Injective p)
    (hpath : ∀ i, (p i).IsPath)
    (hdisj : ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j)) : False := by
  have h := card_le_of_hitting_set p hinj hdisj S fun i ↦
    length_le_one_or_interior_mem S side hu hv hside hcut (hpath i)
  omega

/-- No two vertices of `maderGraph k` are joined by `k + 3` internally disjoint paths. -/
theorem maderGraph_not_hasVertexRails {k : ℕ} (hk : 3 ≤ k) :
    ¬ HasVertexRails (maderGraph k) (k + 3) := by
  rintro ⟨u, v, huv, p, hinj, hpath, hdisj⟩
  obtain ⟨hinj', hpath', hdisj'⟩ := rails_reverse p hinj hpath hdisj
  have hend : ∀ w : MVertex k, (k + 3 ≤ (maderGraph k).degree w) →
      w = apex ∨ ∃ i, w = hv i := by
    intro w hw
    by_contra h
    push Not at h
    exact absurd (degree_lt hk h.1 h.2) (by omega)
  have hu := hend u (card_le_degree_of_rails huv p hinj hpath hdisj)
  have hv := hend v (card_le_degree_of_rails huv.symm _ hinj' hpath' hdisj')
  rcases hu with rfl | ⟨i, rfl⟩ <;> rcases hv with rfl | ⟨j, rfl⟩
  · exact huv rfl
  · refine no_rails_of_separator (sepHA j) (sideHA j) (card_sepHA j) ?_ ?_ ?_
      (fun x y ↦ cut_sepHA x y) _ hinj' hpath' hdisj'
    · simp [mem_sepHA]
    · simp [mem_sepHA]
    · simp [sideHA]
  · refine no_rails_of_separator (sepHA i) (sideHA i) (card_sepHA i) ?_ ?_ ?_
      (fun x y ↦ cut_sepHA x y) _ hinj hpath hdisj
    · simp [mem_sepHA]
    · simp [mem_sepHA]
    · simp [sideHA]
  · have hij : i ≠ j := fun h ↦ huv (by rw [h])
    refine no_rails_of_separator (sepHH i j) (sideHH j) (card_sepHH hij) ?_ ?_ ?_
      (fun x y ↦ cut_sepHH x y) _ hinj hpath hdisj
    · simp [mem_sepHH]
    · simp [mem_sepHH]
    · simp [sideHH, hij]

/-! ## The counterexample for every `m ≥ 5` -/

/-- `2 * C(n, 2) = n * (n - 1)`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

/-- `maderGraph k` has exactly `1 + (k + 2) * C(k + 3, 2)` edges. -/
theorem maderGraph_card_edges {k : ℕ} (hk : 3 ≤ k) :
    (maderGraph k).edgeSet.ncard = 1 + (k + 2) * (k + 3).choose 2 := by
  have h2 : 2 * (maderGraph k).edgeFinset.card = k ^ 3 + 7 * k ^ 2 + 16 * k + 14 := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, sum_degrees hk]
  have hc : 2 * (k + 3).choose 2 = (k + 3) * (k + 2) := by
    rw [two_mul_choose_two]
    congr 1
  have key : 2 * (1 + (k + 2) * (k + 3).choose 2) = k ^ 3 + 7 * k ^ 2 + 16 * k + 14 := by
    have hmul : 2 * ((k + 2) * (k + 3).choose 2) = (k + 2) * (2 * (k + 3).choose 2) := by ring
    rw [Nat.mul_add, hmul, hc]
    ring
  have h3 : (maderGraph k).edgeSet.ncard = (maderGraph k).edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  omega

/-- The Bollobás–Erdős conjecture is false for every `m ≥ 5` (vertex-disjoint reading). -/
theorem exists_no_vertex_rails_of_ge_five {m : ℕ} (hm : 5 ≤ m) :
    ∃ (n : ℕ) (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      1 ≤ n ∧ Fintype.card V = 1 + n * (m - 1) ∧ G.edgeSet.ncard = 1 + n * m.choose 2 ∧
        ¬ HasVertexRails G m := by
  rcases eq_or_lt_of_le hm with rfl | hm6
  · exact exists_no_vertex_rails_five
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hk : 3 ≤ k := by omega
  refine ⟨k + 2, MVertex k, inferInstance, maderGraph k, by omega, ?_, ?_,
    maderGraph_not_hasVertexRails hk⟩
  · have h1 : k + 3 - 1 = k + 2 := by omega
    rw [card_mVertex hk, h1]
    ring
  · rw [maderGraph_card_edges hk]

end Erdos915
