import Proof.Regular

/-!
# Erdős problem #82 — `F(n) ≫ log n` from Ramsey's theorem

The problem page for Erdős problem #82 states:

> Let `F(n)` be maximal such that every graph on `n` vertices contains a regular induced
> subgraph on at least `F(n)` vertices. […] Ramsey's theorem implies that `F(n) ≫ log n`.

This file makes that implication explicit. Since a monochromatic `K_n` (a clique of `G`,
or a clique of `Gᶜ`) is a regular induced subgraph on `n` vertices, the diagonal Ramsey
bound `r(n, n) ≤ binom(2n, n) ≤ 4 ^ n` gives `G(n) ≤ 4 ^ n`, i.e.

`Erdos82.log_le_regGuarantee : Nat.log 4 m ≤ regGuarantee m`

which is the explicit form of `F(m) ≫ log m` (with the implied constant `1 / log 4`).

We also record the first values of `G` computed by Fajtlowicz, McColgan, Reid and
Staton: `G(1) = 1`, `G(2) = 2` and `G(3) = 5`, together with `F(5) = 3`. The last two
rest on `Erdos82.regProp_five_three` (every graph on five vertices has a regular induced
subgraph on at least three vertices) and on two small explicit counterexamples: the path
`P₄`, and `P₄` together with an isolated vertex.

Not claimed here: the open question of Erdős problem #82 (`F(n)/log n → ∞`), the upper bounds
`F(n) ≪ n^{1/2+o(1)}`, `n^{1/2}(log n)^{O(1)}` and `n^{1/2}`, the values `G(4) = 7`, `G(5) = 17`
and `F(7) = 4`, and the lower-bound witnesses `G(6) ≥ 21`, `G(7) ≥ 30`.
-/

namespace Erdos82

open SimpleGraph

/-- The Erdős–Szekeres bound in the lossy `RamseyProp` form: `binom(m + n, m) - 1`
vertices already force a red `K_m` or a blue `K_n`. -/
theorem ramseyProp_choose (m n : ℕ) : RamseyProp ((m + n).choose m - 1) m n := by
  have key : ∀ k m n : ℕ, m + n ≤ k → RamseyProp ((m + n).choose m - 1) m n := by
    intro k
    induction k with
    | zero =>
      intro m n h
      have hm : m = 0 := by omega
      subst hm
      simpa using ramseyProp_zero_left n
    | succ k ih =>
      intro m n h
      obtain _ | a := m
      · simpa using ramseyProp_zero_left n
      obtain _ | b := n
      · simpa using ramseyProp_zero_right (a + 1)
      have hX : 0 < (a + b + 1).choose a := Nat.choose_pos (by omega)
      have hY : 0 < (a + b + 1).choose (a + 1) := Nat.choose_pos (by omega)
      have hpascal : (a + 1 + (b + 1)).choose (a + 1)
          = (a + b + 1).choose a + (a + b + 1).choose (a + 1) := by
        have hsum : a + 1 + (b + 1) = a + b + 1 + 1 := by omega
        rw [hsum, Nat.choose_succ_succ]
      have hAeq : a + (b + 1) = a + b + 1 := by omega
      have hBeq : a + 1 + b = a + b + 1 := by omega
      have hstep : RamseyProp
          ((a + (b + 1)).choose a - 1 + ((a + 1 + b).choose (a + 1) - 1) + 1) (a + 1) (b + 1) :=
        ramseyProp_step (by omega) (by omega) (ih a (b + 1) (by omega))
          (ih (a + 1) b (by omega))
      have hnum : (a + (b + 1)).choose a - 1 + ((a + 1 + b).choose (a + 1) - 1) + 1
          = (a + 1 + (b + 1)).choose (a + 1) - 1 := by
        rw [hAeq, hBeq, hpascal]
        omega
      rwa [hnum] at hstep
  exact key (m + n) m n le_rfl

/-- Ramsey numbers are bounded by binomial coefficients: `r(m, n) ≤ C(m + n, m) - 1`. -/
theorem ramsey_le_choose (m n : ℕ) : ramsey m n ≤ (m + n).choose m - 1 :=
  ramsey_le_of_ramseyProp (ramseyProp_choose m n)

/-- The diagonal Ramsey number is at most `4 ^ n`. -/
theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n := by
  have h1 := ramsey_le_choose n n
  have h2 : Nat.centralBinom n = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  have h3 := Nat.centralBinom_le_four_pow n
  omega

/-- `G(n) ≤ r(n, n)`: a monochromatic `K_n` is a regular induced subgraph on `n`
vertices. -/
theorem regThreshold_le_ramsey (n : ℕ) : regThreshold n ≤ ramsey n n :=
  regThreshold_le_of_regProp (regProp_of_ramseyProp (ramseyProp_ramsey n n))

/-- `G(n) ≤ 4 ^ n`. -/
theorem regThreshold_le_four_pow (n : ℕ) : regThreshold n ≤ 4 ^ n :=
  (regThreshold_le_ramsey n).trans (ramsey_diag_le_four_pow n)

/-- Every graph on `m` vertices has a regular induced subgraph on at least
`log₄ m` vertices. -/
theorem regProp_log (m : ℕ) : RegProp m (Nat.log 4 m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using regProp_zero 0
  · have h1 : 4 ^ Nat.log 4 m ≤ m := Nat.pow_log_le_self 4 (by omega)
    exact regProp_mono ((regThreshold_le_four_pow _).trans h1) (regProp_regThreshold _)

/-- Explicit form of `F(m) ≫ log m`: every graph on `m` vertices has a regular induced
subgraph on at least `log₄ m` vertices, so `F(m) ≥ log₄ m`. -/
theorem log_le_regGuarantee (m : ℕ) : Nat.log 4 m ≤ regGuarantee m :=
  le_regGuarantee_of_regProp (regProp_log m)

/-- The graph-level form of `F(m) ≫ log m`. -/
theorem hasRegularInduced_log (m : ℕ) (G : SimpleGraph (Fin m)) :
    HasRegularInduced G (Nat.log 4 m) :=
  regProp_log m G

/-- `G(0) = 0`. -/
theorem regThreshold_zero : regThreshold 0 = 0 :=
  Nat.le_zero.mp (regThreshold_le_of_regProp (regProp_zero 0))

/-- One vertex suffices for a regular induced subgraph on one vertex. -/
theorem regProp_one_one : RegProp 1 1 :=
  fun G => ⟨{0}, by simp, isRegularOn_singleton G 0⟩

/-- `G(1) = 1`. -/
theorem regThreshold_one : regThreshold 1 = 1 :=
  le_antisymm (regThreshold_le_of_regProp regProp_one_one)
    (regProp_bound (regProp_regThreshold 1))

/-- Two vertices suffice for a regular induced subgraph on two vertices: on two vertices
either both are adjacent or neither is, so the whole graph is regular. -/
theorem regProp_two_two : RegProp 2 2 :=
  fun G => ⟨{0, 1}, by decide, isRegularOn_pair G 0 1⟩

/-- `G(2) = 2`. -/
theorem regThreshold_two : regThreshold 2 = 2 :=
  le_antisymm (regThreshold_le_of_regProp regProp_two_two)
    (regProp_bound (regProp_regThreshold 2))


/-- On five vertices there is always a regular induced subgraph on at least three
vertices. Either the graph has a triangle, or its complement does (an independent set of
size three), or else every vertex has exactly two neighbours — a vertex with three
neighbours would have two adjacent ones (a triangle) or three pairwise non-adjacent ones
(an independent triple), and a vertex with at most one neighbour has at least three
non-neighbours, which are pairwise adjacent (a triangle) or contain two non-adjacent ones
(an independent triple together with the vertex itself). -/
theorem regProp_five_three : RegProp 5 3 := by
  classical
  intro G
  by_cases htri : ∃ t : Finset (Fin 5), G.IsNClique 3 t
  · obtain ⟨t, ht⟩ := htri
    exact ⟨t, ht.2.ge, isRegularOn_of_isClique ht.1⟩
  by_cases hind : ∃ t : Finset (Fin 5), Gᶜ.IsNClique 3 t
  · obtain ⟨t, ht⟩ := hind
    exact ⟨t, ht.2.ge, isRegularOn_of_isClique_compl ht.1⟩
  have hno : ∀ a b c : Fin 5, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) :=
    fun a b c h => htri ⟨{a, b, c}, SimpleGraph.is3Clique_triple_iff.mpr h⟩
  have hno' : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ¬ (¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c) := by
    intro a b c hab hac hbc h
    exact hind ⟨{a, b, c}, SimpleGraph.is3Clique_triple_iff.mpr
      ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨hab, h.1⟩,
        (SimpleGraph.compl_adj _ _ _).mpr ⟨hac, h.2.1⟩,
        (SimpleGraph.compl_adj _ _ _).mpr ⟨hbc, h.2.2⟩⟩⟩
  refine ⟨Finset.univ, by simp, 2, ?_⟩
  intro v _
  have hNe : Finset.univ.filter (fun w => G.Adj v w)
      = (Finset.univ.erase v).filter (fun w => G.Adj v w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h => ⟨fun hc => G.irrefl (hc ▸ h), h⟩, fun h => h.2⟩
  have herase : (Finset.univ.erase v).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v)
    (p := fun w => G.Adj v w)
  rw [herase] at hsum
  rw [hNe]
  have hupper : ((Finset.univ.erase v).filter (fun w => G.Adj v w)).card ≤ 2 := by
    by_contra hc
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq
      (show 3 ≤ ((Finset.univ.erase v).filter (fun w => G.Adj v w)).card by omega)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp htc
    have ha : G.Adj v a := (Finset.mem_filter.mp (hts (by simp))).2
    have hb : G.Adj v b := (Finset.mem_filter.mp (hts (by simp))).2
    have hc' : G.Adj v c := (Finset.mem_filter.mp (hts (by simp))).2
    have h3 : G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
      have := hno' a b c hab hac hbc
      tauto
    rcases h3 with h | h | h
    · exact hno v a b ⟨ha, hb, h⟩
    · exact hno v a c ⟨ha, hc', h⟩
    · exact hno v b c ⟨hb, hc', h⟩
  have hlower : 2 ≤ ((Finset.univ.erase v).filter (fun w => G.Adj v w)).card := by
    by_contra hc
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq
      (show 3 ≤ ((Finset.univ.erase v).filter (fun a => ¬ G.Adj v a)).card by omega)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp htc
    have hmem : ∀ x ∈ ({a, b, c} : Finset (Fin 5)), x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      have hx' := hts hx
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hx'
      exact hx'
    obtain ⟨hav, ha⟩ := hmem a (by simp)
    obtain ⟨hbv, hb⟩ := hmem b (by simp)
    obtain ⟨hcv, hc'⟩ := hmem c (by simp)
    have h3 : ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c := by
      have := hno a b c
      tauto
    rcases h3 with h | h | h
    · exact hno' v a b (Ne.symm hav) (Ne.symm hbv) hab ⟨ha, hb, h⟩
    · exact hno' v a c (Ne.symm hav) (Ne.symm hcv) hac ⟨ha, hc', h⟩
    · exact hno' v b c (Ne.symm hbv) (Ne.symm hcv) hbc ⟨hb, hc', h⟩
  omega

/-- The graph on `Fin m` given by a symmetric, irreflexive `Bool`-valued adjacency
table. -/
def boolGraph {m : ℕ} (adj : Fin m → Fin m → Bool) (hsymm : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false) : SimpleGraph (Fin m) where
  Adj i j := adj i j = true
  symm := ⟨by
    intro i j h
    rw [hsymm j i]
    exact h⟩
  loopless := ⟨by
    intro i h
    rw [hirr i] at h
    exact Bool.noConfusion h⟩

/-- A certificate that a table has no regular induced subgraph on at least `n` vertices:
in every candidate set two vertices have different neighbour counts. -/
theorem not_hasRegularInduced_of_witness {m n : ℕ} (adj : Fin m → Fin m → Bool)
    (hsymm : ∀ i j, adj i j = adj j i) (hirr : ∀ i, adj i i = false)
    (h : ∀ S : Finset (Fin m), n ≤ S.card → ∃ v ∈ S, ∃ w ∈ S,
      (S.filter (fun u => adj v u = true)).card
        ≠ (S.filter (fun u => adj w u = true)).card) :
    ¬ HasRegularInduced (boolGraph adj hsymm hirr) n := by
  classical
  rintro ⟨S, hcard, d, hd⟩
  obtain ⟨v, hv, w, hw, hne⟩ := h S hcard
  have key : ∀ u : Fin m, S.filter (fun x => adj u x = true)
      = S.filter (fun x => (boolGraph adj hsymm hirr).Adj u x) := by
    intro u
    ext x
    simp only [Finset.mem_filter]
    exact Iff.rfl
  rw [key v, key w, hd v hv, hd w hw] at hne
  exact hne rfl

/-- Adjacency table of the path `0 - 1 - 2 - 3` inside `Fin m`; any further vertices are
isolated. -/
def path4Adj (m : ℕ) (i j : Fin m) : Bool :=
  (i.val < 4 && j.val < 4) && ((i.val + 1 == j.val) || (j.val + 1 == i.val))

/-- The path `P₄` has no regular induced subgraph on at least three vertices, so four
vertices do not suffice. -/
theorem not_regProp_four_three : ¬ RegProp 4 3 := by
  intro h
  exact not_hasRegularInduced_of_witness (path4Adj 4) (by decide) (by decide) (by decide)
    (h _)

/-- The disjoint union of the path `P₄` and an isolated vertex has no regular induced
subgraph on at least four vertices. -/
theorem not_regProp_five_four : ¬ RegProp 5 4 := by
  intro h
  exact not_hasRegularInduced_of_witness (path4Adj 5) (by decide) (by decide) (by decide)
    (h _)

/-- `G(3) = 5`. -/
theorem regThreshold_three : regThreshold 3 = 5 := by
  refine le_antisymm (regThreshold_le_of_regProp regProp_five_three) ?_
  by_contra hc
  exact not_regProp_four_three
    (regProp_mono (show regThreshold 3 ≤ 4 by omega) (regProp_regThreshold 3))

/-- `F(5) = 3`. -/
theorem regGuarantee_five : regGuarantee 5 = 3 := by
  refine le_antisymm ?_ (le_regGuarantee_of_regProp regProp_five_three)
  by_contra hc
  exact not_regProp_five_four
    (regProp_antitone_right (show 4 ≤ regGuarantee 5 by omega) (regProp_regGuarantee 5))

end Erdos82
