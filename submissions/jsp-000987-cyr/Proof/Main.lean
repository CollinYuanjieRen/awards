import Proof.TriRamsey

/-!
# Erdős problem #1182 — the trivial bound `R(K_3, G) ≥ 2n − 1`

The problem page asks to estimate `f(n)` and `F(n)`, where `f(n)` is maximal such that some
connected graph `G` on `n` vertices with `f(n)` edges has `R(K_3, G) = 2n − 1`, and `F(n)` is
maximal such that *every* connected graph on `n` vertices with at most `F(n)` edges has
`R(K_3, G) = 2n − 1`. The page calls the bound `R(K_3, G) ≥ 2n − 1` for connected `G` on `n`
vertices trivial, and this package proves exactly that trivial bound, by the red complete
bipartite colouring of `K_{2n−2}`: split the `2n − 2` vertices into two parts of size `n − 1`
and colour an edge red iff its ends lie in different parts. Of any three vertices two share a
part, so there is no red triangle; the blue graph is two disjoint copies of `K_{n−1}`, and a
connected graph on `n` vertices does not fit into a part of size `n − 1`.

Finiteness of `R(K_3, G)`, i.e. `R(K_3, G) ≤ r(3, n)`, comes from the two-colour Ramsey theorem
in our own toolbox (a blue `K_n` contains a copy of every graph on `n` vertices).

Results: `not_triRamseyProp_of_connected` (the witness colouring refutes every `N ≤ 2n − 2`),
`triRamseyProp_ramsey` and `triRamsey_le_ramsey` (finiteness), `le_triRamsey_of_connected` and
`connLowerBound` (the trivial bound), and `not_exists_connected_triRamsey_lt` (the audited root,
the trivial bound in negation form).

Not claimed here: Chvátal's theorem `R(K_3, T) = 2n − 1` for trees, the consequences
`F(n) ≥ n − 1` and `f(n) ≥ F(n)` (whose proof on the page relies on it), the
Burr–Erdős–Faudree–Rousseau–Schelp and Brandt bounds, the numerical values of `f` and `F`, and
the `K_m` generalisations of Erdős problem #1182.
-/

namespace Erdos1182

open SimpleGraph

/-- **The witness statement.** For every `N ≤ 2n − 2` the red complete bipartite colouring of
`K_N`, with parts `{i | i.val < n − 1}` and its complement, has no red triangle and no blue copy
of a connected graph `G` on `n` vertices: a blue copy would be confined to a single part, which
has at most `n − 1 < n` vertices. -/
theorem not_triRamseyProp_of_connected (n N : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hN : N ≤ 2 * n - 2) : ¬ TriRamseyProp N G := by
  intro h
  rcases h (redBipartite N (n - 1)) with hcl | hcopy
  · exact hcl (redBipartite_cliqueFree N (n - 1))
  · obtain ⟨f⟩ : Nonempty (Copy G (redBipartite N (n - 1))ᶜ) := hcopy
    obtain ⟨u₀⟩ : Nonempty (Fin n) := hG.nonempty
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u₀.isLt
    have hinj : Function.Injective f.toHom := f.injective
    have hside : ∀ v : Fin n, ((f.toHom u₀).val < n - 1 ↔ (f.toHom v).val < n - 1) :=
      fun v => (hG.preconnected u₀ v).elim (fun p => side_of_walk f.toHom p)
    have hval : Function.Injective (fun v : Fin n => (f.toHom v).val) :=
      fun a b hab => hinj (Fin.val_injective hab)
    have key : (Finset.univ : Finset (Fin n)).card ≤ n - 1 := by
      by_cases hb : (f.toHom u₀).val < n - 1
      · have hmaps : Set.MapsTo (fun v : Fin n => (f.toHom v).val)
            (Finset.univ : Finset (Fin n)) (Finset.range (n - 1)) := by
          intro v _
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr ((hside v).mp hb))
        have := Finset.card_le_card_of_injOn _ hmaps (fun a _ b _ hab => hval hab)
        rwa [Finset.card_range] at this
      · have hmaps : Set.MapsTo (fun v : Fin n => (f.toHom v).val)
            (Finset.univ : Finset (Fin n)) (Finset.Ico (n - 1) N) := by
          intro v _
          refine Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨?_, (f.toHom v).isLt⟩)
          exact Nat.le_of_not_lt (fun hc => hb ((hside v).mpr hc))
        have := Finset.card_le_card_of_injOn _ hmaps (fun a _ b _ hab => hval hab)
        rw [Nat.card_Ico] at this
        omega
    rw [Finset.card_univ, Fintype.card_fin] at key
    omega

/-- **Finiteness.** `r(3, n)` vertices suffice: every red/blue colouring of `K_{r(3,n)}` has a
red triangle or a blue `K_n`, and a blue `K_n` contains a copy of every graph on `n` vertices. -/
theorem triRamseyProp_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : TriRamseyProp (ramsey 3 n) G := by
  intro R
  by_cases hR : R.CliqueFree 3
  · right
    have h := ramseyProp_ramsey 3 n R
    have hc : ¬ Rᶜ.CliqueFree n := fun hc => h ⟨hR, hc⟩
    let e := SimpleGraph.topEmbeddingOfNotCliqueFree hc
    refine ⟨⟨⟨fun v => e v, ?_⟩, ?_⟩⟩
    · intro a b hab
      exact e.map_rel_iff.mpr (G.ne_of_adj hab)
    · exact fun a b hab => e.injective hab
  · exact Or.inl hR

/-- `R(K_3, G) ≤ r(3, n)` for every graph `G` on `n` vertices. -/
theorem triRamsey_le_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : triRamsey G ≤ ramsey 3 n :=
  Nat.sInf_le (triRamseyProp_ramsey n G)

/-- **The trivial bound**, unfolded: `R(K_3, G) ≥ 2n − 1` for every connected graph `G` on `n`
vertices. -/
theorem le_triRamsey_of_connected (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 1 ≤ triRamsey G := by
  by_contra hlt
  rw [not_le] at hlt
  have hne : {N : ℕ | TriRamseyProp N G}.Nonempty := ⟨ramsey 3 n, triRamseyProp_ramsey n G⟩
  have hmem : TriRamseyProp (triRamsey G) G := Nat.sInf_mem hne
  exact not_triRamseyProp_of_connected n _ G hG (by omega) hmem

/-- **The trivial bound** of Erdős problem #1182: every connected graph `G` on `n` vertices has
`R(K_3, G) ≥ 2n − 1`. -/
theorem connLowerBound (n : ℕ) : ConnLowerBound n :=
  fun G hG => le_triRamsey_of_connected n G hG

/-- The trivial bound in negation form: no connected graph on `n` vertices has `R(K_3, G)` below
`2n − 1`. This is the audited root statement; it is equivalent to `connLowerBound`. -/
theorem not_exists_connected_triRamsey_lt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), G.Connected ∧ triRamsey G < 2 * n - 1 := by
  rintro ⟨G, hG, hlt⟩
  exact absurd (le_triRamsey_of_connected n G hG) (not_le.2 hlt)

end Erdos1182
