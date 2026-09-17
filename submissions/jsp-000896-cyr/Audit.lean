import Erdos1078Haxell

open Finset

#print axioms Erdos1078.erdos_1078
#print axioms Erdos1078.erdos_1078_closed
#print axioms Erdos1078.haxell
#print axioms Erdos1078.nonDom_of_degree
#print axioms Erdos1078.exists_IT
#print axioms Erdos1078.exists_pit_of_valid
#print axioms Erdos1078.step_improve
#print axioms Erdos1078.step_grow
#print axioms Erdos1078.exists_new_center

/-- Erdős Problem 1078 (Bollobás–Erdős–Szemerédi, proved by Haxell): an `r`-partite graph with
`n ≥ 1` vertices in each part and minimum degree at least `(r − 3/2) n` contains a `K_r`. -/
example (r n : ℕ) (hn : 1 ≤ n) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin r)
    (hsize : ∀ i : Fin r, (univ.filter (fun v => part v = i)).card = n)
    (hcross : ∀ v w, G.Adj v w → part v ≠ part w)
    (hdeg : ∀ v, ((r : ℝ) - 3 / 2) * n ≤ G.degree v) :
    ∃ S : Finset V, G.IsNClique r S :=
  Erdos1078.erdos_1078 r n hn G part hsize hcross hdeg

/-- The closed form: no such graph is `K_r`-free. -/
example :
    ¬ ∃ (r n : ℕ), 1 ≤ n ∧ ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj) (part : V → Fin r),
      (∀ i : Fin r, (univ.filter (fun v => part v = i)).card = n) ∧
      (∀ v w, G.Adj v w → part v ≠ part w) ∧
      (∀ v, ((r : ℝ) - 3 / 2) * n ≤ G.degree v) ∧ G.CliqueFree r :=
  Erdos1078.erdos_1078_closed

/-- Haxell's theorem: maximum degree at most `Δ` and all vertex classes of size at least `2Δ`
(and nonempty) give an independent transversal. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hcls : ∀ i : ι, 2 * Δ ≤ (univ.filter (fun v => part v = i)).card)
    (hne : ∀ i : ι, ∃ v, part v = i) :
    ∃ M : Finset V, Erdos1078.IsIT G part M :=
  Erdos1078.haxell G part Δ hdeg hcls hne

/-- The definitions unfold as intended. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι) (M : Finset V) :
    Erdos1078.IsIT G part M ↔
      ((∀ v ∈ M, ∀ w ∈ M, ¬ G.Adj v w) ∧ Set.InjOn part (M : Set V)) ∧ ∀ i, ∃ v ∈ M, part v = i :=
  Iff.rfl
