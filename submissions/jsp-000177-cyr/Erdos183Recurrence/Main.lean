import Mathlib

/-!
# Erdős Problem #183: the pigeonhole recurrence `R(3;k) ≤ 2 + k (R(3;k−1) − 1)`

Erdős asked to determine `lim R(3;k)^{1/k}`, where `R(3;k)` is the least `n` such that every
`k`-colouring of the edges of `K_n` has a monochromatic triangle (SOLVED: the limit is infinite,
OpenAI; NOT formalized here).  The problem page records: "An easy pigeonhole argument shows that
`R(3;k) ≤ 2 + k(R(3;k−1) − 1)`, from which `R(3;k) ≤ ⌈e k!⌉` immediately follows."  This file proves
the recurrence for every `k ≥ 1`, together with the finiteness of `R(3;k)` that makes the
`sInf` in its definition meaningful (the `⌈e k!⌉` corollary is not formalized).

`ForcesMonochromaticTriangle` and `multicolourTriangleRamsey` are copied verbatim from the
formal-conjectures file for the problem, and `TopEdgeLabeling.CliqueFree` from its
`FormalConjecturesForMathlib` dependency.  With these definitions `R(3;0) = 2` (for `n ≥ 2` there
is no `0`-colouring of `K_n`, so the condition holds vacuously) and `R(3;1) = 3`.

Proof idea.  Let `r = R(3;k−1)` and `n = 2 + k(r − 1)`.  In a `k`-colouring of `K_n`, a vertex `v`
has `1 + k(r − 1)` neighbours, so some colour `c` occurs on `≥ r` edges at `v`; if two of those
neighbours are joined in colour `c` we have a monochromatic triangle, otherwise they span a
`(k − 1)`-colouring of `K_r`, which contains a monochromatic triangle by the definition of `r`.
-/

open SimpleGraph

namespace SimpleGraph

/-- A labelling of the edges of the complete graph on `V` by `ι` is `n`-clique-free when no
colour class contains an `n`-clique, that is, when it admits no monochromatic `n`-clique. -/
def TopEdgeLabeling.CliqueFree {V ι : Type*} (C : TopEdgeLabeling V ι) (n : ℕ) : Prop :=
  ∀ i : ι, (C.labelGraph i).CliqueFree n

end SimpleGraph

namespace Erdos183

/-- `n` forces a monochromatic triangle on `k` colours when every `k`-colouring of the edges
of `K_n` has a colour class containing a triangle. -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ C.CliqueFree 3

/-- $R(3;k)$, the minimal `n` such that every `k`-colouring of the edges of `K_n` contains a
monochromatic triangle. -/
noncomputable def multicolourTriangleRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

/-! ### Pullbacks of edge labellings -/

section Pullback

variable {V V' K : Type*}

/-- The colour of an edge of a pullback labelling is the colour of its image edge. -/
theorem get_pullback' (C : TopEdgeLabeling V K) (f : V' ↪ V) (x y : V') (h : x ≠ y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (fun e => h (f.injective e)) := rfl

/-- Adjacency in a colour class of a pullback labelling. -/
theorem labelGraph_pullback_adj (C : TopEdgeLabeling V K) (f : V' ↪ V) (k : K) (x y : V') :
    ((C.pullback f).labelGraph k).Adj x y ↔ (C.labelGraph k).Adj (f x) (f y) := by
  simp only [TopEdgeLabeling.labelGraph_adj, get_pullback', ne_eq, f.injective.eq_iff]

/-- A colour class of a pullback labelling embeds into the corresponding colour class of the
original labelling. -/
def labelGraphEmbedding (C : TopEdgeLabeling V K) (f : V' ↪ V) (k : K) :
    ((C.pullback f).labelGraph k) ↪g (C.labelGraph k) :=
  ⟨f, fun {a b} => (labelGraph_pullback_adj C f k a b).symm⟩

/-- Clique-freeness of an edge labelling passes to pullbacks. -/
theorem cliqueFree_pullback {n : ℕ} {C : TopEdgeLabeling V K} {f : V' ↪ V}
    (h : C.CliqueFree n) : (C.pullback f).CliqueFree n :=
  fun k => (h k).comap (labelGraphEmbedding C f k).isContained

end Pullback

/-- Forcing is monotone in the number of vertices. -/
theorem forces_mono {n m k : ℕ} (hnm : n ≤ m) (h : ForcesMonochromaticTriangle n k) :
    ForcesMonochromaticTriangle m k := by
  intro C hC
  exact h (C.pullback (Fin.castLEEmb hnm)) (cliqueFree_pullback hC)

/-! ### Deleting one colour from `Fin (k + 1)` -/

/-- `dropColour c d h` removes the colour `c` from `Fin (k + 1)`, identifying the remaining
colours with `Fin k`. -/
def dropColour {k : ℕ} (c d : Fin (k + 1)) (h : (d : ℕ) ≠ (c : ℕ)) : Fin k :=
  if hlt : (d : ℕ) < (c : ℕ) then ⟨(d : ℕ), by have := c.isLt; omega⟩
  else ⟨(d : ℕ) - 1, by have := d.isLt; omega⟩

/-- `liftColour c` reinserts the colour `c`; it is a left inverse of `dropColour c`. -/
def liftColour {k : ℕ} (c : Fin (k + 1)) (i : Fin k) : Fin (k + 1) :=
  if (i : ℕ) < (c : ℕ) then ⟨(i : ℕ), by have := i.isLt; omega⟩
  else ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩

theorem liftColour_dropColour {k : ℕ} (c d : Fin (k + 1)) (h : (d : ℕ) ≠ (c : ℕ)) :
    liftColour c (dropColour c d h) = d := by
  have hd := d.isLt
  have hc := c.isLt
  unfold liftColour dropColour
  split_ifs with h1 h2 <;> simp_all [Fin.ext_iff] <;> omega

theorem dropColour_congr {k : ℕ} (c : Fin (k + 1)) {d d' : Fin (k + 1)}
    (h : (d : ℕ) ≠ (c : ℕ)) (h' : (d' : ℕ) ≠ (c : ℕ)) (hdd : d = d') :
    dropColour c d h = dropColour c d' h' := by
  subst hdd; rfl

/-- The pigeonhole step, in the form that is convenient to prove: any `n` at least
`2 + (k + 1)(r − 1)` forces a monochromatic triangle on `k + 1` colours. -/
theorem forces_succ_aux {k r n : ℕ} (hr : ForcesMonochromaticTriangle r k)
    (hn : 2 + (k + 1) * (r - 1) ≤ n) : ForcesMonochromaticTriangle n (k + 1) := by
  intro C hfree
  have hv0 : 0 < n := by omega
  obtain ⟨v⟩ : Nonempty (Fin n) := ⟨⟨0, hv0⟩⟩
  set S : Finset (Fin n) := Finset.univ.erase v with hSdef
  have hScard : S.card = n - 1 := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  set φ : Fin n → Fin (k + 1) := fun w => if h : v ≠ w then C.get v w h else 0 with hφdef
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := φ) (s := S) (t := (Finset.univ : Finset (Fin (k + 1)))) (n := r - 1)
      (fun a _ => Finset.mem_univ _)
      (by rw [hScard, Finset.card_univ, Fintype.card_fin]; omega)
  set T : Finset (Fin n) := {x ∈ S | φ x = c} with hTdef
  have hTcard : r ≤ T.card := by omega
  have hTcol : ∀ x ∈ T, ∃ h : v ≠ x, C.get v x h = c := by
    intro x hx
    rw [hTdef, Finset.mem_filter] at hx
    obtain ⟨hxS, hxφ⟩ := hx
    have hvx : v ≠ x := (Finset.ne_of_mem_erase (hSdef ▸ hxS)).symm
    exact ⟨hvx, by simpa [hφdef, hvx] using hxφ⟩
  by_cases hA : ∃ x ∈ T, ∃ y ∈ T, ∃ h : x ≠ y, C.get x y h = c
  · obtain ⟨x, hx, y, hy, hxy, hxyc⟩ := hA
    obtain ⟨hvx, hvxc⟩ := hTcol x hx
    obtain ⟨hvy, hvyc⟩ := hTcol y hy
    refine hfree c {v, x, y} ?_
    rw [SimpleGraph.is3Clique_triple_iff]
    exact ⟨(TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨hvx, hvxc⟩,
      (TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨hvy, hvyc⟩,
      (TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨hxy, hxyc⟩⟩
  · push Not at hA
    obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq hTcard
    obtain ⟨e, heT⟩ : ∃ e : Fin r ↪ Fin n, ∀ i, e i ∈ T :=
      ⟨(T'.orderEmbOfFin hT'card).toEmbedding, fun i => hT'sub (T'.orderEmbOfFin_mem hT'card i)⟩
    have he_ne : ∀ i j : Fin r, i ≠ j → e i ≠ e j := fun i j h q => h (e.injective q)
    have hcol : ∀ (i j : Fin r) (H : i ≠ j),
        ((C.get (e i) (e j) (he_ne i j H) : Fin (k + 1)) : ℕ) ≠ (c : ℕ) := by
      intro i j H q
      exact hA (e i) (heT i) (e j) (heT j) (he_ne i j H) (Fin.ext q)
    obtain ⟨D, hDget⟩ : ∃ D : SimpleGraph.TopEdgeLabeling (Fin r) (Fin k),
        ∀ (i j : Fin r) (H : i ≠ j),
          D.get i j H = dropColour c (C.get (e i) (e j) (he_ne i j H)) (hcol i j H) :=
      ⟨SimpleGraph.EdgeLabeling.mk
        (fun i j H => dropColour c (C.get (e i) (e j) (he_ne i j H)) (hcol i j H))
        (fun i j H => dropColour_congr c _ _ (SimpleGraph.EdgeLabeling.get_comm _ _ _)),
       fun i j H => rfl⟩
    obtain ⟨i', hi'⟩ : ∃ i, ¬ (D.labelGraph i).CliqueFree 3 := by
      by_contra hcon
      push Not at hcon
      exact hr D hcon
    obtain ⟨t, ht⟩ : ∃ t, (D.labelGraph i').IsNClique 3 t := by
      by_contra hcon
      push Not at hcon
      exact hi' hcon
    obtain ⟨a, b, b', hab, hab', hbb', rfl⟩ := SimpleGraph.is3Clique_iff.1 ht
    have hD : ∀ (i j : Fin r) (H : i ≠ j), (D.labelGraph i').Adj i j →
        C.get (e i) (e j) (he_ne i j H) = liftColour c i' := by
      intro i j H hadj
      obtain ⟨H', hH'⟩ := (TopEdgeLabeling.labelGraph_adj i j).1 hadj
      rw [hDget i j H'] at hH'
      rw [← hH', liftColour_dropColour]
    refine hfree (liftColour c i') {e a, e b, e b'} ?_
    rw [SimpleGraph.is3Clique_triple_iff]
    refine ⟨(TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨he_ne _ _ hab.ne, hD a b hab.ne hab⟩,
      (TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨he_ne _ _ hab'.ne, hD a b' hab'.ne hab'⟩,
      (TopEdgeLabeling.labelGraph_adj (C := C) _ _).2 ⟨he_ne _ _ hbb'.ne, hD b b' hbb'.ne hbb'⟩⟩

/-- **The pigeonhole step**: if `K_r` forces a monochromatic triangle on `k` colours, then
`K_{2 + (k+1)(r−1)}` forces one on `k + 1` colours. -/
theorem forces_succ {k r : ℕ} (hr : ForcesMonochromaticTriangle r k) :
    ForcesMonochromaticTriangle (2 + (k + 1) * (r - 1)) (k + 1) := by
  exact forces_succ_aux hr le_rfl

/-- `R(3;k)` is finite: some `n` forces a monochromatic triangle on `k` colours. -/
theorem exists_forces (k : ℕ) : ∃ n : ℕ, ForcesMonochromaticTriangle n k := by
  induction k with
  | zero => exact ⟨2, fun C _ => (C ⟨s(0, 1), by simp⟩).elim0⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨2 + (k + 1) * (r - 1), forces_succ hr⟩

/-- **Erdős #183, the pigeonhole recurrence**: `R(3;k) ≤ 2 + k (R(3;k−1) − 1)` for `k ≥ 1`. -/
theorem erdos_183_recurrence (k : ℕ) (hk : 1 ≤ k) :
    multicolourTriangleRamsey k ≤ 2 + k * (multicolourTriangleRamsey (k - 1) - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hne : {n : ℕ | ForcesMonochromaticTriangle n k'}.Nonempty := exists_forces k'
  have hr : ForcesMonochromaticTriangle (multicolourTriangleRamsey k') k' := Nat.sInf_mem hne
  have hle : multicolourTriangleRamsey (k' + 1)
      ≤ 2 + (k' + 1) * (multicolourTriangleRamsey k' - 1) := Nat.sInf_le (forces_succ hr)
  simpa using hle

end Erdos183

open Erdos183 in
/-- **Erdős #183, the recurrence, closed form**: `R(3;k)` is finite for every `k`, and no `k ≥ 1`
violates `R(3;k) ≤ 2 + k (R(3;k−1) − 1)`. -/
theorem erdos_183_recurrence_closed :
    (¬ ∃ k : ℕ, ∀ n : ℕ, ¬ ForcesMonochromaticTriangle n k) ∧
      ¬ ∃ k : ℕ, 1 ≤ k ∧ 2 + k * (multicolourTriangleRamsey (k - 1) - 1) < multicolourTriangleRamsey k := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := exists_forces k
    exact hk n hn
  · rintro ⟨k, hk, hlt⟩
    exact absurd (erdos_183_recurrence k hk) (not_le.mpr hlt)
