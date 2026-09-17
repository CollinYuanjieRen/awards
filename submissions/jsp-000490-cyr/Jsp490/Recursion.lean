import Mathlib

/-!
# JSP-000490 / Erdős #603 — the end-homogeneous recursion

This is the combinatorial heart of the Erdős–Rado argument.  Fix a colouring `c : V → V → Y` and a
well-ordered index type `W`.  For every `y : V` we build a transfinite sequence `seq c y : W → V`:
at stage `w`, having already produced the terms `seq c y v` for `v < w`, we pick the
`WellOrderingRel`-least vertex which is new and which is coloured against every earlier term
exactly as `y` is; if there is no such vertex we use `y` itself.

The facts exported here are:

* `seq_mem_candidates` (R1): as long as `y` has not yet appeared, the stage-`w` term really is such
  a vertex;
* `seq_injective_of_forall_ne`, `colour_seq_of_forall_ne` (R2): if `y` never appears, `seq c y` is
  injective and *end-homogeneous*: `c (seq c y v) (seq c y w)` depends only on `v`, for `v < w`;
* `seq_eq_of_pattern_eq` (R3): the sequence up to `β` is determined by the colour pattern below
  `β`, as long as `y` has not appeared below `β`;
* `code_injective` (R4): if every `y` appears in its own sequence, then `y` is determined by its
  first-hit stage together with its colour pattern below that stage.
-/

universe u

namespace Erdos603

open scoped Classical

variable {V Y : Type u} {W : Type u} [LinearOrder W] [WellFoundedLT W]

/-- The candidates at stage `w`, given the earlier terms `prev : Set V`: not yet used, and coloured
against every earlier term exactly as `y` is. -/
def candidates (c : V → V → Y) (y : V) (prev : Set V) : Set V :=
  {z | z ∉ prev ∧ ∀ p ∈ prev, c p z = c p y}

/-- One step of the recursion: the `WellOrderingRel`-least candidate relative to `prev`, or `y`
itself if there is none. -/
private noncomputable def step (c : V → V → Y) (y : V) (prev : Set V) : V :=
  if h : (candidates c y prev).Nonempty then
    (WellOrderingRel.isWellOrder (α := V)).wf.min _ h else y

/-- `seq c y : W → V`: at stage `w`, the `WellOrderingRel`-least candidate relative to the earlier
terms `{seq c y v | v < w}`, or `y` itself if there is no candidate.  Defined by well-founded
recursion. -/
noncomputable def seq (c : V → V → Y) (y : V) : W → V :=
  (wellFounded_lt (α := W)).fix fun w ih => step c y {z | ∃ v, ∃ hv : v < w, ih v hv = z}

/-- The colour pattern of `y`: `pattern c y w = c (seq c y w) y`. -/
noncomputable def pattern (c : V → V → Y) (y : V) (w : W) : Y := c (seq c y w) y

/-- The defining equation of `seq`. -/
theorem seq_eq (c : V → V → Y) (y : V) (w : W) :
    seq c y w =
      (if h : (candidates c y {z | ∃ v < w, seq c y v = z}).Nonempty
        then (WellOrderingRel.isWellOrder (α := V)).wf.min _ h else y) := by
  have h1 : seq c y w = step c y {z | ∃ v, ∃ _ : v < w, seq c y v = z} :=
    WellFounded.fix_eq _ _ w
  have h2 : {z | ∃ v, ∃ _ : v < w, seq c y v = z} = {z | ∃ v < w, seq c y v = z} := by
    ext z; simp only [exists_prop]
  rw [h1, h2, step]

/-- (R1) As long as `y` has not appeared, the stage-`w` term is a genuine candidate. -/
theorem seq_mem_candidates (c : V → V → Y) (y : V) (w : W) (hy : ∀ v < w, seq c y v ≠ y) :
    seq c y w ∈ candidates c y {z | ∃ v < w, seq c y v = z} := by
  have hy' : y ∉ {z | ∃ v < w, seq c y v = z} := by
    rintro ⟨v, hv, hvy⟩
    exact hy v hv hvy
  have hne : (candidates c y {z | ∃ v < w, seq c y v = z}).Nonempty :=
    ⟨y, hy', fun _ _ => rfl⟩
  rw [seq_eq, dite_eq_left hne]
  exact WellFounded.min_mem _ _ hne

/-- (R2) If `y` never appears, the sequence is injective. -/
theorem seq_injective_of_forall_ne (c : V → V → Y) (y : V) (hy : ∀ w : W, seq c y w ≠ y) :
    Function.Injective (seq c y : W → V) := by
  have key : ∀ v w : W, v < w → seq c y w ≠ seq c y v := by
    intro v w hvw hcon
    exact (seq_mem_candidates c y w fun v _ => hy v).1 ⟨v, hvw, hcon.symm⟩
  intro v w hvw
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key v w h hvw.symm
  · exact key w v h hvw

/-- (R2) If `y` never appears, the sequence is end-homogeneous. -/
theorem colour_seq_of_forall_ne (c : V → V → Y) (y : V) (hy : ∀ w : W, seq c y w ≠ y) {v w : W}
    (hvw : v < w) : c (seq c y v) (seq c y w) = pattern c y v :=
  (seq_mem_candidates c y w fun v _ => hy v).2 _ ⟨v, hvw, rfl⟩

/-- (R3) Determinacy: equal colour patterns below `β` force equal sequences up to and including
`β`, provided `y` itself has not yet appeared below `β` (which is what guarantees that the set of
candidates is nonempty at every stage `w ≤ β`, so that both sequences take the `min` branch).

The hypothesis `hy` cannot be dropped: if the candidate set is empty at some stage `w ≤ β`, then by
definition `seq c y w = y` and `seq c y' w = y'`, and these differ for `y ≠ y'`.  At the only place
where this lemma is used (`code_injective`, with `β` the first-hit stage of `y`) `hy` is exactly
`seq_ne_of_lt_firstHit`. -/
theorem seq_eq_of_pattern_eq (c : V → V → Y) {y y' : V} {β : W}
    (hy : ∀ v < β, seq c y v ≠ y) (h : ∀ v < β, pattern c y v = pattern c y' v) :
    ∀ w ≤ β, seq c y w = seq c y' w := by
  intro w
  induction w using WellFoundedLT.induction with
  | _ w ih =>
    intro hw
    have ih' : ∀ v < w, seq c y v = seq c y' v := fun v hv =>
      ih v hv (lt_of_lt_of_le hv hw).le
    -- the two sequences have produced the same terms below `w`
    have hprev : {z | ∃ v < w, seq c y v = z} = {z | ∃ v < w, seq c y' v = z} := by
      ext z
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, (ih' v hv).symm⟩
      · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, ih' v hv⟩
    -- `y` and `y'` are coloured the same way against every earlier term
    have hcol : ∀ p ∈ {z | ∃ v < w, seq c y v = z}, c p y = c p y' := by
      rintro p ⟨v, hv, rfl⟩
      have hvβ := h v (lt_of_lt_of_le hv hw)
      simp only [pattern] at hvβ
      rw [hvβ, ih' v hv]
    -- hence the two candidate sets coincide
    have hcand : candidates c y {z | ∃ v < w, seq c y v = z}
        = candidates c y' {z | ∃ v < w, seq c y v = z} := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun p hp => (h2 p hp).trans (hcol p hp)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun p hp => (h2 p hp).trans (hcol p hp).symm⟩
    -- and they are nonempty, since `y` is a candidate
    have hy' : y ∉ {z | ∃ v < w, seq c y v = z} := by
      rintro ⟨v, hv, hvy⟩
      exact hy v (lt_of_lt_of_le hv hw) hvy
    have hne : (candidates c y {z | ∃ v < w, seq c y v = z}).Nonempty :=
      ⟨y, hy', fun _ _ => rfl⟩
    rw [seq_eq c y w, seq_eq c y' w, ← hprev, dite_eq_left hne, dite_eq_left (hcand ▸ hne)]
    congr 1

/-- The first stage at which `y` appears (given that it does). -/
noncomputable def firstHit (c : V → V → Y) (y : V) (h : ∃ w : W, seq c y w = y) : W :=
  wellFounded_lt.min {w | seq c y w = y} h

theorem seq_firstHit (c : V → V → Y) (y : V) (h : ∃ w : W, seq c y w = y) :
    seq c y (firstHit c y h) = y :=
  wellFounded_lt.min_mem {w : W | seq c y w = y} h

theorem seq_ne_of_lt_firstHit (c : V → V → Y) (y : V) (h : ∃ w : W, seq c y w = y) {v : W}
    (hv : v < firstHit c y h) : seq c y v ≠ y := fun hcon =>
  wellFounded_lt.not_lt_min {w : W | seq c y w = y} (x := v) hcon hv

/-- The code of `y`: its first-hit stage together with its colour pattern below it.

Note the explicit coercion `(v : W)`: written as `pattern c y v` the index type of `pattern` would
be unified with the subtype `↥(Set.Iio β)` itself (which carries a `LinearOrder` and a
`WellFoundedLT` instance), i.e. it would denote a different, subtype-indexed recursion. -/
noncomputable def code (c : V → V → Y) (hall : ∀ y : V, ∃ w : W, seq c y w = y) (y : V) :
    Σ β : W, (Set.Iio β → Y) :=
  ⟨firstHit c y (hall y), fun v => pattern c y (v : W)⟩

/-- (R4) If every `y` appears in its own sequence, the code map is injective. -/
theorem code_injective (c : V → V → Y) (hall : ∀ y : V, ∃ w : W, seq c y w = y) :
    Function.Injective (code c hall) := by
  intro y y' heq
  have hβ : firstHit c y (hall y) = firstHit c y' (hall y') := congrArg Sigma.fst heq
  have hpat : ∀ v < firstHit c y (hall y), pattern c y v = pattern c y' v := by
    intro v hv
    have hvβ : v < firstHit c y' (hall y') := hβ ▸ hv
    have hv' : v < (code c hall y').1 := hvβ
    have hv0 : v < (code c hall y).1 := hv
    have h2 : (if hb : v < (code c hall y).1 then (code c hall y).2 ⟨v, hb⟩ else pattern c y v)
        = (if hb : v < (code c hall y').1 then (code c hall y').2 ⟨v, hb⟩ else pattern c y v) :=
      congrArg
        (fun p : Σ β : W, (Set.Iio β → Y) =>
          if hb : v < p.1 then p.2 ⟨v, hb⟩ else pattern c y v) heq
    rw [dite_eq_left hv0, dite_eq_left hv'] at h2
    simpa only [code] using h2
  have h3 : seq c y (firstHit c y (hall y)) = seq c y' (firstHit c y (hall y)) :=
    seq_eq_of_pattern_eq c (fun v hv => seq_ne_of_lt_firstHit c y (hall y) hv) hpat _ le_rfl
  rw [seq_firstHit c y (hall y), hβ, seq_firstHit c y' (hall y')] at h3
  exact h3


end Erdos603
