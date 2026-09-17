import MerLeanExperiment.GraphCode
import MerLeanExperiment.SmallRamsey

namespace CochromaticTwenty

/-- The actual forbidden subgraphs of the small Ramsey catalog. -/
def R34Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasCliqueOfSize G 3 ∧ ¬ HasIndependentOfSize G 4

theorem r34Free_comap {V W : Type*} (G : SimpleGraph W) (f : V ↪ W)
    (hG : R34Free G) : R34Free (G.comap f) := by
  classical
  constructor
  · rintro ⟨s, hs, hc⟩
    apply hG.1
    refine ⟨s.map f, by simpa using hs, ?_⟩
    intro u hu v hv hne
    obtain ⟨u, hu', rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v, hv', rfl⟩ := Finset.mem_map.mp hv
    exact hc hu' hv' (fun h => hne (congrArg f h))
  · rintro ⟨s, hs, hc⟩
    apply hG.2
    refine ⟨s.map f, by simpa using hs, ?_⟩
    intro u hu v hv hne
    obtain ⟨u, hu', rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v, hv', rfl⟩ := Finset.mem_map.mp hv
    exact hc hu' hv' (fun h => hne (congrArg f h))

theorem r34Free_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : R34Free G) : R34Free H := by
  have h := r34Free_comap G e.symm.toEquiv.toEmbedding hG
  have heq : G.comap e.symm.toEquiv.toEmbedding = H := by
    ext u v
    exact e.symm.map_rel_iff
  rwa [heq] at h

/-- Each extension is rejected by a concrete forbidden set, or accepted by a
concrete permutation into the next catalog. No catalog completeness is assumed. -/
inductive ExtensionWitness (n : ℕ) where
  | clique (vertices : Finset (Fin n))
  | independent (vertices : Finset (Fin n))
  | iso (target : ℕ) (permutation : Fin n → Fin n)

def ExtensionWitness.Valid {n : ℕ} (G : SimpleGraph (Fin n))
    (next : List ℕ) : ExtensionWitness n → Prop
  | .clique s => s.card = 3 ∧ G.IsClique s
  | .independent s => s.card = 4 ∧ G.IsIndepSet s
  | .iso c f => c ∈ next ∧ Function.Bijective f ∧
      ∀ u v, (codeGraph n c).Adj (f u) (f v) ↔ G.Adj u v

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (next : List ℕ) (w : ExtensionWitness n) : Decidable (w.Valid G next) := by
  cases w <;> unfold ExtensionWitness.Valid <;> infer_instance

theorem ExtensionWitness.sound {n : ℕ} {G : SimpleGraph (Fin n)}
    {next : List ℕ} (w : ExtensionWitness n) (hw : w.Valid G next)
    (hG : R34Free G) : ∃ c ∈ next, Nonempty (G ≃g codeGraph n c) := by
  cases w with
  | clique s => exact False.elim (hG.1 ⟨s, hw.1, hw.2⟩)
  | independent s => exact False.elim (hG.2 ⟨s, hw.1, hw.2⟩)
  | iso c f =>
    exact ⟨c, hw.1, ⟨{ toEquiv := Equiv.ofBijective f hw.2.1,
                       map_rel_iff' := by intro u v; exact hw.2.2 u v }⟩⟩

def CatalogComplete (n : ℕ) (codes : List ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), R34Free G →
    ∃ c ∈ codes, Nonempty (G ≃g codeGraph n c)

def CatalogStep (n : ℕ) (previous next : List ℕ) : Prop :=
  ∀ i : Fin previous.length, ∀ m : Fin (2 ^ n),
    R34Free (codeGraph (n + 1) (extendCode n (previous.get i) m.val)) →
    ∃ c ∈ next, Nonempty
      (codeGraph (n + 1) (extendCode n (previous.get i) m.val) ≃g codeGraph (n + 1) c)

theorem catalogStep_of_witnesses {n : ℕ} {previous next : List ℕ}
    (w : Fin previous.length → Fin (2 ^ n) → ExtensionWitness (n + 1))
    (hw : ∀ i m, (w i m).Valid
      (codeGraph (n + 1) (extendCode n (previous.get i) m.val)) next) :
    CatalogStep n previous next := by
  intro i m hG
  exact (w i m).sound (hw i m) hG

theorem catalogComplete_zero : CatalogComplete 0 [0] := by
  intro G _
  refine ⟨0, by simp, ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩⟩
  intro u
  exact Fin.elim0 u

theorem catalogComplete_succ {n : ℕ} {previous next : List ℕ}
    (hprevious : CatalogComplete n previous)
    (hbound : ∀ c ∈ previous, c < 2 ^ triangle n)
    (hstep : CatalogStep n previous next) : CatalogComplete (n + 1) next := by
  intro G hG
  let inc : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩
  obtain ⟨c, hc, ⟨e⟩⟩ := hprevious (G.comap inc) (r34Free_comap G inc hG)
  obtain ⟨mask, hmask, ⟨e'⟩⟩ := exists_extension_iso (hbound c hc) G e
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
  have hfree := r34Free_iso e' hG
  rw [← hi] at hfree e'
  obtain ⟨d, hd, ⟨e''⟩⟩ := hstep i ⟨mask, hmask⟩ hfree
  exact ⟨d, hd, ⟨e'.trans e''⟩⟩

end CochromaticTwenty

#print axioms CochromaticTwenty.catalogComplete_succ
#print axioms CochromaticTwenty.catalogStep_of_witnesses
