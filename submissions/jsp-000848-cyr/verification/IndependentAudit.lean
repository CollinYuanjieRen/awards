import MerLeanExperiment.Goal
import Lean

#check Erdos1018Topological.erdos_1018_ordinary_nonplanarity
#print axioms Erdos1018Topological.erdos_1018_ordinary_nonplanarity
#print axioms Erdos1018.kostochka_pyber_compact_k5
#print axioms Erdos1018Topological.planeDrawing_top_of_cliqueSubdivision
#print axioms Erdos1018Topological.completeFive_no_drawing
#print axioms Graph.IsDrawing.exists_euler_faceSystem

example (ε : ℝ) (hε : 0 < ε) :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
          ∃ S : G.Subgraph,
            S.verts.ncard ≤ C ∧ ¬ Nonempty (PlanarListColoring.PlaneDrawing S.coe) :=
  Erdos1018Topological.erdos_1018_ordinary_nonplanarity ε hε

-- Independent uncached traversal of the actual kernel declaration bodies.
-- This audit metaprogram is not a mathematical dependency of the theorem.
namespace IndependentAudit
open Lean
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  let expr (e : Expr) := e.getUsedConstants.forM (visit env)
  match env.checked.get.find? n with
  | some (.axiomInfo v) => expr v.type
  | some (.defnInfo v) => expr v.type *> expr v.value
  | some (.thmInfo v) => expr v.type *> expr v.value
  | some (.opaqueInfo v) => expr v.type *> expr v.value
  | some (.ctorInfo v) => expr v.type
  | some (.recInfo v) => expr v.type
  | some (.inductInfo v) => expr v.type *> v.ctors.forM (visit env)
  | _ => pure ()
run_cmd do
  let env ← getEnv
  let (_, seen) := (visit env ``Erdos1018Topological.erdos_1018_ordinary_nonplanarity).run {}
  let names := seen.toArray
  let axioms := names.filter fun n => match env.checked.get.find? n with
    | some (.axiomInfo _) => true
    | _ => false
  logInfo m!"Uncached actual declaration closure count: {names.size}"
  logInfo m!"Uncached actual axioms: {axioms.qsort Name.lt}"
  for n in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
      throwError "Unexpected root axiom: {n}"
  for n in [``Erdos1018.IsNonplanar, ``Erdos1018.ProblemStatement, ``Erdos1018.erdos_1018] do
    if seen.contains n then throwError "Unexpected certificate-only dependency: {n}"
  logInfo "Certificate-only IsNonplanar, ProblemStatement, and original erdos_1018 are absent from root closure."
end IndependentAudit
