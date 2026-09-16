import MerLeanExperiment.Goal
import Lean

open Filter MeasureTheory
open scoped Topology

#check Erdos492Real.schmidt_counterexample
#print axioms Erdos492Real.schmidt_counterexample
#print axioms Erdos492Real.finite_subdivision_lemma
#print axioms Erdos492Real.exponentialExceptionalSet_safe
#print axioms Erdos492Real.volume_exponentialExceptionalSet_le
#print axioms Erdos492Real.ae_not_uniformlyDistributed_from_family

example : ∃ a : ℕ → ℝ, a 0 = 0 ∧ StrictMono a ∧ Tendsto a atTop atTop ∧
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) ∧
    ∀ᵐ α : ℝ, 0 < α → ¬ Erdos492Real.UniformlyDistributed a α :=
  Erdos492Real.schmidt_counterexample

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
  let (_, seen) := (visit env ``Erdos492Real.schmidt_counterexample).run {}
  let names := seen.toArray
  let axioms := names.filter fun n => match env.checked.get.find? n with
    | some (.axiomInfo _) => true
    | _ => false
  logInfo m!"Uncached actual declaration closure count: {names.size}"
  logInfo m!"Uncached actual axioms: {axioms.qsort Name.lt}"
  for n in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
      throwError "Unexpected root axiom: {n}"
  for n in [``Erdos492Real.finite_subdivision_lemma,
      ``Erdos492Real.divisionSign_exponentialPoints_eq_phaseSign,
      ``Erdos492Real.ae_not_uniformlyDistributed_from_family] do
    unless seen.contains n do
      throwError "Missing required constructive dependency: {n}"
  logInfo "Actual finite construction, actual sign bridge, and global almost-everywhere argument occur in the root closure."
end IndependentAudit
