import Driver.Core

open Lean
open Jsp511Comparator

def expectRejected (label : String) (action : IO Unit) : IO Unit := do
  let rejected ← try
    action
    pure false
  catch e =>
    IO.println s!"PASS reject {label}: {e}"
    pure true
  unless rejected do
    throw <| IO.userError s!"negative test unexpectedly accepted: {label}"

def changedRootType (candidate : Export.ExportedEnv) (rootName : Name) : IO Export.ExportedEnv := do
  let some (.thmInfo root) := candidate.constMap[rootName]?
    | throw <| IO.userError "self-test root is not a theorem"
  return replaceConst candidate rootName (.thmInfo { root with type := .const ``False [] })

def changedSupportingBody (candidate : Export.ExportedEnv) (supportName : Name) :
    IO Export.ExportedEnv := do
  let some (.defnInfo support) := candidate.constMap[supportName]?
    | throw <| IO.userError "self-test candidate lacks supporting definition"
  return replaceConst candidate supportName (.defnInfo { support with value := .const ``False [] })

def customAxiomDependency (candidate : Export.ExportedEnv) (rootName : Name) :
    IO Export.ExportedEnv := do
  let some (.thmInfo root) := candidate.constMap[rootName]?
    | throw <| IO.userError "self-test root is not a theorem"
  let axiomName := `Jsp511ComparatorTest.customAxiom
  let axiomVal : AxiomVal := {
    name := axiomName, levelParams := [], type := root.type, isUnsafe := false
  }
  let candidate := addConst candidate axiomName (.axiomInfo axiomVal)
  return replaceConst candidate rootName (.thmInfo { root with value := .const axiomName [] })

def selfTest (referencePath candidatePath : System.FilePath) (expectedName rootName : Name) :
    IO Unit := do
  let reference ← parseExport referencePath
  let candidate ← parseExport candidatePath
  verify reference candidate expectedName rootName
  IO.println "PASS accept honest proof"
  let controlFailed ← try
    expectRejected "control" (pure ())
    pure false
  catch _ => pure true
  unless controlFailed do
    throw <| IO.userError "negative-test harness failed to detect its accepting control"
  IO.println "PASS negative-test harness control"
  expectRejected "changed theorem type" do
    verify reference (← changedRootType candidate rootName) expectedName rootName
  expectRejected "changed supporting-definition body" do
    verify reference (← changedSupportingBody candidate `ComparatorFixture.P)
      expectedName rootName
  expectRejected "custom axiom dependency" do
    verify reference (← customAxiomDependency candidate rootName) expectedName rootName

def usage : String :=
  "usage:\n  jsp511-comparator-driver reference.ndjson candidate.ndjson expectedName rootName\n" ++
  "  jsp511-comparator-driver --self-test reference.ndjson candidate.ndjson expectedName rootName"

def main (args : List String) : IO Unit := do
  match args with
  | [referencePath, candidatePath, expectedName, rootName] =>
      verify (← parseExport referencePath) (← parseExport candidatePath)
        expectedName.toName rootName.toName
      IO.println "PASS frozen-target expanded-root comparison, axiom audit, and Lean kernel replay"
  | ["--self-test", referencePath, candidatePath, expectedName, rootName] =>
      selfTest referencePath candidatePath expectedName.toName rootName.toName
  | _ => throw <| IO.userError usage
