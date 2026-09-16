import Comparator.Compare
import Lean

namespace Jsp511Comparator

open Lean

/-- Kernel-special declarations checked by the pinned upstream comparator. -/
def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce]

/-- The only axioms permitted by the frozen-target gate. -/
def legalAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Read an exporter NDJSON stream without elaborating any source. -/
def parseExport (path : System.FilePath) : IO Export.ExportedEnv := do
  let input ← IO.FS.readFile path
  let buffer ← IO.mkRef { data := input.toUTF8 }
  Export.parseStream (IO.FS.Stream.ofBuffer buffer)

/-- Extract the body of the safe, closed proposition definition used as the trusted target. -/
def expectedType (reference : Export.ExportedEnv) (expectedName : Name) : Except String Expr := do
  let some info := reference.constMap[expectedName]?
    | throw s!"Missing trusted expected-statement definition: '{expectedName}'"
  let .defnInfo value := info
    | throw s!"Trusted expected statement is not a definition: '{expectedName}'"
  if !value.levelParams.isEmpty then
    throw s!"Trusted expected statement has universe parameters: '{expectedName}'"
  if value.type != .sort .zero then
    throw s!"Trusted expected statement does not have type Prop: '{expectedName}'"
  if value.safety != .safe then
    throw s!"Trusted expected statement is not safe: '{expectedName}'"
  if value.value.hasLooseBVars || value.value.hasFVar || value.value.hasMVar then
    throw s!"Trusted expected-statement body is not closed: '{expectedName}'"
  return value.value

/-- Require the selected solution root to be a closed theorem with exactly the frozen body. -/
def checkRootType (candidate : Export.ExportedEnv) (rootName : Name)
    (target : Expr) : Except String Unit := do
  let some info := candidate.constMap[rootName]?
    | throw s!"Missing candidate theorem root: '{rootName}'"
  let .thmInfo value := info
    | throw s!"Candidate root is not a theorem: '{rootName}'"
  if !value.levelParams.isEmpty then
    throw s!"Candidate theorem root has universe parameters: '{rootName}'"
  if value.type.hasLooseBVars || value.type.hasFVar || value.type.hasMVar then
    throw s!"Candidate theorem type is not closed: '{rootName}'"
  if value.type != target then
    throw s!"Candidate theorem type does not exactly equal the frozen expected statement: '{rootName}'"

/-- Compare the entire frozen type closure with no theorem or definition exceptions. -/
def compareClosure (reference candidate : Export.ExportedEnv) (target : Expr) : Except String Unit :=
  Comparator.Compare.loop.run
      { challenge := reference, solution := candidate,
        definitionTargets := {}, theoremTargets := {} }
    |>.run' {
      worklist := target.getUsedConstants ++ primitiveTargets ++ legalAxioms,
      checked := {}
    }

/-- Replay every exported candidate declaration through Lean's kernel. -/
def replayCandidate (candidate : Export.ExportedEnv) : IO Unit := do
  let env := (← Lean.mkEmptyEnvironment).toKernelEnv
  let constMap := candidate.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| Lean.Kernel.Environment.replay constMap env

/-- Run the complete expanded-root frozen-target gate. -/
def verify (reference candidate : Export.ExportedEnv) (expectedName rootName : Name)
    : IO Unit := do
  replayCandidate reference
  let target ← IO.ofExcept <| expectedType reference expectedName
  IO.ofExcept <| checkRootType candidate rootName target
  IO.ofExcept <| compareClosure reference candidate target
  IO.ofExcept <| Comparator.checkAxioms candidate #[rootName] #[] legalAxioms
  replayCandidate candidate

/-- Replace one exported declaration, used only by controlled negative tests. -/
def replaceConst (env : Export.ExportedEnv) (name : Name) (info : ConstantInfo) :
    Export.ExportedEnv :=
  { env with constMap := env.constMap.insert name info }

/-- Add one exported declaration, used only by controlled negative tests. -/
def addConst (env : Export.ExportedEnv) (name : Name) (info : ConstantInfo) :
    Export.ExportedEnv :=
  { constMap := env.constMap.insert name info, constOrder := env.constOrder.push name }

end Jsp511Comparator
