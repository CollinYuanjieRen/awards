/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import Lean.AddDecl

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal

/-!
# `Lean.Environment.replay`

`replay env constantMap` will "replay" all the constants in `constantMap : HashMap Name ConstantInfo` into `env`,
sending each declaration to the kernel for checking.

`replay` does not send constructors or recursors in `constantMap` to the kernel,
but rather checks that they are identical to constructors or recursors generated in the environment
after replaying any inductive definitions occurring in `constantMap`.

`replay` can be used either as:
* a verifier for an `Environment`, by sending everything to the kernel, or
* a mechanism to safely transfer constants from one `Environment` to another.

-/

namespace Lean.Jsp937Replay

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info =>
        addDecl (Declaration.defnDecl   info)
      | .thmInfo    info =>
        addDecl (Declaration.thmDecl    info)
      | .axiomInfo  info =>
        addDecl (Declaration.axiomDecl  info)
      | .opaqueInfo info =>
        addDecl (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants[n]!))
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl (Declaration.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        -- quotDecl creates four primitives at once and requires Eq first.
        replayConstant `Eq
        if !((← get).env.find? `Quot).isSome then
          addDecl (Declaration.quotDecl)
        for q in #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
          match (← get).env.find? q, (← read).newConstants[q]? with
          | some (.quotInfo generated), some (.quotInfo original) =>
            unless generated == original do
              throw <| IO.userError s!"Quotient primitive mismatch: {q}"
          | _, _ => throw <| IO.userError s!"Missing quotient primitive: {q}"
          modify fun s => { s with
            remaining := s.remaining.erase q, pending := s.pending.erase q }
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay

/--
"Replay" some constants into an `Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.
-/
def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) : IO Kernel.Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s.env

end Lean.Jsp937Replay

/- Standalone audit IO, never imported by any mathematical proof. The unsafe
   import callback lifetime is standard loader mechanics, not a proof rule. -/
unsafe def main (args : List String) : IO Unit := do
  let moduleText :: rootsText := args | throw <| IO.userError "Usage: ReplayCheck MODULE ROOT..."
  unless !rootsText.isEmpty do
    throw <| IO.userError "At least one root is required"
  let parseName := fun s : String => (s.splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let moduleName := parseName moduleText
  let roots := rootsText.map parseName
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[{ module := moduleName }] {} fun imported => do
    let constants := imported.constants.map₁
    let mut safeCount := 0
    let mut unsafeCount := 0
    let mut partialCount := 0
    for (_, ci) in constants.toList do
      if ci.isUnsafe then unsafeCount := unsafeCount + 1
      else if ci.isPartial then partialCount := partialCount + 1
      else safeCount := safeCount + 1
    IO.println s!"Imported constants: {constants.size}; replay eligible: {safeCount}; skipped unsafe: {unsafeCount}; skipped partial: {partialCount}"
    let fresh := (← Lean.mkEmptyEnvironment 0).toKernelEnv
    unless fresh.header.trustLevel == 0 do
      throw <| IO.userError "Fresh environment is not trust level zero"
    IO.println "Starting checked Kernel.Environment replay from fresh trust0; quotient primitives checked once after Eq"
    (← IO.getStdout).flush
    let checked ← Lean.Jsp937Replay.replay constants fresh
    unless checked.header.trustLevel == 0 do
      throw <| IO.userError "Replayed environment is not trust level zero"
    let mut present := 0
    for (n, ci) in constants.toList do
      if !ci.isUnsafe && !ci.isPartial then
        unless (checked.find? n).isSome do
          throw <| IO.userError s!"Eligible constant absent after replay: {n}"
        present := present + 1
    IO.println s!"All eligible constants present after replay: {present}"
    for root in roots do
      unless (checked.find? root).isSome do
        throw <| IO.userError s!"Root absent after replay: {root}"
      IO.println s!"Root present after replay: {root}"
    IO.println "PASS: checked replay completed, including all postponed constructor/recursor and quotient comparisons"
