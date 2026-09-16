import Lean

unsafe def main : IO Unit := do
  let fresh := (← Lean.mkEmptyEnvironment 0).toKernelEnv
  let bad : Lean.Declaration := .thmDecl {
    name := `Jsp285ReplayNegative.illTyped
    levelParams := []
    type := .sort .zero
    value := .sort .zero
  }
  match fresh.addDeclCore 0 0 bad (cancelTk? := none) with
  | .ok _ => throw <| IO.userError "FAIL: checked kernel entry accepted ill-typed theorem"
  | .error ex =>
    IO.println "PASS: checked kernel entry rejected ill-typed theorem"
    IO.println (← ex.toMessageData {} |>.toString)
