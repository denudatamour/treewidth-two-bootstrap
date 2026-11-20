import Lean.Replay
import Lean.Util.CollectAxioms

/-! Recheck every safe project declaration and its transitive axioms. Each module is replayed
in a fresh Lean process against its direct, pinned imports. This isolates private names
and releases the preceding kernel environment before the next module begins. -/
open Lean

private def allowed : Array Name := #[`Classical.choice, `propext, `Quot.sound]

private def listProject : IO Unit := do
  let env ← importModules #[{module := `Bootstrap}] {}
  for m in env.header.moduleNames.filter (Name.isPrefixOf `Bootstrap) do
    let some idx := env.getModuleIdx? m | throw <| IO.userError s!"Missing module {m}"
    let deps := (env.header.moduleData[idx]!).imports.map (·.module)
    let localDeps := deps.filter (Name.isPrefixOf `Bootstrap)
    IO.println (String.intercalate " " ((m :: localDeps.toList).map toString))

private def replayOne (m : Name) : IO Unit := do
  unless Name.isPrefixOf `Bootstrap m do throw <| IO.userError s!"Unexpected module {m}"
  let env ← importModules #[{module := m}] {}
  let some idx := env.getModuleIdx? m | throw <| IO.userError s!"Could not import {m}"
  let data := env.header.moduleData[idx]!
  let base ← importModules data.imports {} 0
  let mut decls : Std.HashMap Name ConstantInfo := {}
  let mut skipped := 0
  let mut axState : CollectAxioms.State := {}
  for ci in data.constants do
    if ci.getUsedConstantsAsSet.contains `sorryAx then throw <| IO.userError s!"Admitted {ci.name}"
    if ci.isUnsafe || ci.isPartial then
      skipped := skipped + 1
      IO.println s!"EXCLUDED compiler implementation {ci.name}"
    else
      if ci matches .axiomInfo _ then throw <| IO.userError s!"Project axiom {ci.name}"
      if base.contains ci.name then throw <| IO.userError s!"Declaration already imported {ci.name}"
      decls := decls.insert ci.name ci
      axState := ((CollectAxioms.collect ci.name).run env).run axState |>.2
  let checked ← base.replay decls
  for (n, _) in decls.toList do
    unless checked.contains n do throw <| IO.userError s!"Missing after replay: {n}"
  for ax in axState.axioms do
    unless allowed.contains ax do throw <| IO.userError s!"Unexpected transitive axiom {ax}"
  let axioms := String.intercalate " " (axState.axioms.toList.map toString)
  IO.println s!"MODULE {m} PASS {decls.size} safe declarations"
  IO.println s!"RESULT {m} {decls.size} {skipped} {axioms}"

private def child (args : Array String) : IO String := do
  let exe ← IO.appPath
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["--run","ReplayAudit.lean"] ++ args
  }
  unless out.stderr.trim.isEmpty do IO.eprint out.stderr
  unless out.exitCode == 0 do
    IO.print out.stdout
    throw <| IO.userError s!"Replay worker {args} exited with code {out.exitCode}"
  return out.stdout

private def replayAll : IO Unit := do
  let jobs := (← child #["list"]).trim.splitOn "\n"
  let mut doneModules : Array String := #[]
  let mut used : Array String := #[]
  let mut total := 0
  let mut skipped := 0
  for line in jobs do
    let module :: deps := line.trim.splitOn " " | throw <| IO.userError "Missing module name"
    if module.isEmpty || doneModules.contains module then throw <| IO.userError s!"Invalid job {line}"
    for dep in deps do
      unless doneModules.contains dep do throw <| IO.userError s!"Unreplayed dependency {dep} of {module}"
    IO.println s!"REPLAY {module} in a fresh process"
    (← IO.getStdout).flush
    let out ← child #["module", module]
    IO.print out
    let some row := (out.trim.splitOn "\n").getLast? | throw <| IO.userError s!"No receipt for {module}"
    let "RESULT" :: name :: decls :: excluded :: axioms :=
      (row.trim.splitOn " ").filter (!·.isEmpty) | throw <| IO.userError s!"Malformed receipt: {row}"
    unless name == module do throw <| IO.userError s!"Unexpected receipt from {name}"
    let some n := decls.toNat? | throw <| IO.userError "Bad declaration count"
    let some k := excluded.toNat? | throw <| IO.userError "Bad excluded count"
    total := total+n
    skipped := skipped+k
    for ax in axioms do
      unless (allowed.map toString).contains ax do throw <| IO.userError s!"Unexpected transitive axiom {ax}"
      unless used.contains ax do used := used.push ax
    doneModules := doneModules.push module
  unless doneModules.back? == some "Bootstrap" do throw <| IO.userError "Missing umbrella module"
  let sorted := allowed.filter (fun ax => used.contains (toString ax))
  IO.println s!"PASS {total} safe declarations, {doneModules.size} project modules, {skipped} compiler auxiliaries excluded"
  IO.println s!"TRANSITIVE AXIOMS {sorted}"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match args with
  | [] => replayAll
  | ["list"] => listProject
  | ["module", module] => replayOne module.toName
  | _ => throw <| IO.userError "Use no arguments, list, or module Bootstrap.Module"
