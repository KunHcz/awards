/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

The replay implementation below is adapted from Lean 4.23.0 Lean/Replay.lean.
Local modifications: use Kernel.Environment directly instead of the elaborator
Environment wrapper; replay the target dependency closures; initialize the
built-in quotient group once. Every declaration is checked through the official
Kernel.Environment.addDeclCore, with kernel checking enabled. The wrapper avoids
private-name collisions in elaborator metadata; it does not rename or remove
proof declarations. This tool is not imported by the mathematical proof.
-/
import Lean.Replay

open Lean

namespace JSP751KernelReplay

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Lean.Kernel.Environment
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
        addDecl (Declaration.quotDecl)
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
end JSP751KernelReplay

open Lean
open JSP751KernelReplay

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Erdos751Extension }] {} fun env => do
    if !env.contains `Erdos751Extension.answer then
      throw <| IO.userError "Missing target theorem"
    let constants := env.constants.map₁
    let mut remaining : NameSet := {}
    let mut quotientCount := 0
    for (n, ci) in constants.toList do
      if !ci.isUnsafe && !ci.isPartial then
        match ci with
        | .quotInfo _ =>
          quotientCount := quotientCount + 1
          if n == `Quot.lift then remaining := remaining.insert n
        | _ => remaining := remaining.insert n
    if !remaining.contains `Quot.lift then
      throw <| IO.userError "Missing kernel quotient primitive"
    let targets := #[`Erdos751.Main.erdos_751_strong,
      `Erdos751Extension.colorable_of_finite_subgraphs,
      `Erdos751Extension.finite_noncolorable_witness,
      `Erdos751Extension.lift_cycle,
      `Erdos751Extension.close_cycles_of_not_three_colorable,
      `Erdos751Extension.close_cycle_lengths,
      `Erdos751Extension.not_three_separated,
      `Erdos751Extension.answer,
      `Erdos751Extension.answer_with_girth]
    IO.println s!"Fresh target-closure replay: {targets.size} targets; {quotientCount} quotient primitives initialized as one kernel group"
    let fresh := (← mkEmptyEnvironment 0).toKernelEnv
    let (_, checked) ← StateRefT'.run (s := ({ env := fresh, remaining } : Replay.State)) do
      ReaderT.run (r := ({ newConstants := constants } : Replay.Context)) do
        Replay.replayConstant `Quot.lift
        for target in targets do
          if !constants.contains target then
            throw <| IO.userError s!"Missing target {target}"
          Replay.replayConstant target
        Replay.checkPostponedConstructors
        Replay.checkPostponedRecursors
    for target in targets do
      if (checked.env.find? target).isNone then
        throw <| IO.userError s!"Replay omitted target {target}"
    let good : Declaration := .thmDecl {
      name := `JSP751KernelReplay.validControl, levelParams := [],
      type := mkConst `True, value := mkConst `True.intro }
    match checked.env.addDeclCore 0 good (cancelTk? := none) with
    | .ok _ => IO.println "CONTROL: kernel accepted True from True.intro"
    | .error ex =>
      let message ← ex.toMessageData {} |>.toString
      throw <| IO.userError s!"Positive kernel control failed: {message}"
    let bad : Declaration := .thmDecl {
      name := `JSP751KernelReplay.invalidControl, levelParams := [],
      type := mkConst `False, value := mkConst `True.intro }
    match checked.env.addDeclCore 0 bad (cancelTk? := none) with
    | .ok _ => throw <| IO.userError "Kernel accepted an invalid proof of False"
    | .error _ => IO.println "CONTROL: kernel rejected False from True.intro"
    IO.println s!"Checked {remaining.size - checked.remaining.size} logical declarations in target dependency closures"
    IO.println "PASS: all nine targets and their complete transitive logical dependencies replayed from an empty environment"
