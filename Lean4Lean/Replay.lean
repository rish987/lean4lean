import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Lean.Environment

open Lean

namespace Lean

def HashMap.keyNameSet (m : Std.HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}

namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

namespace NameSet

def ofList (names : List Name) : NameSet :=
  names.foldl (fun s n => s.insert n) {}

end NameSet

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstants' ++ match c.value? with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstants'
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

end Lean

def Lean.Declaration.name : Declaration → String
  | .axiomDecl d => s!"axiomDecl {d.name}"
  | .defnDecl d => s!"defnDecl {d.name}"
  | .thmDecl d => s!"thmDecl {d.name}"
  | .opaqueDecl d => s!"opaqueDecl {d.name}"
  | .quotDecl => s!"quotDecl"
  | .mutualDefnDecl d => s!"mutualDefnDecl {d.map (·.name)}"
  | .inductDecl _ _ d _ => s!"inductDecl {d.map (·.name)}"

namespace Lean4Lean

structure Context where
  opts : TypeCheckerOpts := {}
  newConstants : Std.HashMap Name ConstantInfo
  verbose := false
  compare := false

structure Data where
prfIrrelUses := 0
kLikeRedUses := 0

structure State where
  env : Environment
  data : Data := {}
  printNewLine := false
  numToCheck : Nat
  numChecked : Nat := 0
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

def Ansi.resetLine : String :=
  "\x1B[2K\r"

def maybePrintln : M Unit := do
  if (← get).printNewLine then
    IO.println ""
  modify fun s => {s with printNewLine := false}

def println (m : String) : M Unit := do
  maybePrintln
  IO.println m

def print (m : String) : M Unit := do
  maybePrintln
  IO.print m

def printProgress (op : String := "typecheck") (name : Option String := none) : M Unit := do
  let numToCheck := (← get).numToCheck
  let numChecked := (← get).numChecked
  let curr := (name.map fun n => s!" (current: {n})").getD ""
  IO.print s!"{Ansi.resetLine}[{numChecked}/{numToCheck}] ({(numChecked  * 100) / numToCheck}%) constants {op}ed{curr}"
  modify fun s => {s with printNewLine := true}
  let stdout ← IO.getStdout
  stdout.flush

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `KernelException`. -/
def throwKernelException (ex : KernelException) : M α := do
    let ctx := { fileName := "", options := pp.match.set (pp.rawOnError.set {} true) false, fileMap := default }
    let state := { env := (← get).env }
    Prod.fst <$> (Lean.Core.CoreM.toIO · ctx state) do Lean.throwKernelException ex

/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) (verbose := false) (allowAxiomReplace := false) : M Unit := do
  if (← read).verbose then
    println s!"adding {d.name}"
  let t1 ← IO.monoMsNow
  match (← get).env.addDecl' d (← read).opts allowAxiomReplace with
  | .ok (env, data) =>
    if data.usedKLikeReduction then
      if verbose then
        println s!"{d.name} used K-like reduction"
      modify fun s => {s with data := {s.data with kLikeRedUses := s.data.kLikeRedUses + 1}}
    if data.usedProofIrrelevance then
      if verbose then
        println s!"{d.name} used proof irrelevance"
      modify fun s => {s with data := {s.data with prfIrrelUses := s.data.prfIrrelUses + 1}}
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      if (← read).compare then
        let t3 ← match (← get).env.addDecl {} d with
        | .ok _ => IO.monoMsNow
        | .error ex => throwKernelException ex
        if (t2 - t1) > 2 * (t3 - t2) then
          println
            s!"{(← get).env.mainModule}:{d.name}: lean took {t3 - t2}, lean4lean took {t2 - t1}"
        else
          println s!"{(← get).env.mainModule}:{d.name}: lean4lean took {t2 - t1}"
      else
        println s!"{(← get).env.mainModule}:{d.name}: lean4lean took {t2 - t1}"
    modify fun s => { s with env := env }
  | .error ex =>
    throwKernelException ex

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal




mutual

partial def getDepConsts (newConstants : Std.HashMap Name ConstantInfo) (names : List Name) : IO NameSet := do
  let rec loop ret names := do
    let mut ret := ret
    for name in names do
      if let none := ret.find? name then
        let acc' := ret.insert name
        let some ci := newConstants[name]? | unreachable!
        ret ← loop acc' ci.getUsedConstants.toList
    pure ret
  loop default names

/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) (addDeclFn' : Declaration → M Unit) (printProgress? : Bool := false) (op : String := "typecheck") : M Unit := do
  let postAddDecl := do
    modify fun s => {s with numChecked := s.numChecked + 1}
    if printProgress? then
      printProgress op

  let preAddDecl n := do
    if printProgress? then
      printProgress op n

  let addDeclFn := fun decl => do
    preAddDecl decl.name
    try
      addDeclFn' decl
    catch e =>
      dbg_trace s!"Error in {decl.name}"
      throw e
    postAddDecl

  if ← isTodo name then
    -- dbg_trace s!"Processing deps: {name}"

    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstants addDeclFn' printProgress? (op := op)
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info =>
        addDeclFn (Declaration.defnDecl   info)
      | .thmInfo    info =>
        addDeclFn (Declaration.thmDecl    info)
      | .axiomInfo  info =>
        addDeclFn (Declaration.axiomDecl  info)
      | .opaqueInfo info =>
        addDeclFn (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants.get! n)
        for o in all do
          -- There is exactly one awkward special case here:
          -- `String` is a primitive type, which depends on `Char.ofNat` to exist
          -- because the kernel treats the existence of the `String` type as license
          -- to use string literals, which use `Char.ofNat` internally. However
          -- this definition is not transitively reachable from the declaration of `String`.
          if o.name == ``String then replayConstant ``Char.ofNat addDeclFn' (op := op)
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants.get! n))
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants addDeclFn' (op := op)
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDeclFn (Declaration.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        postAddDecl
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        postAddDecl
      | .quotInfo _ =>
        addDeclFn (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) (addDeclFn : Declaration → M Unit) (printProgress? : Bool := false) (op : String := "typecheck") : M Unit := do
  for n in names do replayConstant n addDeclFn printProgress? op

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, (← read).newConstants.get? ctor with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, (← read).newConstants.get? ctor with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

variable (addDeclFn : Declaration → M Unit)

/-- "Replay" some constants into an `Environment`, sending them to the kernel for checking. -/
def replay (ctx : Context) (env : Environment) (onlyConsts? : Option (List Name) := none) (decl : Option Name := none) (printProgress : Bool := false) (op : String := "typecheck") : IO Environment := do 
  let mut remaining : NameSet := ∅
  let mut numToCheck : Nat := 0
  for (n, ci) in ctx.newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
      numToCheck := numToCheck + 1
  if let some onlyConsts := onlyConsts? then
    numToCheck := (← getDepConsts ctx.newConstants onlyConsts).size
  let (_, s) ← StateRefT'.run (s := { env, remaining, numToCheck }) do
    ReaderT.run (r := ctx) do
      match decl with
      | some d => replayConstant d addDeclFn (op := op)
      | none =>
        let tryReplay n :=
          try
            replayConstant n addDeclFn printProgress op
          catch
          | e => 
            IO.eprintln s!"Error {op}ing constant `{n}`: {e.toString}"
            throw e
        if let some onlyConsts := onlyConsts? then
          for n in onlyConsts do
            tryReplay n
        else
          for n in remaining do
            tryReplay n
      checkPostponedConstructors
      checkPostponedRecursors
  if s.printNewLine then
    IO.println ""
  if printProgress then
    IO.println s!"{numToCheck} total constants typechecked"
    IO.println s!"-- {s.data.prfIrrelUses} used proof irrelevance"
    IO.println s!"-- {s.data.kLikeRedUses} used k-like reduction"
  return s.env

unsafe def replayFromImports (module : Name) (verbose := false) (compare := false) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports
    |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
  let env ← finalizeImport s #[{module}] {} 0
  let env := env.setMainModule module
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let env' ← replay addDeclFn { newConstants, verbose, compare } env
  env'.freeRegions
  region.free

unsafe def replayFromInit'' (module : Name) (initEnv : Environment) (newConstants : Std.HashMap Name ConstantInfo) (f : Environment → IO Unit) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
    let ctx := { newConstants, verbose, compare, opts }
    let env ← replay addDeclFn ctx (initEnv.setMainModule module) (onlyConsts? := onlyConsts?) (op := op) (decl := decl) (printProgress := true)
    f env

unsafe def replayFromInit' (module : Name) (initEnv : Environment) (f : Environment → IO Unit) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
  Lean.withImportModules #[{module}] {} 0 fun env => do
    let mut newConstants := initEnv.constants.fold (init := env.constants.map₁) fun acc const _info =>
      if let some _info' := acc[const]? then
        -- assert! _info == _info' --TODO sanity check; need to derive BEq?
        acc.erase const
      else acc
    replayFromInit'' addDeclFn module (initEnv.setMainModule module) newConstants f (onlyConsts? := onlyConsts?) (op := op) (decl := decl) (verbose := verbose) (compare := compare) (opts := opts)

unsafe def replayFromEnv (module : Name) (initEnv : Environment) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
  let mut newConstants := initEnv.constants.map₁
  replayFromInit'' addDeclFn module (← mkEmptyEnvironment) newConstants (fun _ => pure ()) (onlyConsts? := onlyConsts?) (op := op) (decl := decl) (verbose := verbose) (compare := compare) (opts := opts)

unsafe def replayFromInit (module : Name) (initEnv : Environment) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
  discard <| replayFromInit' addDeclFn module initEnv (fun _ => pure ()) onlyConsts? op verbose compare decl opts

unsafe def replayFromFresh' (module : Name) (f : Environment → IO Unit) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
  replayFromInit' addDeclFn module (← mkEmptyEnvironment) f (onlyConsts? := onlyConsts?) (op := op) (verbose := verbose) (compare := compare) (decl := decl) (opts := opts)

unsafe def replayFromFresh (module : Name) (onlyConsts? : Option (List Name) := none) (op : String := "typecheck")
    (verbose := false) (compare := false) (decl : Option Name := none) (opts : TypeCheckerOpts := {}) : IO Unit := do
  replayFromInit addDeclFn module (← mkEmptyEnvironment) (onlyConsts? := onlyConsts?) (op := op) (verbose := verbose) (compare := compare) (decl := decl) (opts := opts)

end Lean4Lean

register_option l4l.check : Bool := {
  defValue := false
  group := "l4l"
  descr := "run secondary Lean4Lean typechecker on definintions"
}
