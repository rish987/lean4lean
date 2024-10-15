import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Lean.TypeChecker

namespace Lean4Less
open Lean

-- def cond : Expr → Expr → Bool
-- | .forallE _ _ tbod _, .forallE _ _ sbod _ => cond tbod sbod
-- | tbod, sbod => 
--   let tf := tbod.getAppFn
--   let sf := sbod.getAppFn
--   let tArgs := tbod.getAppArgs
--   let sArgs := sbod.getAppArgs
--
--   if let .const `Eq _ := tf then -- if let .const `B _ := sf then
--     if true then
--       if let .const `WellFounded.fix _ := tArgs[1]!.getAppFn then -- if let .const `B _ := sf then
--         true
--       else false
--     else false
--   else false
--
def _cond : Nat → Expr → Bool
| n + 1, .lam _ _ tbod _ => _cond n tbod
| 0, tbod => 
  if false then
    false
  else
    let tf := tbod.getAppFn
    let tArgs := tbod.getAppArgs

    if let .const ``PSigma.casesOn _ := tf then -- if let .const `B _ := sf then
      if tArgs.size == 5 then
        if true then -- if let .const `B _ := sf then
          true
        else false
      else false
    else false
| _, _ => false
def cond : Expr → Bool
:= _cond 0

def cond' (ta sa : Expr) : Bool :=
  if let .lam .. := ta.getAppFn then if let .const `S.b _ := sa.getAppFn then
      if ta.getAppArgs.size == 1 then
        let tArgs := ta.getAppArgs
        let sArgs := sa.getAppArgs
        let tArg := tArgs[0]!
        let sArg := sArgs[0]!
        if tArg.isApp then if let .const `K.rec _ := tArg.withApp fun k _ => k then
          if sArg.isApp then if let .const `K.rec _ := sArg.withApp fun k _ => k then
            true
          else false
          else false
          else false
          else false
        else false
      else false
    else false

section

structure ExtMethods (m : Type → Type u) where
  isDefEq : Nat → PExpr → PExpr → m (Bool × Option EExpr)
  isDefEqPure : Nat → PExpr → PExpr → m Bool
  isDefEqPure' : Nat → PExpr → PExpr → Nat → m Bool
  isDefEqCore : Nat → PExpr → PExpr → m (Bool × Option EExpr)
  whnf  : Nat → PExpr → m (PExpr × Option EExpr)
  whnf'  : Nat → PExpr → Bool → m (PExpr × Option EExpr)
  whnfCore : Nat → PExpr → Bool → Bool → m (PExpr × Option EExpr)
  whnfPure  : Nat → PExpr → m PExpr
  quickIsDefEq : Nat → PExpr → PExpr → Bool → m (LBool × Option EExpr)
  mkId  : Nat → m Name
  inferTypePure : Nat → PExpr → m PExpr
  withPure : {T : Type} → m T → m T
  mkHRefl : Level → PExpr → PExpr → m EExpr
  getTypeLevel : PExpr → m (Level × PExpr)
  ensureSortCorePure : PExpr → Expr → m PExpr
  appPrfIrrelHEq : PExpr → PExpr → EExpr → PExpr → PExpr → m EExpr
  appPrfIrrel : PExpr → PExpr →  PExpr → m EExpr
  appHEqTrans? : PExpr → PExpr → PExpr → Option EExpr → Option EExpr → m (Option EExpr)
  appHEqSymm? : PExpr → PExpr → Option EExpr → m (Option EExpr)
  isPropPure : PExpr → m Bool
  trace : String → m Unit

namespace TypeChecker

abbrev InferCache := Std.HashMap Expr (PExpr × Option PExpr)
abbrev InferCacheP := Std.HashMap Expr (PExpr)

structure State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCacheP := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : Std.HashMap PExpr (PExpr × Option EExpr) := {}
  whnfCache : Std.HashMap (PExpr × Bool) (PExpr × Option EExpr) := {}
  isDefEqCache : Std.HashMap (PExpr × PExpr) EExpr := Std.HashMap.empty (capacity := 1000)
  fvarRegistry : Std.HashMap Name Nat := {} -- for debugging purposes
  eqvManager : EquivManager := {}
  numCalls : Nat := 0
  leanMinusState : Lean.TypeChecker.State := {}
  failure : Std.HashSet (Expr × Expr) := {}

inductive CallData where
|  isDefEqCore : PExpr → PExpr → CallData
|  isDefEqCorePure : PExpr → PExpr → CallData
|  quickIsDefEq : PExpr → PExpr → Bool → CallData
|  whnfCore (e : PExpr) (cheapK : Bool) (cheapProj : Bool) : CallData
|  whnf (e : PExpr) (cheapK : Bool) : CallData
|  whnfPure (e : PExpr) : CallData
|  inferType (e : Expr) (dbg : Bool) : CallData
|  inferTypePure (e : PExpr) : CallData
deriving Inhabited

instance : ToString CallData where
toString
| .isDefEqCore t s     => s!"isDefEqCore ({t}) ({s})"
| .isDefEqCorePure t s => s!"isDefEqCorePure ({t}) ({s})"
| .quickIsDefEq t s h  => s!"quickIsDefEq ({t}) ({s}) {h}"
| .whnfCore e k p      => s!"whnfCore ({e}) {k} {p}"
| .whnf e k            => s!"whnf ({e}) {k}"
| .whnfPure e          => s!"whnfPure ({e})"
| .inferType e d       => s!"inferType ({e}) ({d})"
| .inferTypePure e     => s!"inferTypePure ({e})"


def CallData.name : CallData → String
| .isDefEqCore ..     => "isDefEqCore"
| .isDefEqCorePure .. => "isDefEqCorePure"
| .quickIsDefEq ..    => "quickIsDefEq"
| .whnfCore ..        => "whnfCore"
| .whnf ..            => "whnf"
| .whnfPure ..        => "whnfPure"
| .inferType ..       => "inferType"
| .inferTypePure ..   => "inferTypePure"

@[reducible]
def CallDataT : CallData → Type
| .isDefEqCore ..     => Bool × Option EExpr
| .isDefEqCorePure .. => Bool
| .quickIsDefEq ..    => LBool × Option EExpr
| .whnfCore ..        => PExpr × Option EExpr
| .whnf ..            => PExpr × Option EExpr
| .whnfPure ..        => PExpr
| .inferType ..       => PExpr × Option PExpr
| .inferTypePure ..   => PExpr

structure Context where
  env : Environment
  pure : Bool := false -- (for debugging purposes)
  forallOpt : Bool := true -- (for debugging purposes)
  const : Name -- (for debugging purposes)
  lctx : LocalContext := {}
  /--
  Mapping from free variables to proofs of their equality,
  introduced by isDefEqLambda.
  -/
  eqFVars : Std.HashMap (FVarId × FVarId) (LocalDecl × EExpr) := {}
  safety : DefinitionSafety := .safe
  callId : Nat := 0
  dbgCallId : Option Nat := none
  cheapK := false
  callStack : Array (Nat × CallData) := #[]
  lparams : List Name := []


variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (env : Environment)
  (meth : ExtMethods m)

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withEqFVar [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (LocalDecl × EExpr)) m] (idt ids : FVarId) (eq : (LocalDecl × EExpr)) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its `ConstantInfo` if so.
-/
def isDelta (env : Environment) (e : PExpr) : Option ConstantInfo := do
  if let .const c _ := e.toExpr.getAppFn then
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its value (instantiated by level parameters)
if so.
-/
def unfoldDefinitionCore (env : Environment) (e : PExpr) : Option PExpr := do
  if let .const _ ls := e.toExpr then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        -- can assume that any constant value added to the environment has been patched
        return d.instantiateValueLevelParams! ls |>.toPExpr
  none

/--
Unfolds the definition at the head of the application `e` (or `e` itself if it
is not an application).
-/
def unfoldDefinition (env : Environment) (e : PExpr) : Option PExpr := do
  if e.toExpr.isApp then
    let f0 := e.toExpr.getAppFn
    if let some f := unfoldDefinitionCore env f0.toPExpr then
      let rargs := e.toExpr.getAppRevArgs
      return f.toExpr.mkAppRevRange 0 rargs.size rargs |>.toPExpr
    none
  else
    unfoldDefinitionCore env e
