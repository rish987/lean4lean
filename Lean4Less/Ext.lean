import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr

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
  isDefEqLean : Expr → Expr → m Bool
  whnf  : Nat → PExpr → m (PExpr × Option EExpr)
  whnfPure  : Nat → PExpr → m PExpr
  mkId  : Nat → Expr → m Name
  mkId'  : Nat → LocalContext → Expr → m Name
  mkIdNew : Nat → m Name
  inferTypePure : Nat → PExpr → m PExpr
  inferType : Nat → Expr → m (PExpr × Option PExpr)
  withPure : {T : Type} → m T → m T
  mkHRefl : Nat → Level → PExpr → PExpr → m EExpr
  getTypeLevel : PExpr → m (Level × PExpr)
  ensureSortCorePure : PExpr → Expr → m PExpr
  appPrfIrrelHEq : PExpr → PExpr → EExpr → PExpr → PExpr → m EExpr
  appPrfIrrel : PExpr → PExpr →  PExpr → m EExpr
  appHEqTrans? : PExpr → PExpr → PExpr → Option EExpr → Option EExpr → m (Option EExpr)
  trace : String → m Unit
  ttrace : String → m Unit
  callId : m Nat
  numCalls : m Nat
  shouldTTrace : m Bool

structure ExtMethodsR (m : Type → Type u) extends ExtMethods m where
  isDefEqApp' : PExpr → PExpr → Std.HashMap Nat (Option EExpr) → m (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))
  isDefEqApp : PExpr → PExpr → Std.HashMap Nat (Option EExpr) → m (Bool × Option EExpr)
  smartCast : Nat → PExpr → PExpr → PExpr → m (Bool × PExpr)
  maybeCast (n : Nat) (p? : Option EExpr) (typLhs typRhs e : PExpr) : m PExpr
  isDefEqProofIrrel' : PExpr → PExpr → PExpr → PExpr → Option EExpr → m (Option EExpr)

namespace TypeChecker

variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (env : Environment)
  (meth : ExtMethods m)

def replaceParams (meth : ExtMethodsR m) (fType : Expr) (params : Array Expr) (newParams : Array Expr) (args : Array Expr) : m (Array (PExpr × Option EExpr)) := do
  let numParams := params.size
  let rec loop1 (type origType : Expr) (n : Nat) := do
    match (← meth.whnfPure 116 type.toPExpr).toExpr, (← meth.whnfPure 117 origType.toPExpr).toExpr, n with
  | .forallE _ _ newBody _, .forallE _ _ body _, m + 1 => 
    let idx := numParams - n
    let param := params[idx]!
    let newParam := newParams[idx]!
    loop1 (newBody.instantiate1 newParam) (body.instantiate1 param) m
  | newBody, body, m =>
    assert! m == 0
    pure (newBody, body)
  let (newType', type') ← loop1 fType fType numParams

  let rec loop2 (newType type : Expr) (n : Nat) ret := do
    match (← meth.whnfPure 118 newType.toPExpr).toExpr, (← meth.whnfPure 119 type.toPExpr).toExpr, n with
    | .forallE _ newDom newBody _, .forallE _ dom body _, m + 1 => 
      let idx := args.size - n
      let arg := args[idx]!.toPExpr
      let (true, newArg) ← meth.smartCast 101 dom.toPExpr newDom.toPExpr arg | unreachable!
      -- _ ← meth.inferTypePure 5000 newArg -- sanity check TODO remove
      let (true, argEqnewArg?) ← meth.isDefEq 120 arg newArg | unreachable!
      let ret := ret.push (newArg, argEqnewArg?)
      loop2 (newBody.instantiate1 newArg) (body.instantiate1 arg) m ret
    | _, _, m =>
      assert! m == 0
      pure ret

  let ret ← loop2 newType' type' args.size #[]
  pure ret


@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def rctx [MonadReaderOf Context m] : m Context := (readThe Context)

@[inline] def withEqFVar [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) m] (idt ids : FVarId) (eq : FVarDataE) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x
