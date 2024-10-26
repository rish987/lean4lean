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
  isDefEqLean : PExpr → PExpr → m Bool
  whnf  : Nat → PExpr → m (PExpr × Option EExpr)
  whnfPure  : Nat → PExpr → m PExpr
  mkId  : Nat → m Name
  inferTypePure : Nat → PExpr → m PExpr
  inferType : Nat → Expr → m (PExpr × Option PExpr)
  withPure : {T : Type} → m T → m T
  mkHRefl : Level → PExpr → PExpr → m EExpr
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

namespace TypeChecker

variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (env : Environment)
  (meth : ExtMethods m)

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def rctx [MonadReaderOf Context m] : m Context := (readThe Context)

@[inline] def withEqFVar [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) m] (idt ids : FVarId) (eq : FVarDataE) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x
