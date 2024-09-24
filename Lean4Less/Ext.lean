import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr

namespace Lean4Less
open Lean

def cond : Expr → Expr → Bool
| .forallE _ _ tbod _, .forallE _ _ sbod _ => cond tbod sbod
| tbod, sbod=> 
  let tf := tbod.getAppFn
  let sf := sbod.getAppFn
  let tArgs := tbod.getAppArgs
  let sArgs := sbod.getAppArgs

  if let .const `Eq _ := tf then if let .const `Eq _ := sf then
    if tArgs.size == 3 then
      let tArg := tArgs[2]!
      let sArg := sArgs[2]!
      if tArg.isApp then if let .const `Std.DHashMap.get? _ := tArg.withApp fun k _ => k then
        if sArg.isApp then if let .const `Std.DHashMap.Internal.Raw₀.get? _ := sArg.withApp fun k _ => k then
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
  isDefEq : PExpr → PExpr → m (Bool × Option EExpr)
  isDefEqPure : PExpr → PExpr → m Bool
  whnf  : PExpr → m (PExpr × Option EExpr)
  whnfPure  : PExpr → Nat → m PExpr
  inferTypePure : PExpr → Nat → m PExpr
  withPure : {T : Type} → m T → m T
  mkHRefl : Level → PExpr → PExpr → m EExpr
  getTypeLevel : PExpr → m (Level × PExpr)
  ensureSortCorePure : PExpr → Expr → m PExpr
  appPrfIrrelHEq : PExpr → PExpr → EExpr → PExpr → PExpr → m EExpr
  appPrfIrrel : PExpr → PExpr →  PExpr → m EExpr
  appHEqTrans? : PExpr → PExpr → PExpr → Option EExpr → Option EExpr → m (Option EExpr)

namespace TypeChecker

variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (env : Environment)
  (meth : ExtMethods m)

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withEqFVar [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (idt ids : FVarId) (eq : (FVarId × FVarId)) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x
