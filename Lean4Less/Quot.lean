import Batteries.Tactic.OpenPrivate
import Lean4Less.PExpr
import Lean4Less.Ext

namespace Lean4Less
open Lean4Less.TypeChecker

variable [Monad m] [MonadExcept KernelException M] (env : Environment)
  (meth : ExtMethodsR m)

open Lean

/--
Reduces the head application of a quotient eliminator as follows:

```
Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β

Quot.lift f h (Quot.mk r a) ... ⟶ f a ...
```

```
Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop} :
  (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q

Quot.ind p (Quot.mk r a) ... ⟶ p a ...
```
-/
def quotReduceRec [Monad m] (e : PExpr)
  : m (Option (PExpr × Option EExpr)) := do
  let fn := e.toExpr.getAppFn
  let fnType ← meth.inferTypePure 400 fn.toPExpr
  let .const fnName _ := e.toExpr.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.toExpr.getAppArgs
    if h : mkPos < args.size then
      let quotArg := args[mkPos].toPExpr
      let quotArgType ← meth.whnfPure 402 (← meth.inferTypePure 401 quotArg)
      let (mk, argEqmk?) ← meth.whnf 403 quotArg
      if !mk.toExpr.isAppOfArity ``Quot.mk 3 then return none
      let mkType ← meth.whnfPure 405 (← meth.inferTypePure 404 mk)
      let params := quotArgType.toExpr.getAppArgs
      let newParams := mkType.toExpr.getAppArgs
      let argsd ← replaceParams meth fnType params newParams args[params.size:mkPos]
      let mut newArgs := args.set! mkPos mk
      let mut map := Std.HashMap.insert default mkPos argEqmk?
      let mut i := 0
      for newParam in newParams do
        newArgs := newArgs.set! i newParam
        i := i + 1
      for (newArg, p?) in argsd do
        newArgs := newArgs.set! i newArg
        map := map.insert i p?
        i := i + 1
      let newe := (mkAppN fn $ newArgs).toPExpr
      let (.true, eEqnewe?) ← meth.isDefEqApp e newe map | unreachable!
      let mut r := Expr.app newArgs[argPos]! mk.toExpr.appArg! |>.toPExpr
      let elimArity := mkPos + 1
      if elimArity < newArgs.size then
        r := mkAppRange r elimArity newArgs.size newArgs |>.toPExpr
      return some (r, eEqnewe?)
    else return none
  if fnName == ``Quot.lift then cont 5 3
  else if fnName == ``Quot.ind then cont 4 3
  else return none
