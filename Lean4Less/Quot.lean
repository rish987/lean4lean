import Batteries.Tactic.OpenPrivate
import Lean4Less.PExpr

namespace Lean4Less

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
def quotReduceRec [Monad m] (e : PExpr) (whnf : PExpr → m (PExpr × Option EExpr))
  (isDefEqApp : PExpr → PExpr → Nat × (Option EExpr) → m (Bool × Option EExpr)) : m (Option (PExpr × Option EExpr)) := do
  let fn := e.toExpr.getAppFn
  let .const fnName _ := e.toExpr.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.toExpr.getAppArgs
    if h : mkPos < args.size then
      let (mk, argEqmk?) ← whnf $ args[mkPos].toPExpr
      -- TODO can we really assume that the type of args[mkPos] did not change after whnf?
      -- if not, need to call infer on `eMk` to cast `mk` as necessary
      let eMk := (mkAppN fn $ args.set! mkPos mk).toPExpr
      let (.true, eEqe'?) ← isDefEqApp e eMk (mkPos, argEqmk?) | unreachable!
      if !mk.toExpr.isAppOfArity ``Quot.mk 3 then return none
      let mut r := Expr.app args[argPos]! mk.toExpr.appArg! |>.toPExpr
      let elimArity := mkPos + 1
      if elimArity < args.size then
        r := mkAppRange r elimArity args.size args |>.toPExpr
      return some (r, eEqe'?)
    else return none
  if fnName == ``Quot.lift then cont 5 3
  else if fnName == ``Quot.ind then cont 4 3
  else return none
