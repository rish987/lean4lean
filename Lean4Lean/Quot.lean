import Std.Tactic.OpenPrivate
import Lean4Lean.Environment.Basic
import Lean4Lean.Expr
import Lean4Lean.PExpr
import Lean4Lean.LocalContext

namespace Lean

open private add markQuotInit from Lean.Environment

abbrev ExprBuildT (m) := ReaderT LocalContext <| ReaderT NameGenerator m

def ExprBuildT.run [Monad m] (x : ExprBuildT m α) : m α := x {} {}

instance : MonadLocalNameGenerator (ExprBuildT m) where
  withFreshId x c ngen := x ngen.curr c ngen.next

def checkEqType (env : Environment) : Except KernelException Unit := do
  let fail {α} (s : String) : Except KernelException α :=
    throw <| .other s!"failed to initialize quot module, {s}"
  let .inductInfo info ← env.get ``Eq | fail "environment does not have 'Eq' type"
  let [u] := info.levelParams | fail "unexpected number of universe params at 'Eq' type"
  let [eqRefl] := info.ctors | fail "unexpected number of constructors for 'Eq' type"
  ExprBuildT.run do
    withLocalDecl `α (.sort (.param u)) .implicit fun α => do
      if info.type != ((← read).mkForall #[α] <| .arrow α <| .arrow α .prop) then
        fail "'Eq' has an expected type"
    let info ← env.get eqRefl
    let [u] := info.levelParams
      | fail "unexpected number of universe params at 'Eq' type constructor"
    withLocalDecl `α (.sort (.param u)) .implicit fun α => do
      withLocalDecl `a α .default fun a => do
        if info.type != ((← read).mkForall #[α, a] <| mkApp3 (.const ``Eq [.param u]) α a a) then
          fail "unexpected type for 'Eq' type constructor"

def Environment.addQuot (env : Environment) : Except KernelException Environment := do
  if env.header.quotInit then return env
  checkEqType env
  ExprBuildT.run do
  let u := .param `u
  withLocalDecl `α (.sort u) .implicit fun α => do
  let env ← withLocalDecl `r (.arrow α (.arrow α .prop)) .default fun r => do
    -- constant Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
    let env := add env <| .quotInfo {
      name := ``Quot, kind := .type, levelParams := [`u]
      type := (← read).mkForall #[α, r] <| .sort u
    }
    withLocalDecl `a α .default fun a => do
      -- constant Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
      return add env <| .quotInfo {
        name := ``Quot.mk, kind := .ctor, levelParams := [`u]
        type := (← read).mkForall #[α, r, a] <| mkApp2 (.const ``Quot [u]) α r
      }
  withLocalDecl `r (.arrow α (.arrow α .prop)) .implicit fun r => do
  let quot_r := mkApp2 (.const ``Quot [u]) α r
  withLocalDecl `a α .default fun a => do
  let v := .param `v
  let env ← withLocalDecl `β (.sort v) .implicit fun β => do
    withLocalDecl `f (.arrow α β) .default fun f => do
    withLocalDecl `b α .default fun b => do
    let rab := mkApp2 r a b
    let fa_eq_fb := mkApp3 (.const ``Eq [v]) β (.app f a) (.app f b)
    let sanity := (← read).mkForall #[a, b] <| .arrow rab fa_eq_fb
    -- constant Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
    --   (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    return add env <| .quotInfo {
      name := ``Quot.lift, kind := .lift, levelParams := [`u, `v]
      type := (← read).mkForall #[α, r, β, f] <| .arrow sanity <| .arrow quot_r β
    }
  let quotMk_a := mkApp3 (.const ``Quot.mk [u]) α r a
  withLocalDecl `β (.arrow quot_r .prop) .implicit fun β => do
  let all_quot := (← read).mkForall #[a] <| .app β quotMk_a
  withLocalDecl `q quot_r .implicit fun q => do
  -- constant Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop} :
  --   (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q
  let env := add env <| .quotInfo {
    name := ``Quot.ind, kind := .ind, levelParams := [`u]
    type := (← read).mkForall #[α, r, β] <|
      .forallE `mk all_quot ((← read).mkForall #[q] <| .app β q) .default
  }
  return markQuotInit env

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
def quotReduceRec [Monad m] (e : PExpr) (whnf : PExpr → m (PExpr × Option PExpr))
  (isDefEqApp : PExpr → PExpr → Nat × (Option PExpr) → m (Bool × Option PExpr)) : m (Option (PExpr × Option PExpr)) := do
  let fn := e.toExpr.getAppFn
  let .const fnName _ := e.toExpr.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.toExpr.getAppArgs
    if h : mkPos < args.size then
      let (mk, argEqmk?) ← whnf args[mkPos].toPExpr
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
