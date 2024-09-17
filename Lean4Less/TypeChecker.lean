import Lean4Less.Quot
import Lean4Less.Inductive.Reduce
import Lean4Less.EExpr

import Lean4Lean.Environment
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Util
import Lean4Lean.Instantiate
import Lean4Lean.TypeChecker

namespace Lean4Less
open Lean

abbrev InferCache := HashMap Expr (PExpr × Option PExpr)
abbrev InferCacheP := HashMap Expr (PExpr)

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCacheP := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap (PExpr × Option EExpr) := {}
  whnfCache : ExprMap (PExpr × Option EExpr) := {}
  eqvManager : EquivManager := {}
  failure : HashSet (Expr × Expr) := {}

structure TypeChecker.Context where
  env : Environment
  pure : Bool := false -- (for debugging purposes)
  const : Name -- (for debugging purposes)
  lctx : LocalContext := {}
  /--
  Mapping from free variables to proofs of their equality,
  introduced by isDefEqLambda.
  -/
  eqFVars : HashMap (FVarId × FVarId) FVarId := {}
  safety : DefinitionSafety := .safe
  lparams : List Name := []

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException
abbrev MPE := M (PExpr × Option PExpr)
abbrev MEE := M (PExpr × Option EExpr)
abbrev MB := M (Bool × Option EExpr)

def M.run (env : Environment) (const : Name) (safety : DefinitionSafety := .safe) (lctx : LocalContext := {})
    (x : M α) : Except KernelException α :=
  x { env, safety, lctx, const } |>.run' {}

instance : MonadEnv M where
  getEnv := return (← read).env
  modifyEnv _ := pure ()

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

instance (priority := low) : MonadWithReaderOf (HashMap (FVarId × FVarId) FVarId) M where
  withReader f := withReader fun s => { s with eqFVars := f s.eqFVars }

structure Methods where
  isDefEqCore : PExpr → PExpr → MB
  isDefEqCorePure : PExpr → PExpr → M Bool
  whnfCore (e : PExpr) (cheapRec := false) (cheapProj := false) : MEE
  whnf (e : PExpr) : MEE
  whnfPure (e : PExpr) : M PExpr
  inferType (e : Expr) : MPE
  inferTypePure (e : PExpr) : M PExpr

abbrev RecM := ReaderT Methods M
abbrev RecPE := RecM (PExpr × (Option PExpr))
abbrev RecEE := RecM (PExpr × (Option EExpr))
abbrev RecB := RecM (Bool × (Option EExpr))
abbrev RecLB := RecM (LBool × (Option EExpr))

def runLeanMinus (M : Lean.TypeChecker.M T) : RecM T := do
  Lean.TypeChecker.M.run' (← getEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := false, proofIrrelevance := false}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (ngen := (← get).ngen) M

inductive ReductionStatus where
  | continue (nltn nlsn : PExpr) (pltnEqnltn? plsnEqnlsn? : Option EExpr)
  | unknown (ltn lsn : PExpr) (tnEqltn? snEqlsn? : Option EExpr)
  | notDelta
  | bool (b : Bool) (p?: Option EExpr)
deriving Inhabited

namespace Inner

/--
Reduces `e` to its weak-head normal form.
-/
def whnf (e : PExpr) : RecEE := fun m => m.whnf e

def whnfPure (e : PExpr) : RecM PExpr := fun m => m.whnfPure e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withEqFVar [MonadWithReaderOf (HashMap (FVarId × FVarId) FVarId) m] (idt ids : FVarId) (eq : FVarId) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x

@[inline] def withPure [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with pure := true}) x

/--
Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not,
throws an error with `s` (the expression required be a sort).
NOTE: e must be a patched expression
-/
def ensureSortCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isSort e then return (e, none)
  let (e, p?) ← whnf e
  if e.toExpr.isSort then return (e, p?)
  throw <| .typeExpected (← getEnv) default s

def assert (n : Nat) (b : Bool) : RecM Unit := do if not b then throw $ .other s!"assert fail {n}"

@[inherit_doc ensureSortCore]
def ensureSortCorePure (e : PExpr) (s : Expr) : RecM PExpr := do
  let (s, p?) ← (ensureSortCore e s)
  assert 1 $ p? == none
  return s

/--
Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not,
throws an error with `s := f a` (the application requiring `f` to be of
function type).
-/
def ensureForallCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isForall e then return (e, none)
  let (e, p?) ← whnf e
  if e.toExpr.isForall then return (e, p?)
  throw <| .funExpected (← getEnv) (← getLCtx) s

@[inherit_doc ensureForallCore]
def ensureForallPure (e : PExpr) (s : Expr) : RecM PExpr := do
  if Expr.isForall e then return e
  let e ← whnfPure e
  if e.toExpr.isForall then return e
  throw <| .funExpected (← getEnv) (← getLCtx) s

/--
Checks that `l` does not contain any level parameters not found in the context `tc`.
-/
def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}' {tc.lparams}"

def inferFVar (tc : Context) (name : FVarId) : Except KernelException PExpr := do
  if let some decl := tc.lctx.find? name then
    return decl.type.toPExpr
  throw <| .other "unknown free variable"

/--
Infers the type of `.const e ls`.
-/
def inferConstant (tc : Context) (name : Name) (ls : List Level) :
    Except KernelException PExpr := do
  let e := Expr.const name ls
  -- should be okay as the environment should only contain patched constants
  let info ← Environment.get tc.env name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if info.isUnsafe && tc.safety != .unsafe then
    throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
  if let .defnInfo v := info then
    if v.safety == .partial && tc.safety == .safe then
      throw <| .other
        s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
  for l in ls do
    checkLevel tc l
  return info.instantiateTypeLevelParams ls |>.toPExpr

/--
Infers the type of expression `e`. If `inferOnly := false`, this function will
throw an error if and only if `e` is not typeable according to Lean's
algorithmic typing judgment. Setting `inferOnly := true` optimizes to avoid
unnecessary checks in the case that `e` is already known to be well-typed.
-/
def inferType (e : Expr) : RecPE := fun m => m.inferType e

def inferTypePure (e : PExpr) : RecM PExpr := fun m => m.inferTypePure e

def getConst (n : Name) (lvls : List Level) : RecM Expr := do
  pure $ .const n lvls
/--
Gets the universe level of the sort that the type of `e` inhabits.
-/
def getTypeLevel (e : PExpr) : RecM (Level × PExpr) := do
  let eType ← inferTypePure e
  let eTypeSort ← inferTypePure eType
  let (eTypeSort', es?) ← ensureSortCore eTypeSort eType
  assert 4 $ es? == none
  pure (eTypeSort'.toExpr.sortLevel!, eType)

def appHEqSymm (t s : PExpr) (theqs : EExpr) : RecM EExpr := do
  let (lvl, tType) ← getTypeLevel t
  let sType ← inferTypePure s
  pure $ theqs.reverse t s tType sType lvl

def appHEqSymm? (t s : PExpr) (theqs? : Option EExpr) : RecM (Option EExpr) := do
  let some theqs := theqs? | return none
  appHEqSymm t s theqs

def smartCast (e tl tr : PExpr) (p : EExpr) : RecM PExpr := do
  let mkCast' n tl tr p e (prfVars prfVals : Array Expr) := do
    let sort ← inferTypePure tr.toPExpr
    let sort' ← ensureSortCorePure sort tl.toPExpr
    let p := p.toExpr.replaceFVars prfVars prfVals
    let lvl := sort'.toExpr.sortLevel!
    pure $ Lean.mkAppN (← getConst n [lvl]) #[tl, tr, p, e]

  let mkCast tl tr p e (prfVars prfVals : Array Expr) := do
    mkCast' `L4L.castHEq tl tr p e prfVars prfVals

  let rec loop e tl tr (lamVars prfVars prfVals : Array Expr) p : RecM Expr := do
    match e, tl, tr, p with
    | .lam n _ b bi, .forallE _ _ tbl .., .forallE _ tdr tbr .., .forallE forallData =>
      let {A, a, UaEqVx, extra, ..} := forallData
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id n tdr bi) do
        let v := .fvar id

        let (newPrfVars, newPrfVals, vCast) ←
          match extra with
          | .AB {B, b, vaEqb, hAB} =>
            let hBA ← appHEqSymm A B hAB
            let vCast ← mkCast B.toExpr A.toExpr hBA v prfVars prfVals
            let vCastEqv ← mkCast' `L4L.castOrigHEq B.toExpr A.toExpr hBA v prfVars prfVals
            pure (#[a.toExpr, b.toExpr, vaEqb.aEqb], #[vCast, v, vCastEqv], vCast)
          | _ => 
            pure (#[a.toExpr], #[v], v)
        let prfVars := prfVars ++ newPrfVars
        let prfVals := prfVals ++ newPrfVals

        let lamVars := lamVars.push v
        let b := b.instantiate1 vCast
        let tbl := tbl.instantiate1 vCast
        let tbr := tbr.instantiate1 v
        loop b tbl tbr lamVars prfVars prfVals UaEqVx
    | _, _, _, _ =>
      let cast ← mkCast tl tr p e prfVars prfVals
      pure $ (← getLCtx).mkLambda lamVars cast
  pure (← loop e.toExpr tl.toExpr tr.toExpr #[] #[] #[] p).toPExpr

def maybeCast (p? : Option EExpr) (typLhs typRhs e : PExpr) : RecM PExpr := do
  pure $ (← p?.mapM (fun (p : EExpr) => do smartCast e typLhs typRhs p)).getD e

/--
Infers the type of lambda expression `e`.
-/
def inferLambda (e : Expr) : RecPE := loop #[] false e where
  loop fvars domPatched : Expr → RecPE -- TODO OK that fvars is not `Array PExpr`?
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let (typ, d'?) ← inferType d
    let (typ', p?) ← ensureSortCore typ d
    let d' ← maybeCast p? typ typ' (d'?.getD d.toPExpr)

    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let e := e.instantiateRev fvars
    let (r, e'?) ← inferType e
    let e' := e'?.getD e.toPExpr
    let r := r.toExpr.cheapBetaReduce |>.toPExpr
    let (rSort, r'?) ← inferType r
    let (rSort', p?) ← ensureSortCore rSort r -- TODO need to test this
    assert 2 $ r'? == none
    let r' ← maybeCast p? rSort rSort' r

    let patch ←
      if domPatched || e'?.isSome then do
        pure $ some $ ((← getLCtx).mkLambda fvars e').toPExpr
      else 
        pure none
    -- TODO only return .some if any of the fvars had domains that were patched, or if e'? := some e'
    return (( (← getLCtx).mkForall fvars r').toPExpr, patch)

-- def inferLambdaPure (e : PExpr) : RecM PExpr := sorry

/--
Infers the type of for-all expression `e`.
-/
def inferForall (e : Expr) : RecPE := loop #[] #[] false e where
  loop fvars us domPatched : Expr → RecPE
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let (t, d'?) ← inferType d
    let (t', p?) ← ensureSortCore t d
    let lvl := t'.toExpr.sortLevel!
    let d' ← maybeCast p? t t' (d'?.getD d.toPExpr)

    let us := us.push lvl
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let e := e.instantiateRev fvars
    let (r, e'?) ← inferType e
    let (r', p?) ← ensureSortCore r e
    let lvl := r'.toExpr.sortLevel!
    let e' ← maybeCast p? r r' (e'?.getD e.toPExpr)

    let patch? ←
      if domPatched || e'?.isSome || p?.isSome then do
        pure $ .some $ ((← getLCtx).mkForall fvars e').toPExpr
      else
        pure none
    return ((Expr.sort <| us.foldr mkLevelIMax' lvl ).toPExpr, patch?)

-- def inferForallPure (e : PExpr) : RecM PExpr := sorry

/--
Returns whether `t` and `s` are definitionally equal according to Lean's
algorithmic definitional equality judgment.

NOTE: This function does not do any typechecking of its own on `t` and `s`.
So, when this is used as part of a typechecking routine, it is expected that
they are already well-typed (that is, that `check t` and `check s` 
did not/would not throw an error). This ensures in particular that any calls to
`inferType e (inferOnly := false)` on subterms `e` would not fail, so we know
that `e` types as the return value of `inferType e (inferOnly := true)`.
-/
def isDefEqCore (t s : PExpr) : RecB := fun m => m.isDefEqCore t s

def isDefEqCorePure (t s : PExpr) : RecM Bool := fun m => m.isDefEqCorePure t s

@[inherit_doc isDefEqCore]
def isDefEq (t s : PExpr) : RecB := do
  let r ← isDefEqCore t s
  pure r

def isDefEqPure (t s : PExpr) : RecM Bool := do
  runLeanMinus $ Lean.TypeChecker.isDefEq t s

/--
Infers the type of application `e`, assuming that `e` is already well-typed.
-/
def inferApp (e : PExpr) : RecM PExpr := do
  e.toExpr.withApp fun f args => do
  let f := f.toPExpr
  let args := args.map (·.toPExpr)
  let mut fType ← inferTypePure f
  let mut j := 0
  for i in [:args.size] do
    match fType.toExpr with
    | .forallE _ _ body _ =>
      fType := body.toPExpr
    | _ =>
      fType := fType.toExpr.instantiateRevRange j i args |>.toPExpr
      let (fType', p?) ← ensureForallCore fType e
      assert 3 $ p? == none -- sanity check; f should already have been cast as necessary
      fType := fType'.toExpr.bindingBody!.toPExpr -- TODO ask on zulip about how to avoid this kind of double-casting
      j := i
  return fType.toExpr.instantiateRevRange j args.size args |>.toPExpr

def markUsed (n : Nat) (fvars : Array Expr) (b : Expr) (used : Array Bool) : Array Bool := Id.run do
  if !b.hasFVar then return used
  (·.2) <$> StateT.run (s := used) do
    b.forEachV' fun x => do
      if !x.hasFVar then return false
      if let .fvar name := x then
        for i in [:n] do
          if fvars[i]!.fvarId! == name then
            modify (·.set! i true)
            return false
      return true

/--
Infers the type of let-expression `e`.
-/
def inferLet (e : Expr) : RecPE := loop #[] #[] false e where
  loop fvars vals typePatched : Expr → RecPE
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let (typeType, type'?) ← inferType type 
    let (typeType', pType?) ← ensureSortCore typeType type
    let type' ← maybeCast pType? typeType typeType' (type'?.getD type.toPExpr)
    let val := val.instantiateRev fvars
    let (valType, val'?) ← inferType val 
    let (defEq, pVal?) ← isDefEq valType type' -- FIXME order?
    if !defEq then
      throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type'
    let val' ← maybeCast pVal? valType type' (val'?.getD val.toPExpr)
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLetDecl id name type' val') do
      let fvars := fvars.push (.fvar id)
      let vals := vals.push val'
      loop fvars vals (typePatched || type'?.isSome || pType?.isSome || val'?.isSome || pVal?.isSome) body
  | e => do
    let (r, e'?) ← inferType (e.instantiateRev fvars)
    let e' := e'?.getD e.toPExpr
    let r := r.toExpr.cheapBetaReduce.toPExpr
    let rec loopUsed i (used : Array Bool) :=
      match i with
      | 0 => used
      | i+1 =>
        let used := if used[i]! then markUsed i fvars vals[i]! used else used
        loopUsed i used
    let used := mkArray fvars.size false
    let used := markUsed fvars.size fvars r used
    let used := loopUsed fvars.size used
    let mut usedFVars := #[]
    for fvar in fvars, b in used do
      if b then
        usedFVars := usedFVars.push fvar
    -- FIXME `usedFVars` is never used
    let patch? ←
      if typePatched || e'?.isSome then do
        pure $ .some $ (← getLCtx).mkForall fvars e' |>.toPExpr
      else
        pure none
    return ((← getLCtx).mkForall fvars r |>.toPExpr, patch?)

-- def inferLetPure (e : PExpr) : RecM PExpr := sorry

/--
Checks if the type of `e` is definitionally equal to `Prop`.
-/
def isProp (e : PExpr) : RecB := do
  let t ← inferTypePure e
  let (t', p?) ← whnf t
  return (t' == Expr.prop.toPExpr, p?)

/--
Infers the type of structure projection `e`.

FIXME: This does a lot of checking on the struct constructor type itself,
shouldn't that belong in Inductive/Add.lean instead?
-/
def inferProj (typeName : Name) (idx : Nat) (struct : PExpr) (patched : Bool) (structType : PExpr) : RecPE := do
  let e := Expr.proj typeName idx struct
  let (type, pType?) ← whnf structType
  let mut struct := struct
  -- TODO if pType? := some _ then must cast struct
  type.toExpr.withApp fun I args => do
  let env ← getEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let [c] := I_val.ctors | fail
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels |>.toPExpr
  for i in [:I_val.numParams] do
    let (.mk (.forallE _ _ b _), p?) ← whnf r | fail -- FIXME use ensureForall?
    assert 0 $ p? == none -- FIXME can we guarantee this? if so should remove whnf, if not need to "cast" `c` in Inductive.add
    r := b.instantiate1 args[i]! |>.toPExpr
  let (isPropType, p?) := ← isProp type
  assert 0 $ p? == none
  for i in [:idx] do
    let (.mk (.forallE _ dom b _), p?) ← whnf r | fail -- FIXME use ensureForall?
    assert 0 $ p? == none -- FIXME
    if b.hasLooseBVars then
      -- prop structs cannot have non-prop dependent fields
      let (isPropDom, p?) := ← isProp dom.toPExpr
      assert 0 $ p? == none
      if isPropType then if !isPropDom then fail
      r := b.instantiate1 (.proj I_name i struct) |>.toPExpr
    else
      r := b.toPExpr
  let (.mk (.forallE _ dom _ _), p?) ← whnf r | fail -- FIXME use ensureForall?
  assert 0 $ p? == none -- FIXME
  let (isPropDom, p?) := ← isProp dom.toPExpr
  assert 0 $ p? == none -- FIXME
  if isPropType then if !isPropDom then fail
  let patched := patched || pType?.isSome
  let patch := if patched then some (Expr.proj typeName idx struct).toPExpr else none
  return (dom.toPExpr, patch)

-- def inferProjPure (typeName : Name) (idx : Nat) (struct : Expr) (structType : Expr) (structp? : Option Expr) : RecM PExpr := sorry

@[inherit_doc inferType]
def inferType' (e : Expr) : RecPE := do
  -- if (← readThe Context).const == `eq_of_heq' then
  --   dbg_trace s!"started e={e}"
  if e.isBVar then
    throw <| .other
      s!"patcher does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert 5 $ !e.hasLooseBVars
  let state ← get
  if let some r := state.inferTypeC.find? e then
    -- if (← readThe Context).const == `eq_of_heq' then
    --   dbg_trace s!"finished e={e}"
    return r
  let (r, ep?) ← match e with
    | .lit l => pure (l.type.toPExpr, none)
    | .mdata _ e => inferType' e
    | .proj s idx e =>
      let (t, e'?) ← inferType' e
      let e' := e'?.getD e.toPExpr
      inferProj s idx e' e'?.isSome t
    | .fvar n => pure (← inferFVar (← readThe Context) n, none)
    | .mvar _ => throw <| .other "patcher does not support meta variables"
    | .bvar _ => throw $ .other "unreachable 1"
    | .sort l =>
      checkLevel (← readThe Context) l
      pure <| (Expr.sort (.succ l) |>.toPExpr, none)
    | .const c ls => pure (← inferConstant (← readThe Context) c ls, none)
    | .lam .. => inferLambda e
    | .forallE .. => inferForall e
    | .app f a =>
      let (fType, f'?) ← inferType' f
      let (fType', pf'?) ← ensureForallCore fType f
      let f' ← maybeCast pf'? fType fType' (f'?.getD f.toPExpr)
      -- if (← readThe Context).const == `eq_of_heq' then if let .lam _ (.const `Ty _) _ _ := a then

      let (aType, a'?) ← inferType' a

      let dType := Expr.bindingDomain! fType' |>.toPExpr
      -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
      -- for some universe level `l`, so this use of `isDefEq` is valid
      let (defEq, pa'?) ← isDefEq aType dType
      let a' ← maybeCast pa'? aType dType (a'?.getD a.toPExpr)
      if defEq then
        let patch := if f'?.isSome || a'?.isSome || pf'?.isSome || pa'?.isSome then .some (Expr.app f' a').toPExpr else none
        pure ((Expr.bindingBody! fType').instantiate1 a' |>.toPExpr, patch)
      else
        -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
        --   dbg_trace s!"DBG[66]: TypeChecker.lean:1407 (after dbg_trace s!DBG[47]: TypeChecker.lean:14…)"
        throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType' aType
    | .letE .. => inferLet e
  modify fun s => { s with inferTypeC := s.inferTypeC.insert e (r, ep?) }
  -- if (← readThe Context).const == `eq_of_heq' then
  --   dbg_trace s!"finished e={e}"
  return (r, ep?)

-- def _inferTypePure' (e : Expr) : RecM PExpr := do
--   if e.isBVar then
--     throw <| .other
--       s!"type checker does not support loose bound variables, {""
--         }replace them with free variables before invoking it"
--   assert 1 $ !e.hasLooseBVars
--   let state ← get
--   if let some r := state.inferTypeI.find? e then
--     return r
--   let r ← match e with
--     | .lit l => pure l.type.toPExpr
--     | .mdata _ e' => _inferTypePure' e'
--     | .proj s idx e =>
--       let t ← _inferTypePure' e.toPExpr
--       inferProjPure s idx e t .none
--     | .fvar n => inferFVar (← readThe Context) n
--     | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
--     | .bvar _ => throw $ .other "unreachable"
--     | .sort l =>
--       pure <| (Expr.sort (.succ l)).toPExpr
--     | .const c ls => inferConstant (← readThe Context) c ls true
--     | .lam .. => inferLambdaPure e.toPExpr
--     | .forallE .. => inferForallPure e.toPExpr
--     | .app .. => inferApp e.toPExpr
--     | .letE .. => inferLetPure e.toPExpr
--   modify fun s => { s with inferTypeI := s.inferTypeI.insert e r }
--   return r

def inferTypePure' (e : PExpr) : RecM PExpr := do -- TODO make more efficient
  let eT ← runLeanMinus $ Lean.TypeChecker.inferTypeCheck e.toExpr
  pure eT.toPExpr

/--
Reduces `e` to its weak-head normal form, without unfolding definitions. This
is a conservative version of `whnf` (which does unfold definitions), to be used
for efficiency purposes.

Setting `cheapRec` or `cheapProj` to `true` will cause the major premise/struct
argument to be reduced "lazily" (using `whnfCore` rather than `whnf`) when
reducing recursor applications/struct projections. This can be a useful
optimization if we're checking the definitional equality of two recursor
applications/struct projections of the same recursor/projection, where we
might save some work by directly checking if the major premises/struct
arguments are defeq (rather than eagerly applying a recursor rule/projection).
-/
def whnfCore (e : PExpr) (cheapRec := false) (cheapProj := false) : RecEE :=
  fun m => m.whnfCore e cheapRec cheapProj

/--
Gets the weak-head normal form of the free variable `e`,
which is the weak-head normal form of its definition if `e` is a let variable and itself if it is a lambda variable.
-/
def whnfFVar (e : PExpr) (cheapRec cheapProj : Bool) : RecEE := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.toExpr.fvarId! then
    return ← whnfCore v.toPExpr cheapRec cheapProj
  return (e, none)

def appProjThm? (structName : Name) (projIdx : Nat) (struct structN : PExpr) (structEqstructN? : Option EExpr) : RecM (Option EExpr) := do
  structEqstructN?.mapM fun structEqstructN => do
    let env ← getEnv
    let structType ← whnfPure (← inferTypePure struct)
    let .const typeC lvls := if structType.toExpr.isApp then structType.toExpr.withApp fun f _ => f else structType.toExpr | unreachable!
    let .inductInfo {ctors := [ctor], numParams, ..} ← env.get typeC | unreachable!
    let params := structType.toExpr.getAppArgs
    let ctorInfo ← env.get ctor
    let ctorType := ctorInfo.instantiateTypeLevelParams lvls |>.toPExpr

    let structSort ← inferTypePure structType
    let structLvl := structSort.toExpr.sortLevel!
    
    let ids := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl ids default structType default) do
      let s := (Expr.fvar ids).toPExpr

      let mut remCtorType := ctorType.toExpr
      for idx in [:projIdx + numParams] do
        if let .forallE _ _ b _ := remCtorType then
          let inst :=
            if idx >= numParams then
              .proj structName (idx - numParams) s
            else
              params[idx]!
          remCtorType := b.instantiate1 inst
        else
          unreachable!
      let .forallE _ projOutType _ _ := remCtorType | unreachable!

      let U := ((← getLCtx).mkLambda #[s] projOutType).toPExpr

      let projSort ← inferTypePure (Expr.app U structN).toPExpr
      let .sort projLvl := (← ensureSortCorePure projSort default).toExpr | throw $ .other "unreachable 4"

      let f := (← getLCtx).mkLambda #[s] (.proj structName projIdx s) |>.toPExpr

      let ret := .app {u := structLvl, v := projLvl, A := structType, U := (projOutType.toPExpr, s), f, a := struct, extra := .Arg {b := structN, aEqb := structEqstructN}, lctx := (← getLCtx)}
      pure ret

/--
Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a
constructor application).
-/
def reduceProj (structName : Name) (projIdx : Nat) (struct : PExpr) (cheapRec cheapProj : Bool) : RecM (Option (PExpr × Option EExpr)) := do
  let mut (structN, structEqc?) ← (if cheapProj then whnfCore struct cheapRec cheapProj else whnf struct)

  -- -- TODO is this necessary? can we assume the type of c and struct are the same?
  -- -- if not, we will need to use a different patch theorem
  -- let cType ← inferTypePure c
  -- let (.true, cTypeEqstructType?) ← isDefEq cType structType | throw $ .other "unreachable 2"
  -- c ← maybeCast cTypeEqstructType? lvl cType structType c 

  if let (.lit (.strVal s)) := structN.toExpr then
    structN := Expr.strLitToConstructor s |>.toPExpr

  structN.toExpr.withApp fun mk args => do
    let .const mkC _ := mk | return none
    let .ctorInfo mkCtorInfo ← (← getEnv).get mkC | return none
    let projstructEqprojstructN? ← appProjThm? structName projIdx struct structN structEqc?

    return args[mkCtorInfo.numParams + projIdx]?.map (·.toPExpr, projstructEqprojstructN?)

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

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

def reduceNative (_env : Environment) (e : PExpr) : Except KernelException (Option (PExpr × Option EExpr)) := do
  let .app f (.const c _) := e.toExpr | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def appHEqTrans? (t s r : PExpr) (theqs? sheqr? : Option EExpr) : RecM (Option EExpr) := do
  match theqs?, sheqr? with
  | none, none => return none
  | .some theqs, .some sheqr =>
    let (lvl, tType) ← getTypeLevel t
    let sType ← inferTypePure s
    let rType ← inferTypePure r

    return .some $ .trans {u := lvl, A := tType, B := sType, C := rType, a := t, b := s, c := r, aEqb := theqs, bEqc := sheqr}
  | none, .some sheqr => return sheqr
  | .some theqs, none => return theqs

-- def mkRefl (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do
--   pure $ Lean.mkAppN (← getConst `Eq.refl [lvl]) #[T, t] |>.toEExprD

def mkHRefl (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do
  pure $ .refl {u := lvl, A := T, a := t}

def natLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

/--
Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced
to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatOp (op : Name) (f : Nat → Nat → Nat) (a b : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let (a', pa?) := (← whnf a)
  let (b', pb?) := (← whnf b)
  let some v1 := natLitExt? a' | return none
  let some v2 := natLitExt? b' | return none
  let ret? ← if pa?.isSome || pb?.isSome then
      let pa ← pa?.getDM (mkHRefl (.succ .zero) (Expr.const `Nat []).toPExpr a')
      let pb ← pb?.getDM (mkHRefl (.succ .zero) (Expr.const `Nat []).toPExpr b')
      pure $ .some $ Lean.mkAppN (← getConst `L4L.appHEqBinNatFn []) #[.const `Nat [], .const `Nat [], .const op [], a, a', b, b', pa, pb] |>.toEExpr
    else
      pure none
  return some <| ((Expr.lit <| .natVal <| f v1 v2).toPExpr, ret?)

/--
Reduces the application `f a b` to a boolean expression if `a` and `b` can be
reduced to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatPred (op : Name) (f : Nat → Nat → Bool) (a b : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let (a', pa?) := (← whnf a)
  let (b', pb?) := (← whnf b)
  let some v1 := natLitExt? a' | return none
  let some v2 := natLitExt? b' | return none
  let ret? ← if pa?.isSome || pb?.isSome then
      let pa ← pa?.getDM (mkHRefl (.succ .zero) (Expr.const `Nat []).toPExpr a')
      let pb ← pb?.getDM (mkHRefl (.succ .zero) (Expr.const `Nat []).toPExpr b')
      pure $ .some $ Lean.mkAppN (← getConst `L4L.appHEqBinNatFn []) #[.const `Nat [], .const `Bool [], .const op [], a, a', b, b', pa, pb] |>.toEExpr
    else
      pure none
  return (toExpr (f v1 v2) |>.toPExpr, ret?)

def mkNatSuccAppArgHEq? (p? : Option EExpr) (t s : PExpr) : RecM (Option EExpr) := do
  p?.mapM fun p => do
    pure $ (mkAppN (← getConst `appArgHEq [.succ .zero, .succ .zero]) #[.const `Nat [], --FIXME
    .const `Nat [], .const `Nat.succ [], t, s, p.toExpr]).toEExpr

/--
Reduces `e` to a natural number literal if possible, where binary operations
and predicates may be applied (provided they have an external implementation).
These include: `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`,
`Nat.mod`, `Nat.div`, `Nat.beq`, `Nat.ble`.
-/
def reduceNat (e : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  if e.toExpr.hasFVar then return none
  let nargs := e.toExpr.getAppNumArgs
  if nargs == 1 then
    let f := e.toExpr.appFn!
    if f == .const ``Nat.succ [] then
      let prec := e.toExpr.appArg!.toPExpr
      let (prec', p?) ← whnf prec
      let some v := natLitExt? prec' | return none
      return some <| ((Expr.lit <| .natVal <| v + 1).toPExpr, ← mkNatSuccAppArgHEq? p? prec prec')
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e.toExpr | return none
    if f == ``Nat.add then return ← reduceBinNatOp ``Nat.add Nat.add a.toPExpr b.toPExpr
    if f == ``Nat.sub then return ← reduceBinNatOp ``Nat.sub Nat.sub a.toPExpr b.toPExpr
    if f == ``Nat.mul then return ← reduceBinNatOp ``Nat.mul Nat.mul a.toPExpr b.toPExpr
    if f == ``Nat.pow then return ← reduceBinNatOp ``Nat.pow Nat.pow a.toPExpr b.toPExpr
    if f == ``Nat.gcd then return ← reduceBinNatOp ``Nat.gcd Nat.gcd a.toPExpr b.toPExpr
    if f == ``Nat.mod then return ← reduceBinNatOp ``Nat.mod Nat.mod a.toPExpr b.toPExpr
    if f == ``Nat.div then return ← reduceBinNatOp ``Nat.div Nat.div a.toPExpr b.toPExpr
    if f == ``Nat.beq then return ← reduceBinNatPred ``Nat.beq Nat.beq a.toPExpr b.toPExpr
    if f == ``Nat.ble then return ← reduceBinNatPred ``Nat.ble Nat.ble a.toPExpr b.toPExpr
  return none

structure BinderData where
name : Name
dom : PExpr
info : BinderInfo
deriving Inhabited

def isDefEqBinderForApp' (aVars bVars : Array PExpr) (Uas Vbs : Array PExpr) (ds? : Array (Option (FVarId × FVarId × EExpr))) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (fEqg? : Option EExpr) (f g : PExpr) 
: RecM (Option EExpr) := do
  let mut fEqg? := fEqg?
  let mut f := f
  let mut g := g
  for idx in [:as.size] do
    let a := as[idx]!
    let b := bs[idx]!
    let aEqb? := asEqbs?[idx]!

    fEqg? ←
      if aEqb?.isSome || fEqg?.isSome then
        let aVar := aVars[idx]!
        let bVar := bVars[idx]!
        let d? := ds?[idx]!
        let A ← inferTypePure aVar

        let lctx ← getLCtx

        let (u, _) ← getTypeLevel aVar

        let Ua := Uas[idx]!
        let Vb := Vbs[idx]!

        let (defEq, UaEqVb?) ← isDefEq Ua Vb
        assert 23 defEq

        let (UaTypeLvl, UaType) ← getTypeLevel Ua
        let UaType ← whnfPure UaType
        let v := UaType.toExpr.sortLevel!

        let (U, V) := ((Ua, aVar), (Vb, bVar))

        let extra ← if let .some (idaEqb, idbEqa, hAB) := d? then
          let B ← inferTypePure bVar

          let some fEqg := fEqg? | unreachable!
          let some aEqb := aEqb? | unreachable!

          -- Ua and Vb may still contain references to a and b despite being
          -- defeq (if dep == true), so we need to consider this case, and
          -- cannot immediately fall back to .AB (which has no dependent variant)
          let dep := Ua.toExpr.containsFVar aVar.toExpr.fvarId! || Vb.toExpr.containsFVar bVar.toExpr.fvarId!

          if UaEqVb?.isSome || dep then
            let UaEqVb ← UaEqVb?.getDM $ mkHRefl UaTypeLvl UaType Ua
            let hUV := {a := aVar, UaEqVb, extra := .some {b := bVar, vaEqb := {aEqb := (Expr.fvar idaEqb).toPExpr, bEqa := (Expr.fvar idbEqa).toPExpr}}}
            pure $ .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb}
          else
            assert! not dep
            pure $ .AB {B, hAB, g, fEqg, b, aEqb}
        else
          if let .some UaEqVb := UaEqVb? then
            let some fEqg := fEqg? | unreachable!
            let hUV := {a := aVar, UaEqVb, extra := .none}
            if let some aEqb := aEqb? then
              pure $ .UV {V, hUV, g, fEqg, b, aEqb}
            else
              pure $ .UVFun {V, hUV, g, fEqg}
          else
            if let some fEqg := fEqg? then
              if let some aEqb := aEqb? then
                pure $ .none {g, fEqg, b, aEqb}
              else
                pure $ .Fun {g, fEqg}
            else
              if let some aEqb := aEqb? then
                pure $ .Arg {b, aEqb}
              else
                unreachable!

        pure $ .some $ .app {u, v, A, U, f, a, extra, lctx}
      else
        pure none

    f := f.toExpr.app a |>.toPExpr
    g := g.toExpr.app b |>.toPExpr
  pure fEqg?

def isDefEqBinderForApp (T S : PExpr) (as bs : Array PExpr) (tArgsEqsArgs? : Array (Option EExpr)) (tfEqsf? : (Option EExpr)) (f g : PExpr) : RecM (Option EExpr) := do
  let rec loop idx T S aVars bVars Uas Vbs ds? : RecM (Option EExpr) := do
    let (T', dA, S', dB) ← match (← whnfPure T).toExpr, (← whnfPure S).toExpr with
      | .forallE tName tDom tBody tBi, .forallE sName sDom sBody sBi =>
        pure $ (tBody, ({name := tName, dom := tDom.toPExpr, info := tBi} : BinderData), sBody, ({name := sName, dom := sDom.toPExpr, info := sBi} : BinderData))
      | tBody, sBody => unreachable!

    let a := as[idx]!
    let b := bs[idx]!

    let T := (T'.instantiate1 a.toExpr).toPExpr
    let S := (S'.instantiate1 b.toExpr).toPExpr

    let ({name := aName, dom := A, info := aBi},
      {name := bName, dom := B, info := bBi}) := (dA, dB)

    -- sanity check
    let aType ← inferTypePure a
    let bType ← inferTypePure b
    let .true ← isDefEqPure A aType | do
      throw $ .other s!"expected: {A}\n inferred: {aType}"
    let .true ← isDefEqPure B bType | do
      throw $ .other s!"expected: {B}\n inferred: {bType}"

    let AEqB? ← if A != B then
      let (defEq, AEqB?) ← isDefEq A B
      assert 22 defEq
      pure AEqB?
    else pure (none)

    let sort ← inferTypePure A
    let .sort lvl := (← ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"
    let ida := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl ida aName A aBi) do
      let aVar := (Expr.fvar ida).toPExpr

      let cont d? bVar := do 
        let ds? := ds?.push d?
        let Ua := (T'.instantiate1 aVar).toPExpr
        let Vb := (S'.instantiate1 bVar).toPExpr

        let aVars := aVars.push aVar
        let bVars := bVars.push bVar
        let Uas := Uas.push Ua
        let Vbs := Vbs.push Vb
        if _h : idx < as.size - 1 then
          loop (idx + 1) T S aVars bVars Uas Vbs ds?
        else
          isDefEqBinderForApp' aVars bVars Uas Vbs ds? as bs tArgsEqsArgs? tfEqsf? f g

      if let some AEqB := AEqB? then 
        let idb := ⟨← mkFreshId⟩
        let idaEqb := ⟨← mkFreshId⟩
        let idbEqa := ⟨← mkFreshId⟩
        withLCtx ((← getLCtx).mkLocalDecl idb bName B bBi) do
          let bVar := (Expr.fvar idb).toPExpr
          let teqsType := mkAppN (.const `HEq [lvl]) #[A, aVar, B, bVar]
          let seqtType := mkAppN (.const `HEq [lvl]) #[B, bVar, A, aVar]
          withLCtx ((← getLCtx).mkLocalDecl idaEqb default teqsType default) do
            withLCtx ((← getLCtx).mkLocalDecl idbEqa default seqtType default) do
              withEqFVar ida idb idaEqb do
                let d := (idaEqb, idbEqa, AEqB)
                cont (.some d) bVar
      else
        cont none aVar
  termination_by (as.size - 1) - idx

  loop 0 T S #[] #[] #[] #[] #[]

def isDefEqBinder (binDatas : Array (BinderData × BinderData)) (tBody sBody : PExpr)
(f : PExpr → PExpr → Option EExpr → Array PExpr → Array (Option (PExpr × FVarId × FVarId × EExpr)) → RecM (Option T))
: RecM (Bool × (Option T)) := do
  let rec loop idx tvars svars ds : RecM (Bool × (Option T)) := do
    let ({name := tName, dom := tDom, info := tBi},
      {name := sName, dom := sDom,  info := sBi}) := binDatas.get! idx
    let tDom := tDom.instantiateRev tvars
    let sDom := sDom.instantiateRev svars
    let p? ← if tDom != sDom then
      let (defEq, p?) ← isDefEq tDom sDom
      if !defEq then return (false, none)
      pure p?
    else pure none
    let sort ← inferTypePure tDom
    let .sort lvl := (← ensureSortCorePure sort tDom).toExpr | throw $ .other "unreachable 5"
    let idt := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl idt tName tDom tBi) do
      let tvar := (Expr.fvar idt).toPExpr
      let tvars := tvars.push tvar

      let cont d? svar := do
        let svars := svars.push svar
        let ds := ds.push d?

        if _h : idx < binDatas.size - 1 then
          loop (idx + 1) tvars svars ds
        else
          let tBody := tBody.instantiateRev tvars
          let sBody := sBody.instantiateRev svars
          let (defEq, ptbodEqsbod?) ← isDefEq tBody sBody
          if !defEq then return (false, none)
          pure (true, ← f tBody sBody ptbodEqsbod? tvars.reverse ds.reverse) -- FIXME can iterate backwards instead of reversing lists?

      if let some p := p? then
        let ids := ⟨← mkFreshId⟩
        withLCtx ((← getLCtx).mkLocalDecl ids sName sDom sBi) do
          let svar := (Expr.fvar ids).toPExpr
          let teqsType := mkAppN (.const `HEq [lvl]) #[tDom, tvar, sDom, svar]
          let seqtType := mkAppN (.const `HEq [lvl]) #[sDom, svar, tDom, tvar]
          let idtEqs := ⟨← mkFreshId⟩
          let idsEqt := ⟨← mkFreshId⟩
          withLCtx ((← getLCtx).mkLocalDecl idtEqs default teqsType default) do
            withLCtx ((← getLCtx).mkLocalDecl idsEqt default seqtType default) do
              withEqFVar idt ids idtEqs do
                cont (.some (svar, idtEqs, idsEqt, p)) svar 
      else
        cont none tvar

  termination_by (binDatas.size - 1) - idx
  loop 0 #[] #[] #[]

/--
If `t` and `s` are lambda expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqLambda (t s : PExpr) : RecB := do
  let rec getData t s := do
    match t, s with
    | .lam tName tDom tBody tBi, .lam sName sDom sBody sBi =>
      let (datas, tBody, sBody) ← getData tBody sBody
      pure (#[({name := tName, dom := tDom.toPExpr, info := tBi}, {name := sName, dom := sDom.toPExpr, info := sBi})] ++ datas, tBody, sBody)
    | tBody, sBody =>
      pure (#[], tBody.toPExpr, sBody.toPExpr)
  let (datas, tBody, sBody) ← getData t.toExpr s.toExpr
  isDefEqBinder datas tBody sBody fun fa gx faEqgb? as ds => do
    let mut faEqgx? := faEqgb?
    let mut fa := fa
    let mut gx := gx
    for (a, d?) in as.zip ds do
      let f := (← getLCtx).mkLambda #[a] fa |>.toPExpr
      -- gx was abstracted over a if A defeq B (instead of over a fresh (b : B))
      let x : PExpr := if let some (b, _, _) := d? then b else a
      let g := (← getLCtx).mkLambda #[x] gx |>.toPExpr
      if d?.isSome || faEqgx?.isSome then
        let (ALvl, A) ← getTypeLevel a
        let u := ALvl
        let (UaLvl, Ua) ← getTypeLevel fa
        let v := UaLvl
        let Vx ← inferTypePure gx
        let faEqgx ← faEqgx?.getDM $ mkHRefl UaLvl Ua fa
        let (U, V) := ((Ua, a), (Vx, x))
        let extra ← if let some (b, idaEqb, idbEqa, hAB) := d? then
          let B ← inferTypePure b
          let aEqb := (Expr.fvar idaEqb).toPExpr
          let bEqa := (Expr.fvar idbEqa).toPExpr
          pure $ .ABUV {B, b, hAB, vaEqb := {aEqb, bEqa}} {V}
        else
          let (_, UaEqVx?) ← isDefEq Ua Vx
          if UaEqVx?.isSome then
            pure $ .UV {V}
          else
            pure $ .none
        faEqgx? := .some $ .lam {u, v, A, a, U, f, g, faEqgx, extra, lctx := ← getLCtx}

      fa := f
      gx := g
    pure faEqgx?

def withAppDatas (T S : PExpr) (tArgs sArgs : Array PExpr) (tasEqsas? : Array (Option EExpr)) (tfEqsf? : (Option EExpr)) (f g : PExpr) : RecM (Option EExpr) := do
  isDefEqBinderForApp T S tArgs sArgs tasEqsas? tfEqsf? f g

/--
If `t` and `s` are for-all expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqForall' (t s : PExpr) : RecB := do
  let rec getData t s := do
    match t, s with
    | .forallE tName tDom tBody tBi, .forallE sName sDom sBody sBi =>
      let (datas, tBody, sBody) ← getData tBody sBody
      pure (#[({name := tName, dom := tDom.toPExpr, info := tBi}, {name := sName, dom := sDom.toPExpr, info := sBi})] ++ datas, tBody, sBody)
    | tBody, sBody =>
      pure (#[], tBody.toPExpr, sBody.toPExpr)
  let (datas, tBody, sBody) ← getData t.toExpr s.toExpr
  isDefEqBinder datas tBody sBody fun Ua Vx UaEqVx? as ds => do
    let mut UaEqVx? := UaEqVx?
    let mut Ua := Ua
    let mut Vx := Vx

    let mut idx := 0
    for (a, d?) in as.zip ds do
      let x := if let some (b, _, _) := d? then b else a

      idx := idx + 1

      if d?.isSome || UaEqVx?.isSome then
        let (UaTypeLvl, UaType) ← getTypeLevel Ua
        let UaType ← whnfPure UaType
        let UaLvl := UaType.toExpr.sortLevel!

        let (ALvl, A) ← getTypeLevel a
        let u := ALvl
        let v := UaLvl

        let UaEqVx := UaEqVx?.getD $ ← mkHRefl UaTypeLvl UaType Ua
        let (U, V) := ((Ua, a), (Vx, x))

        let extra ← if let .some (b, idaEqb, idbEqa, hAB) := d? then
          let B ← inferTypePure b
          let aEqb := (Expr.fvar idaEqb).toPExpr
          let bEqa := (Expr.fvar idbEqa).toPExpr
          pure $ .AB {B, b, vaEqb := {aEqb, bEqa}, hAB}
        else
          pure .none

        UaEqVx? := .some $ .forallE {u, v, A, a, U, V, UaEqVx, extra, lctx := ← getLCtx}

      Ua := (← getLCtx).mkForall #[a] Ua |>.toPExpr
      Vx := (← getLCtx).mkForall #[x] Vx |>.toPExpr

    pure $ UaEqVx?

def isDefEqForall (t s : PExpr) : RecB := do
  let (true, p?) ← isDefEqForall' t s | return (false, none)
  return (true, p?)

def isDefEqFVar (idt ids : FVarId) : RecLB := do
  if let some id := (← readThe Context).eqFVars.find? (idt, ids) then
    let p := (Expr.fvar id).toEExpr
    return (.true, some p)
  else if let some id := (← readThe Context).eqFVars.find? (ids, idt) then
    let p := (Expr.fvar id).toEExpr
    return (.true, ← appHEqSymm? (Expr.fvar idt).toPExpr (Expr.fvar ids).toPExpr p)
  return (.undef, none)

/--
If `t` and `s` have matching head constructors and are not projections or
(non-α-equivalent) applications, checks that they are definitionally equal.
Otherwise, defers to the calling function.
-/
def quickIsDefEq (t s : PExpr) (useHash := false) : RecLB := do
  -- optimization for terms that are already α-equivalent
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 (eqvManager := m)) =>
    let (b, m) := m.isEquiv useHash t s
    (b, .mk a1 a2 a3 a4 a5 a6 (eqvManager := m))
  then return (.true, none)
  let res : Option (Bool × PExpr) ← match t.toExpr, s.toExpr with
  | .lam .., .lam .. => pure $ some $ ← isDefEqLambda t s
  | .fvar idt, .fvar ids =>
    match ← isDefEqFVar idt ids with
    | (.undef, _) => pure none
    | (.true, p?) => pure (true, p?)
    | (.false, p?) => pure (false, p?)
  | .forallE .., .forallE .. => pure $ some $ ← isDefEqForall t s
  | .sort a1, .sort a2 => pure $ some $ ((a1.isEquiv a2), none)
  | .mdata _ a1, .mdata _ a2 => pure $ some $ ← isDefEq a1.toPExpr a2.toPExpr
  | .mvar .., .mvar .. => throw $ .other "unreachable 6"
  | .lit a1, .lit a2 => pure $ some ((a1 == a2), none)
  | _, _ => pure none
  let some (defeq, p?) := res | return (.undef, none)
  pure (defeq.toLBool, p?)

/--
Checks if `t` and `s` are defeq after applying η-expansion to `s`.

Assuming that `s` has a function type `(x : A) -> B x`, it η-expands to
`fun (x : A) => s x` (which it is definitionally equal to by the η rule).
-/
def tryEtaExpansionCore (t s : PExpr) : RecB := do
  if t.toExpr.isLambda && !s.toExpr.isLambda then
    let .forallE name ty _ bi := (← whnfPure (← inferTypePure s)).toExpr | return (false, none)
    isDefEq t (Expr.lam name ty (.app s (.bvar 0)) bi).toPExpr -- NOTE: same proof should be okay because of eta-expansion when typechecking
  else return (false, none)

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : PExpr) : RecB := do
  match ← tryEtaExpansionCore t s with
  | ret@(true, _) => pure ret 
  | (false, _) => 
    let (true, sEqt?) ← tryEtaExpansionCore s t | return (false, none)-- TODO apply symm
    return (true, ← appHEqSymm? s t sEqt?)

def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr) (n : Nat) (tfEqsf? : Option (Option EExpr) := none)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) : RecM (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))):= do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, ret?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
    else isDefEq tf sf | return (false, none)

  let mut taEqsas := #[]
  let mut idx := 0
  for ta in tArgs, sa in sArgs do
    let mut p? := none
    if let some _p? := targsEqsargs?.find? idx then
      p? := _p?
    else
      let (.true, _p?) ← isDefEq ta sa | return (false, none)
      p? := _p?
    taEqsas := taEqsas.push (p?.map (ta, sa, ·))
    idx := idx + 1

  let mut tfT ← inferTypePure tf
  let mut sfT ← inferTypePure sf

  try
    let tEqs? ← withAppDatas tfT sfT tArgs sArgs (taEqsas.map (·.map (·.2.2))) ret? tf sf

    -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
    return (true, (tEqs?.map fun tEqs => (tEqs, taEqsas)))
  catch e =>
    dbg_trace s!"DBG[1]: TypeChecker.lean:1202 {n}"
    throw e

/--
Checks if applications `t` and `s` (should be WHNF) are defeq on account of
their function heads and arguments being defeq.
-/
def isDefEqApp' (t s : PExpr) (n : Nat) (tfEqsf? : Option (Option EExpr) := none)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) : RecM (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless t.toExpr.isApp && s.toExpr.isApp do return (false, none)
  t.toExpr.withApp fun tf tArgs =>
  s.toExpr.withApp fun sf sArgs => 
    let tf := tf.toPExpr
    let sf := sf.toPExpr
    let tArgs := tArgs.map (·.toPExpr)
    let sArgs := sArgs.map (·.toPExpr)
    isDefEqApp'' tf sf tArgs sArgs n tfEqsf? targsEqsargs?

def isDefEqApp (t s : PExpr) (n : Nat) (tfEqsf? : Option (Option EExpr) := none) (targsEqsargs? : HashMap Nat (Option EExpr) := default) : RecB := do
  let (isDefEq, data?) ← isDefEqApp' t s n tfEqsf? targsEqsargs?
  pure (isDefEq, data?.map (·.1))


/--
Checks if `t` and `s` are application-defeq (as in `isDefEqApp`)
after applying struct-η-expansion to `t`.

Assuming that `s` has a struct type `S` constructor `S.mk` and projection
functions `pᵢ : S → Tᵢ`, it struct-η-expands to `S.mk (p₁ s) ... (pₙ s)` (which
it is definitionally equal to by the struct-η rule).
-/
def tryEtaStructCore (t s : PExpr) : RecB := do
  let ctor := s.toExpr.getAppFn
  let .const f _ := ctor | return (false, none)
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return (false, none)
  unless s.toExpr.getAppNumArgs == fInfo.numParams + fInfo.numFields do return (false, none)
  unless isStructureLike env fInfo.induct do return (false, none)
  unless ← isDefEqPure (← inferTypePure t) (← inferTypePure s) do return (false, none)
  let args := s.toExpr.getAppArgs
  let mut exptE := ctor
  for i in [:fInfo.numParams] do
    exptE := mkApp exptE (args[i]!)
  for i in [fInfo.numParams:args.size] do
    exptE := mkApp exptE (.proj fInfo.induct (i - fInfo.numParams) t)
  let expt := exptE.toPExpr
  
  let tEqexpt? := none -- TODO use proof here to eliminate struct eta
  let (true, exptEqs?) ← isDefEqApp expt s 1 | return (false, none) -- TODO eliminate struct eta
  return (true, ← appHEqTrans? t expt s tEqexpt? exptEqs?)

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : PExpr) : RecB := do
  match ← tryEtaStructCore t s with
  | ret@(true, _) => pure ret
  | (false, _) =>
    let (true, sEqt?) ← tryEtaStructCore s t | return (false, none)
    return (true, ← appHEqSymm? s t sEqt?)

def appPrfIrrelHEq (P Q : PExpr) (hPQ : EExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q, extra := .HEq {Q, hPQ}}

def appPrfIrrel (P : PExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q}

def reduceRecursor (e : PExpr) (cheapRec cheapProj : Bool) : RecM (Option (PExpr × Option EExpr)) := do
  let env ← getEnv
  if env.header.quotInit then
    if let some r ← quotReduceRec e whnf (fun x y tup => isDefEqApp x y 2 (targsEqsargs? := HashMap.insert default tup.1 tup.2)) then
      return r
  let whnf' e := if cheapRec then whnfCore e cheapRec cheapProj else whnf e
  let recReduced? ← inductiveReduceRec {
      isDefEq := isDefEq
      isDefEqPure := isDefEqPure
      whnf  := whnf'
      inferTypePure := fun x => do 
        inferTypePure x
      appPrfIrrelHEq := appPrfIrrelHEq
      appPrfIrrel := appPrfIrrel
      appHEqTrans? := appHEqTrans?
      isDefEqApp := fun t s m mm => isDefEqApp t s m (targsEqsargs? := mm)
      isDefEqApp' := fun t s m mm => isDefEqApp' t s m (targsEqsargs? := mm)
      withPure := withPure
    }
    env e
  if let some r := recReduced? then
    return r
  return none

@[inherit_doc whnfCore]
private def _whnfCore' (e' : Expr) (cheapRec := false) (cheapProj := false) : RecEE := do
  let e := e'.toPExpr
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return (e, none)
  | .mdata _ e => return ← _whnfCore' e cheapRec cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return (e, none)
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache.find? e then
    return r
  let rec save r := do
    if !cheapRec && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => throw $ .other "unreachable 9"
  | .fvar _ => return ← whnfFVar e cheapRec cheapProj
  | .app .. => -- beta-reduce at the head as much as possible, apply any remaining `rargs` to the resulting expression, and re-run `whnfCore`
    e'.withAppRev fun f0 rargs => do
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let (f, pf0Eqf?) ← whnfCore f0.toPExpr cheapRec cheapProj
    let frargs := f.toExpr.mkAppRevRange 0 rargs.size rargs
    -- patch to cast rargs as necessary to agree with type of f
    let (_, frargs'?) ← inferType frargs
    let frargs' := frargs'?.getD frargs.toPExpr
    let rargs' := frargs'.toExpr.getAppArgs[f.toExpr.getAppArgs.size:].toArray.reverse
    assert 10 $ rargs'.size == rargs.size
    let (.true, data?) ← isDefEqApp'' f0.toPExpr f (rargs.map (·.toPExpr)).reverse (rargs'.map (·.toPExpr)).reverse 5 pf0Eqf? |
      throw $ .other "unreachable 10"
    let eEqfrargs'? := data?.map (·.1)


    if let (.lam _ _ body _) := f.toExpr then
      -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
      --   dbg_trace s!"DBG[66]: TypeChecker.lean:1407 (after dbg_trace s!DBG[47]: TypeChecker.lean:14…)"
      let rec loop m (f : Expr) : RecEE :=
        let cont := do
          let r := f.instantiateRange (rargs'.size - m) rargs'.size rargs'
          let r := r.mkAppRevRange 0 (rargs'.size - m) rargs' |>.toPExpr
          let (r', rEqr'?) ← whnfCore r cheapRec cheapProj
          let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? rEqr'?
          save (r', eEqr'?)
        if let .lam _ _ body _ := f then
          if m < rargs'.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if f == f0 then
      if let some (r, eEqr?) ← reduceRecursor e cheapRec cheapProj then
        let (r', rEqr'?) ← whnfCore r cheapRec cheapProj
        let eEqr'? ← appHEqTrans? e r r' eEqr? rEqr'?
        pure (r', eEqr'?)
      else
        pure (e, none)
    else
      -- FIXME replace with reduceRecursor? adding arguments can only result in further normalization if the head reduced to a partial recursor application
      let (r', frargsEqr'?) ← whnfCore frargs' cheapRec cheapProj
      let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? frargsEqr'?
      save (r', eEqr'?)
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val).toPExpr cheapRec cheapProj
  | .proj typeName idx s =>
    if let some (m, eEqm?) ← reduceProj typeName idx s.toPExpr cheapRec cheapProj then
      let (r', mEqr'?) ← whnfCore m cheapRec cheapProj
      let eEqr'? ← appHEqTrans? e m r' eEqm? mEqr'?
      save (r', eEqr'?)
    else
      save (e, none)

@[inherit_doc whnfCore]
def whnfCore' (e : PExpr) (cheapRec := false) (cheapProj := false) : RecEE := _whnfCore' e cheapRec cheapProj

@[inherit_doc whnf]
private def _whnf' (e' : Expr) : RecEE := do
  let e := e'.toPExpr
  -- Do not cache easy cases
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return (e, none)
  | .mdata _ e => return ← _whnf' e
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return (e, none)
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache FIXME re-enable
  -- if let some r := (← get).whnfCache.find? e then
  --   return r
  let rec loop le eEqle?
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let (ler, leEqler?) ← whnfCore' le
    let eEqler? ← appHEqTrans? e le ler eEqle? leEqler?
    if let some (ler', lerEqler'?) ← reduceNative env ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    if let some (ler', lerEqler'?) ← reduceNat ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    let some leru := unfoldDefinition env ler | return (ler, eEqler?)
    loop leru eEqler? fuel
  let r ← loop e none 1000
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

@[inherit_doc whnf]
def whnf' (e : PExpr) : RecEE := _whnf' e

def whnfPure' (e : PExpr) : RecM PExpr := do
  let leanMinusWhnf ← runLeanMinus $ Lean.TypeChecker.whnf e.toExpr
  pure leanMinusWhnf.toPExpr

/--
Checks if `t` and `s` are definitionally equivalent according to proof irrelevance
(that is, they are proofs of the same proposition).
-/
def isDefEqProofIrrel (t s : PExpr) : RecLB := do
  let tType ← inferTypePure t
  let (prop, pprop?) ← isProp tType
  assert 12 $ pprop? == none
  if !prop then return (.undef, none)
  let sType ← inferTypePure s
  let (ret, pt?) ← isDefEq tType sType
  if ret == .true then
    let p ← if let some pt := pt? then
      appPrfIrrelHEq tType sType pt t s
    else
      appPrfIrrel tType t s
    return (.true, .some p)
  pure (.undef, none)

def failedBefore (failure : HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : PExpr) : RecM (Option (PExpr × Option EExpr)) := do
  let f := e.toExpr.getAppFn
  if !f.isProj then return none
  let (e', p?) ← whnfCore e
  return if e' != e then (e', p?) else none

/--
Performs a single step of δ-reduction on `tn`, `sn`, or both (according to
optimizations) followed by weak-head normalization (without further
δ-reduction). If the resulting terms have matching head constructors (excluding
non-α-equivalent applications and projections), or are applications with the
same function head and defeq args, returns whether `tn` and `sn` are defeq.
Otherwise, a return value indicates to the calling `lazyDeltaReduction` that
δ-reduction is to be continued.

If δ-reduction+weak-head-normalization cannot be continued (i.e. we have a
weak-head normal form (with cheapProj := true)), defers further defeq-checking
to `isDefEq`.
-/
def lazyDeltaReductionStep (ltn lsn : PExpr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := whnfCore (unfoldDefinition env e).get! (cheapProj := true)
  let cont (nltn nlsn : PExpr) (pltnEqnltn? plsnEqnlsn? : Option EExpr) :=
    return ← match ← quickIsDefEq nltn nlsn with
    | (.undef, _) => pure $ .continue nltn nlsn pltnEqnltn? plsnEqnlsn?
    | (.true, pnltnEqnlsn?) =>
      do pure $ .bool .true (← appHEqTrans? ltn nltn lsn pltnEqnltn? <| ← appHEqTrans? nltn nlsn lsn pnltnEqnlsn? <| ← appHEqSymm? lsn nlsn plsnEqnlsn?)
    | (.false, _) => pure $ .bool false none
  let deltaCont_t := do
    pure () -- FIXME why is this needed to block `delta` below from being run immediately in the outer monad context?
    let (nltn, pltnEqnltn?) ← delta ltn
    let ret ← cont nltn lsn pltnEqnltn? none
    pure ret
  let deltaCont_s := do
    pure ()
    let (nlsn, plsnEqnlsn?) ← delta lsn
    cont ltn nlsn none plsnEqnlsn?
  let deltaCont_both := do
    pure ()
    let (nltn, pltnEqnltn?) ← delta ltn
    let (nlsn, plsnEqnlsn?) ← delta lsn
    cont nltn nlsn pltnEqnltn? plsnEqnlsn?
  match isDelta env ltn, isDelta env lsn with
  | none, none => return .notDelta
  | some _, none =>
    -- FIXME hasn't whnfCore already been called on sn? so when would this case arise?
    if let some (nlsn, plsnEqnlsn?) ← tryUnfoldProjApp lsn then
      cont ltn nlsn none plsnEqnlsn?
    else
      deltaCont_t
  | none, some _ =>
    if let some (nltn, pltnEqnltn?) ← tryUnfoldProjApp ltn then
      cont nltn lsn pltnEqnltn? none
    else
      deltaCont_s
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      deltaCont_s
    else if hs.lt' ht then
      deltaCont_t
    else
      if ltn.toExpr.isApp && lsn.toExpr.isApp && (unsafe ptrEq dt ds) && dt.hints.isRegular
        && !failedBefore (← get).failure ltn lsn
      then
        if Level.isEquivList ltn.toExpr.getAppFn.constLevels! lsn.toExpr.getAppFn.constLevels! then
          let (r, proof?) ← isDefEqApp ltn lsn 6 (tfEqsf? := some none)
          if r then
            return .bool true proof?
        cacheFailure ltn lsn
      deltaCont_both

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? (e : PExpr) : Option PExpr :=
  match e.toExpr with
  | .lit (.natVal (n+1)) => return Expr.lit (.natVal n) |>.toPExpr
  | .app (.const ``Nat.succ _) e => return e.toPExpr
  | _ => none

/--
If `t` and `s` are both successors of natural numbers `t'` and `s'`, either as
literals or `Nat.succ` applications, checks that `t'` and `s'` are
definitionally equal. Otherwise, defers to the calling function.
-/
def isDefEqOffset (t s : PExpr) : RecLB := do
  if isNatZero t && isNatZero s then
    return (.true, none)
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' =>
    let (ret, p?) ← isDefEqCore t' s'
    let p? ← mkNatSuccAppArgHEq? p? t' s'
    pure (ret.toLBool, p?)
  | _, _ => return (.undef, none)

/--
Returns whether the `cheapProj := true` weak-head normal forms of `tn` and
`sn` are defeq if:
- they have matching head constructors (excluding non-α-equivalent applications
  and projections)
- they're both natural number successors (as literals or `Nat.succ` applications)
- one of them can be converted to a natural number/boolean literal.
Otherwise, defers to the calling function with these normal forms.
-/
def lazyDeltaReduction (tn sn : PExpr) : RecM ReductionStatus := loop tn sn none none 1000 where
  loop ltn lsn (tnEqltn? snEqlsn? : Option EExpr)
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let (r, proof?) ← isDefEqOffset ltn lsn
    if r != .undef then
      if (r == .true) then
        return .bool true proof?
      else
        return .bool false none
    if !ltn.toExpr.hasFVar && !lsn.toExpr.hasFVar then
      if let some (ltn', ltnEqltn'?) ← reduceNat ltn then
        let (ret, ptn'Eqsn?) ← isDefEqCore ltn' lsn
        let tnEqsn? ← appHEqTrans? ltn ltn' lsn ltnEqltn'? ptn'Eqsn?
        return .bool ret tnEqsn?
      else if let some (lsn', lsnEqlsn'?) ← reduceNat lsn then
        let (ret, ptnEqsn'?) ← isDefEqCore ltn lsn'
        let tnEqsn? ← appHEqTrans? ltn lsn' lsn ptnEqsn'? (← appHEqSymm? lsn lsn' lsnEqlsn'?)
        return .bool ret tnEqsn?
    let env ← getEnv
    if let some (ltn', pltnEqLtn'?) ← reduceNative env ltn then
      -- TODO does this case ever happen?
      let (ret, ptn'Eqsn?) ← isDefEqCore ltn' lsn
      let tnEqsn? ← appHEqTrans? ltn ltn' lsn pltnEqLtn'? ptn'Eqsn?
      return .bool ret tnEqsn?
    else if let some (lsn', lsnEqlsn'?) ← reduceNative env lsn then
      -- TODO does this case ever happen?
      let (ret, ptnEqsn'?) ← isDefEqCore ltn lsn'
      let tnEqsn? ← appHEqTrans? ltn lsn' lsn ptnEqsn'? (← appHEqSymm? lsn lsn' lsnEqlsn'?)
      return .bool ret tnEqsn?

    match ← lazyDeltaReductionStep ltn lsn with
    | .continue nltn nlsn ltnEqnltn? lsnEqnlsn? =>

      let tnEqnltn? ← appHEqTrans? tn ltn nltn tnEqltn? ltnEqnltn?
      let snEqnlsn? ← appHEqTrans? sn lsn nlsn snEqlsn? lsnEqnlsn?

      let ret ← loop nltn nlsn tnEqnltn? snEqnlsn? fuel
      pure ret
    | .notDelta =>
      return .unknown ltn lsn tnEqltn? snEqlsn?
    | .bool .true ltnEqlsn? =>
      return .bool .true (← appHEqTrans? tn ltn sn tnEqltn? <| ← appHEqTrans? ltn lsn sn ltnEqlsn? <| ← appHEqSymm? sn lsn snEqlsn?)
    | .bool .false _ =>
      return .bool .false none
    | .unknown .. => throw $ .other "unreachable 11"

/--
If `t` is a string literal and `s` is a string constructor application,
checks that they are defeq after turning `t` into a constructor application.
Otherwise, defers to the calling function.
-/
def tryStringLitExpansionCore (t s : PExpr) : RecM LBool := do
  let .lit (.strVal st) := t.toExpr | return .undef
  let .app sf _ := s.toExpr | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCorePure (Expr.strLitToConstructor st).toPExpr s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : PExpr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/--
Checks if `t` and `s` are defeq on account of both being of a unit type (a type
with one constructor without any fields or indices).
-/
-- NOTE: It is okay for this to be a non-congruence-proving function,
-- because any two instances of a unit type must be definitionally equal to a constructor application
def isDefEqUnitLike (t s : PExpr) : RecB := do
  let (tType, p?) ← whnf (← inferTypePure t)
  assert 13 $ p? == none
  let .const I _ := tType.toExpr.getAppFn | return (false, none)
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return (false, none)
  let .ctorInfo { numFields := 0, .. } ← env.get c | return (false, none)
  if ← isDefEqCorePure tType (← inferTypePure s) then
    return (true, none)
  else
    return (false, none)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : PExpr) : RecB := do
  let leanMinusDefEq ← runLeanMinus $ Lean.TypeChecker.isDefEq t.toExpr s.toExpr
  if leanMinusDefEq then
    return (true, none)
  let (r, pteqs?) ← quickIsDefEq t s (useHash := true)
  if r != .undef then return (r == .true, pteqs?)

  if !t.toExpr.hasFVar && s.toExpr.isConstOf ``true then
    let (t, p?) ← whnf t
    if t.toExpr.isConstOf ``true then return (true, p?)

  let (tn, tEqtn?) ← whnfCore t (cheapProj := true)
  let (sn, sEqsn?) ← whnfCore s (cheapProj := true)

  let mktEqs? (t' s' : PExpr) (tEqt'? sEqs'? t'Eqs'? : Option EExpr) := do appHEqTrans? t s' s (← appHEqTrans? t t' s' tEqt'? t'Eqs'?) (← appHEqSymm? s s' sEqs'?)

  if !(unsafe ptrEq tn t && ptrEq sn s) then
    let (r, tnEqsn?) ← quickIsDefEq tn sn
    if r == .false then
      return (false, none)
    else if r == .true then
      return (true, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)

  let (r, tnEqsn?) ← isDefEqProofIrrel tn sn
  if r != .undef then 
    if r == .true then
      return (true, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)
    return (false, none)

  match ← lazyDeltaReduction tn sn with
  | .continue ..
  | .notDelta => throw $ .other "unreachable 12"
  | .bool b tnEqsn? =>
    return (b, ← mktEqs? tn sn tEqtn? sEqsn? tnEqsn?)
  | .unknown tn' sn' tnEqtn'? snEqsn'? =>

  let tEqtn'? ← appHEqTrans? t tn tn' tEqtn? tnEqtn'?
  let sEqsn'? ← appHEqTrans? s sn sn' sEqsn? snEqsn'?

  match tn'.toExpr, sn'.toExpr with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
  | .fvar tv, .fvar sv => if tv == sv then return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
  | .proj tTypeName ti te, .proj _ si se =>
    if ti == si then
      -- optimized by `lazyDeltaReductionStep` using `cheapProj = true`
      let (r, teEqse?) ← isDefEq te.toPExpr se.toPExpr

      if r then
        return (true, ← appProjThm? tTypeName ti te.toPExpr se.toPExpr teEqse?)
  | _, _ => pure ()

  -- `lazyDeltaReductionStep` used `cheapProj = true`, so we may not have a complete WHNF
  let (tn'', tn'Eqtn''?) ← whnfCore tn'
  let (sn'', sn'Eqsn''?) ← whnfCore sn'
  if !(unsafe ptrEq tn'' tn' && ptrEq sn'' sn') then
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    let tEqtn''? ← appHEqTrans? t tn' tn'' tEqtn'? tn'Eqtn''?
    let sEqsn''? ← appHEqTrans? s sn' sn'' sEqsn'? sn'Eqsn''?
    let (true, tn''Eqsn''?) ← isDefEqCore tn'' sn'' | return (false, none)
    return (true, ← mktEqs? tn'' sn'' tEqtn''? sEqsn''? tn''Eqsn''?)

  -- tn' and sn' are both in WHNF
  match ← isDefEqApp tn' sn' 7 with
  | (true, tn'Eqsn'?) =>
    return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ =>
    pure ()
  match ← tryEtaExpansion tn' sn' with
  | (true, tn'Eqsn'?) => return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ => pure ()
  match ← tryEtaStruct tn' sn' with
  | (true, tn'Eqsn'?) => return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  | _ => pure ()
  let r ← tryStringLitExpansion tn' sn'
  if r != .undef then
    if r == .true then 
      return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? none)
    else
      return (false, none)
  let (r, tn'Eqsn'?) ← isDefEqUnitLike tn' sn'
  if r then
    return (true, ← mktEqs? tn' sn' tEqtn'? sEqsn'? tn'Eqsn'?)
  return (false, none)

def isDefEqCorePure' (t s : PExpr) : RecM Bool := do
  let (defEq, p?) ← isDefEqCore' t s
  assert 14 $ p? == none
  pure defEq


end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      isDefEqCorePure := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      whnfPure := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion
      inferTypePure := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      isDefEqCorePure := fun t s => isDefEqCorePure' t s (withFuel n)
      whnfCore := fun e r p => whnfCore' e r p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      whnfPure := fun e => whnfPure' e (withFuel n)
      inferType := fun e => inferType' e (withFuel n)
      inferTypePure := fun e => inferTypePure' e (withFuel n) }

/--
Runs `x` with a limit on the recursion depth.
-/
def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

/--
With the level context `lps`, infers the type of expression `e` and checks that
`e` is well-typed according to Lean's typing judgment.

Use `inferType` to infer type alone.
-/
def check (e : Expr) (lps : List Name) : MPE := do
  let ret ← withReader ({ · with lparams := lps }) (inferType e).run
  let (_, e'?) := ret

  if let some e' := e'? then
    for c in e'.toExpr.getUsedConstants do
      if not ((← getEnv).find? c).isSome then
        throw $ .other s!"possible patching loop detected ({c})"

  pure ret
  

def checkPure (e : Expr) (lps : List Name) : M PExpr :=
  withReader ({ · with lparams := lps }) (inferTypePure e.toPExpr).run

@[inherit_doc whnf']
def whnf (e : PExpr) (lps : List Name) : M PExpr := withReader ({ · with lparams := lps }) $ (Inner.whnfPure e).run

/--
Infers the type of expression `e`. Note that this uses the optimization
`inferOnly := false`, and so should only be used for the purpose of type
inference on terms that are known to be well-typed. To typecheck terms for the
first time, use `check`.
-/
def inferType (e : PExpr) (lps : List Name) : M PExpr := withReader ({ · with lparams := lps }) $ (Inner.inferTypePure e).run

@[inherit_doc isDefEqCore]
def isDefEq (t s : PExpr) (lps : List Name) : MB :=
  withReader ({ · with lparams := lps }) (Inner.isDefEq t s).run

def isDefEqPure (t s : PExpr) (lps : List Name) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqPure t s).run

@[inherit_doc ensureSortCore]
def ensureSort (t : PExpr) (lps : List Name) (s := t) : MEE := 
  withReader ({ · with lparams := lps }) $ RecM.run do 
    ensureSortCore t s

@[inherit_doc ensureSortCore]
def ensureSortPure (t : PExpr) (lps : List Name) (s := t) : M PExpr := withReader ({ · with lparams := lps }) $ RecM.run do 
  let (s, p?) ← (ensureSortCore t s)
  assert 15 $ p? == none
  pure s

@[inherit_doc ensureForallCore]
def ensureForall (t : PExpr) (lps : List Name) (s := t) : MEE := withReader ({ · with lparams := lps }) $ (ensureForallCore t s).run

def maybeCast (p? : Option EExpr) (typLhs typRhs e : PExpr) (lps : List Name) : M PExpr := 
  withReader ({ · with lparams := lps }) (Inner.maybeCast p? typLhs typRhs e).run

-- def test' : MetaM String := do
--   dbg_trace s!"test"
--   unreachable!
--   pure "HERE"
--
-- def test : MetaM Unit := do
--   let x ← test'
--   dbg_trace s!"{x}"
--
-- -- #eval test

/--
Ensures that `e` is defeq to some `e' := .sort (_ + 1)`, returning `e'`. If not,
throws an error with `s` (the expression required be a type).
-/
def ensureType (e : PExpr) (lps : List Name) : MEE := withReader ({ · with lparams := lps }) $ RecM.run $
  do ensureSortCore (← inferType e lps) e -- FIXME transport e using proof from ensureSort?

def ensureTypePure (e : PExpr) (lps : List Name) : M PExpr := do ensureSortPure (← inferType e lps) lps e -- FIXME transport e using proof from ensureSort?

-- def etaExpand (e : Expr) : M Expr :=
--   let rec loop fvars
--   | .lam name dom body bi => do
--     let d := dom.instantiateRev fvars
--     let id := ⟨← mkFreshId⟩
--     withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
--       let fvars := fvars.push (.fvar id)
--       loop fvars body
--   | it => do
--     let itType ← whnf <| (← inferType <| it.instantiateRev fvars).1
--     if !itType.isForall then return e
--     let rec loop2 fvars args
--     | 0, _ => throw .deepRecursion
--     | fuel + 1, .forallE name dom body bi => do
--       let d := dom.instantiateRev fvars
--       let id := ⟨← mkFreshId⟩
--       withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
--         let arg := .fvar id
--         let fvars := fvars.push arg
--         let args := args.push arg
--         loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
--     | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
--     loop2 fvars #[] 1000 itType
--   loop #[] e
