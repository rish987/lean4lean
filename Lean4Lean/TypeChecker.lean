import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.PExpr

namespace Lean

abbrev InferCache := HashMap Expr (PExpr × Option PExpr)
abbrev InferCacheP := HashMap Expr (PExpr)

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCacheP := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : HashSet (Expr × Expr) := {}

structure TypeChecker.Context where
  env : Environment
  lctx : PLocalContext := {}
  /--
  Mapping from free variables to proofs of their equality,
  introduced by isDefEqLambda.
  -/
  eqFVars : HashMap (FVarId × FVarId) PExpr := {}
  safety : DefinitionSafety := .safe
  lparams : List Name := []

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException
abbrev ME := M (PExpr × Option PExpr)
abbrev MB := M (Bool × Option PExpr)

def M.run (env : Environment) (safety : DefinitionSafety := .safe) (lctx : PLocalContext := {})
    (x : M α) : Except KernelException α :=
  x { env, safety, lctx } |>.run' {}

instance : MonadEnv M where
  getEnv := return (← read).env
  modifyEnv _ := pure ()

instance : MonadPLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance (priority := low) : MonadWithReaderOf PLocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

instance (priority := low) : MonadWithReaderOf (HashMap (FVarId × FVarId) PExpr) M where
  withReader f := withReader fun s => { s with eqFVars := f s.eqFVars }

structure Methods where
  isDefEqCore : PExpr → PExpr → MB
  whnfCore (e : PExpr) (cheapRec := false) (cheapProj := false) : ME
  whnf (e : PExpr) : ME
  inferType (e : Expr) : ME
  inferTypePure (e : PExpr) : M PExpr

abbrev RecM := ReaderT Methods M
abbrev RecE := RecM (PExpr × (Option PExpr))
abbrev RecB := RecM (Bool × (Option PExpr))
abbrev RecLB := RecM (LBool × (Option PExpr))

inductive ReductionStatus where
  | continue (tn sn : PExpr)
  | unknown (tn : PExpr) (ptn? : Option PExpr) (sn : PExpr) (psn? : Option PExpr)
  | bool (b : (Bool × Option PExpr))

namespace Inner

/--
Reduces `e` to its weak-head normal form.
-/
def whnf (e : PExpr) : RecE := fun m => m.whnf e

@[inline] def withLCtx [MonadWithReaderOf PLocalContext m] (lctx : PLocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withEqFVar [MonadWithReaderOf (HashMap (FVarId × FVarId) PExpr) m] (idt ids : FVarId) (eq : PExpr) (x : m α) : m α :=
  withReader (fun l => l.insert (idt, ids) eq) x

/--
Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not,
throws an error with `s` (the expression required be a sort).
NOTE: e must be a patched expression
-/
def ensureSortCore (e : PExpr) (s : Expr) : RecE := do
  if Expr.isSort e then return (e, none)
  let (e, p?) ← whnf e -- TODO (TC1) test that this works with an expr that need PI to reduce to Sort
  if e.toExpr.isSort then return (e, p?)
  throw <| .typeExpected (← getEnv) (← getLCtx) s

/--
Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not,
throws an error with `s := f a` (the application requiring `f` to be of
function type).
-/
def ensureForallCore (e : PExpr) (s : Expr) : RecE := do
  if Expr.isForall e then return (e, none)
  let (e, p?) ← whnf e -- TODO (TC2) test that this works with an expr that need PI to reduce to forAll
  if e.toExpr.isForall then return (e, p?)
  throw <| .funExpected (← getEnv) (← getLCtx) s

/--
Checks that `l` does not contain any level parameters not found in the context `tc`.
-/
def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except KernelException PExpr := do
  if let some decl := LocalContext.find? tc.lctx name then
    return decl.type.toPExpr
  throw <| .other "unknown free variable"

/--
Infers the type of `.const e ls`.
-/
def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except KernelException PExpr := do
  let e := Expr.const name ls
  -- should be okay as the environment should only contain patched constants
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if !inferOnly then
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
def inferType (e : Expr) : RecE := fun m => m.inferType e

def inferTypePure (e : PExpr) : RecM PExpr := fun m => m.inferTypePure e

def maybeCast (p? : Option Expr) (lvl : Level) (typLhs typRhs e : PExpr) : PExpr :=
  p?.map (fun p => sorry) |>.getD e

/--
Infers the type of lambda expression `e`.
-/
def inferLambda (e : Expr) : RecE := loop #[] false e where
  loop fvars domPatched : Expr → RecE
  | .lam name dom body bi => do
    let mut d := dom.instantiateRev fvars
    let (typ, d'?) ← inferType d
    let (typ', p?) ← ensureSortCore typ d -- TODO (TC1) if p? = some _, d'? must be cast. also make sure that typ needed to be patched
    let lvl := typ'.toExpr.sortLevel!
    let d' := maybeCast p? lvl.succ typ typ' (d'?.getD d.toPExpr)

    let id := ⟨← mkFreshId⟩
    withLCtx (LocalContext.mkLocalDecl (← getLCtx) id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let (r, e'?) ← inferType (e.instantiateRev fvars)
    let e' := e'?.getD e.toPExpr
    let r := r.toExpr.cheapBetaReduce |>.toPExpr
    let (rSort, r'?) ← inferType (r.instantiateRev fvars)
    let (rSort', p?) ← ensureSortCore rSort r -- TODO need to test this
    assert! r'? == none
    let lvl := rSort'.toExpr.sortLevel!
    let r' := maybeCast p? lvl.succ rSort rSort' r

    let patch := if domPatched || e'?.isSome then some $ (LocalContext.mkLambda (← getLCtx) fvars e').toPExpr else none
    -- TODO only return .some if any of the fvars had domains that were patched, or if e'? := some e'
    return ((LocalContext.mkForall (← getLCtx) fvars r').toPExpr, patch)

def inferLambdaPure (e : PExpr) : RecM PExpr := sorry

/--
Infers the type of for-all expression `e`.
-/
def inferForall (e : Expr) : RecE := loop #[] #[] false e where
  loop fvars us domPatched : Expr → RecE
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let (t, d'?) ← inferType d
    let (t', p?) ← ensureSortCore t d
    let lvl := t'.toExpr.sortLevel!
    let d' := maybeCast p? lvl.succ t t' (d'?.getD d.toPExpr)

    let us := us.push lvl
    let id := ⟨← mkFreshId⟩
    withLCtx (LocalContext.mkLocalDecl (← getLCtx) id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let (r, e'?) ← inferType (e.instantiateRev fvars)
    let (r', p?) ← ensureSortCore r e
    let lvl := r'.toExpr.sortLevel!
    let e' := maybeCast p? lvl.succ r r' (e'?.getD e.toPExpr)

    let patch := if domPatched || e'?.isSome || p?.isSome then .some $ (LocalContext.mkForall (← getLCtx) fvars e').toPExpr else none
    return (.sort <| us.foldr mkLevelIMax' lvl, patch)

def inferForallPure (e : PExpr) : RecM PExpr := sorry

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

def isDefEqCorePure (t s : PExpr) : RecM Bool := do
  pure (← isDefEqCore t s).1

@[inherit_doc isDefEqCore]
def isDefEq (t s : PExpr) : RecB := do
  let r ← isDefEqCore t s
  if r.1 then
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  pure r

def isDefEqPure (t s : PExpr) : RecM Bool := do
  pure (← isDefEq t s).1

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
    match fType with
    | .forallE _ _ body _ =>
      fType := body
    | _ =>
      fType := fType.toExpr.instantiateRevRange j i args |>.toPExpr
      let (fType', p?) ← ensureForallCore fType e -- TODO (TC2)
      assert! p? == none -- sanity check; f should already have been cast as necessary
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
def inferLet (e : Expr) : RecE := loop #[] #[] false e where
  loop fvars vals typePatched : Expr → RecE
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let (typeType, type'?) ← inferType type 
    let (typeType', pType?) ← ensureSortCore typeType type
    let lvl := typeType'.toExpr.sortLevel!
    let type' := maybeCast pType? lvl.succ typeType typeType' (type'?.getD type.toPExpr)
    let val := val.instantiateRev fvars
    let (valType, val'?) ← inferType val 
    let (defEq, pVal?) ← isDefEq valType type' -- FIXME order?
    if !defEq then
      throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type'
    let val' := maybeCast pVal? lvl valType type' (val'?.getD val.toPExpr)
    let id := ⟨← mkFreshId⟩
    withLCtx (LocalContext.mkLetDecl (← getLCtx) id name type' val') do
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
    let patch := if typePatched || e'?.isSome then .some $ LocalContext.mkForall (← getLCtx) fvars e' |>.toPExpr else none
    return (LocalContext.mkForall (← getLCtx) fvars r |>.toPExpr, patch)

def inferLetPure (e : PExpr) : RecM PExpr := sorry

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
def inferProj (typeName : Name) (idx : Nat) (struct : PExpr) (patched : Bool) (structType : PExpr) : RecE := do
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
    let (.forallE _ _ b _, p?) ← whnf r | fail -- FIXME use ensureForall?
    assert! p? == none -- FIXME can we guarantee this? if so should remove whnf, if not need to "cast" `c` in Inductive.add
    r := b.toExpr.instantiate1 args[i]! |>.toPExpr
  let (isPropType, p?) := ← isProp type
  for i in [:idx] do
    let (.forallE _ dom b _, p?) ← whnf r | fail -- FIXME use ensureForall?
    assert! p? == none -- FIXME
    if b.toExpr.hasLooseBVars then
      -- prop structs cannot have non-prop dependent fields
      let (isPropDom, p?) := ← isProp dom
      if isPropType then if !isPropDom then fail
      r := b.toExpr.instantiate1 (.proj I_name i struct) |>.toPExpr
    else
      r := b
  let (.forallE _ dom _ _, p?) ← whnf r | fail -- FIXME use ensureForall?
  assert! p? == none -- FIXME
  let (isPropDom, p?) := ← isProp dom
  assert! p? == none -- FIXME
  if isPropType then if !isPropDom then fail
  let patched := patched || pType?.isSome
  let patch := if patched then some (.proj typeName idx struct) else none
  return (dom, patch)

def inferProjPure (typeName : Name) (idx : Nat) (struct : Expr) (structType : Expr) (structp? : Option Expr) : RecM PExpr := sorry

/--
Gets the universe level of the sort that the type of `e` inhabits.
-/
def getTypeLevel (e : PExpr) : RecM (Level × PExpr) := do
  let eType ← inferTypePure e
  let eTypeSort ← inferTypePure eType
  let (eTypeSort', es?) ← ensureSortCore eTypeSort eType
  assert! es? == none
  pure (eTypeSort'.toExpr.sortLevel!, eType)

@[inherit_doc inferType]
def inferType' (e : Expr) : RecE := do
  if e.isBVar then
    throw <| .other
      s!"type checker does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert! !e.hasLooseBVars
  let state ← get
  if let some r := state.inferTypeC.find? e then
    return r
  let (r, ep?) ← match e with
    | .lit l => pure (l.type.toPExpr, none)
    | .mdata _ e => inferType' e
    | .proj s idx e =>
      let (t, e'?) ← inferType' e
      let e' := e'?.getD e.toPExpr
      inferProj s idx e' e'?.isSome t
    | .fvar n => pure (← inferFVar (← readThe Context) n, none)
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      checkLevel (← readThe Context) l
      pure <| (.sort (.succ l), none)
    | .const c ls => pure (← inferConstant (← readThe Context) c ls false, none)
    | .lam .. => inferLambda e
    | .forallE .. => inferForall e
    | .app f a =>
      let (fType, f'?) ← inferType' f
      let (fTypeSort, fType''?) ← inferType fType
      assert! fType''? == none
      let (fTypeSort', fs?) ← ensureSortCore fTypeSort fType
      assert! fs? == none
      let fTypeLvl := fTypeSort'.toExpr.sortLevel!
      let (fType', pf'?) ← ensureForallCore fType f
      let f' := maybeCast pf'? fTypeLvl fType fType' (f'?.getD f.toPExpr)

      let (aType, a'?) ← inferType' a
      let (aTypeLvl, _) ← getTypeLevel (a'?.getD a.toPExpr)

      let dType := Expr.bindingDomain! fType |>.toPExpr
      -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
      -- for some universe level `l`, so this use of `isDefEq` is valid
      let (defEq, pa'?) ← isDefEq aType dType
      let a' := maybeCast pa'? aTypeLvl aType dType (a'?.getD a.toPExpr)
      if defEq then
        let patch := if f'?.isSome || a'?.isSome || pf'?.isSome || pa'?.isSome then .some (.app f' a') else none
        pure ((Expr.bindingBody! fType).instantiate1 a' |>.toPExpr, patch)
      else
        throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
    | .letE .. => inferLet e
  modify fun s => { s with inferTypeC := s.inferTypeC.insert e (r, ep?) }
  return (r, ep?)

def inferTypePure' (e : PExpr) : RecM PExpr := do
  if e.toExpr.isBVar then
    throw <| .other
      s!"type checker does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert! !e.toExpr.hasLooseBVars
  let state ← get
  if let some r := state.inferTypeI.find? e then
    return r
  let r ← match e with
    | .lit l => pure l.type.toPExpr
    | .mdata _ e => inferTypePure' e
    | .proj s idx e =>
      let t ← inferTypePure' e
      inferProjPure s idx e t .none
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls true
    | .lam .. => inferLambdaPure e
    | .forallE .. => inferForallPure e
    | .app .. => inferApp e
    | .letE .. => inferLetPure e
  modify fun s => { s with inferTypeI := s.inferTypeI.insert e r }
  return r

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
def whnfCore (e : PExpr) (cheapRec := false) (cheapProj := false) : RecE :=
  fun m => m.whnfCore e cheapRec cheapProj

def reduceRecursor (e : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let env ← getEnv
  if env.header.quotInit then
    if let some r ← quotReduceRec e whnf then
      return r
  let whnf' e := if cheapRec then whnfCore e cheapRec cheapProj else whnf e
  if let some r ← inductiveReduceRec env e whnf' inferTypePure isDefEqPure then
    return r
  return none

/--
Gets the weak-head normal form of the free variable `e`,
which is the weak-head normal form of its definition if `e` is a let variable and itself if it is a lambda variable.
-/
def whnfFVar (e : Expr) (cheapRec cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapRec cheapProj
  return e

/--
Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a
constructor application).
-/
def reduceProj (idx : Nat) (struct : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let mut c ← (if cheapProj then whnfCore struct cheapRec cheapProj else whnf struct)
  if let .lit (.strVal s) := c then
    c := .strLitToConstructor s
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

@[inherit_doc whnfCore]
def whnfCore' (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapRec cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache.find? e then
    return r
  let rec save r := do
    if !cheapRec && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapRec cheapProj
  | .app .. => -- beta-reduce at the head as much as possible, apply any remaining `rargs` to the resulting expression, and re-run `whnfCore`
    e.withAppRev fun f0 rargs => do
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let f ← whnfCore f0 cheapRec cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecM Expr :=
        let cont2 := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r cheapRec cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont2
        else cont2
      loop 1 body
    else if f == f0 then
      if let some r ← reduceRecursor e cheapRec cheapProj then
        whnfCore r cheapRec cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      -- FIXME replace with reduceRecursor? adding arguments can only result in further normalization if the head reduced to a partial recursor application
      save <|← whnfCore r cheapRec cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapRec cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapRec cheapProj then
      save <|← whnfCore m cheapRec cheapProj
    else
      save e

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its `ConstantInfo` if so.
-/
def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c _ := e.getAppFn then
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

/--
Checks if `e` has a head constant that can be delta-reduced (that is, it is a
theorem or definition), returning its value (instantiated by level parameters)
if so.
-/
def unfoldDefinitionCore (env : Environment) (e : Expr) : Option Expr := do
  if let .const _ ls := e then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        return d.instantiateValueLevelParams! ls
  none

/--
Unfolds the definition at the head of the application `e` (or `e` itself if it
is not an application).
-/
def unfoldDefinition (env : Environment) (e : Expr) : Option Expr := do
  if e.isApp then
    let f0 := e.getAppFn
    if let some f := unfoldDefinitionCore env f0 then
      let rargs := e.getAppRevArgs
      return f.mkAppRevRange 0 rargs.size rargs
    none
  else
    unfoldDefinitionCore env e

def reduceNative (_env : Environment) (e : Expr) : Except KernelException (Option Expr) := do
  let .app f (.const c _) := e | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def natLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.natLit?

/--
Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced
to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := natLitExt? (← whnf a) | return none
  let some v2 := natLitExt? (← whnf b) | return none
  return some <| .lit <| .natVal <| f v1 v2

/--
Reduces the application `f a b` to a boolean expression if `a` and `b` can be
reduced to Nat literals.

Note: `f` should have an (efficient) external implementation.
-/
def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := natLitExt? (← whnf a) | return none
  let some v2 := natLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

/--
Reduces `e` to a natural number literal if possible, where binary operations
and predicates may be applied (provided they have an external implementation).
These include: `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`,
`Nat.mod`, `Nat.div`, `Nat.beq`, `Nat.ble`.
-/
def reduceNat (e : Expr) : RecM (Option Expr) := do
  if e.hasFVar then return none
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := natLitExt? (← whnf e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reduceBinNatOp Nat.pow a b
    if f == ``Nat.gcd then return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
  return none

@[inherit_doc whnf]
def whnf' (e : Expr) : RecM Expr := do
  -- Do not cache easy cases
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
  | .mdata _ e => return ← whnf' e
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return e
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  if let some r := (← get).whnfCache.find? e then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let t ← whnfCore' t
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t := unfoldDefinition env t | return t
    loop t fuel
  let r ← loop e 1000
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

def mkRefl (lvl : Level) (T : PExpr) (t : PExpr) : PExpr :=
  Lean.mkAppN (.const `Eq.refl [lvl]) #[T, t] |>.toPExpr

def mkHRefl (lvl : Level) (T : PExpr) (t : PExpr) : PExpr :=
  Lean.mkAppN (.const `HEq.refl [lvl]) #[T, t] |>.toPExpr

def isDefEqBinder (binDatas : Array ((Name × PExpr × PExpr × BinderInfo) × (Name × PExpr × PExpr × BinderInfo)))
(f : PExpr → PExpr → Option PExpr → Array PExpr → Array PExpr → Array PExpr → Array (Option PExpr) → RecM (Option PExpr))
: RecB := do
  let rec loop idx tvars svars teqsvars domEqs : RecB := do
    let ((tName, tDom, tBody, tBi), (sName, sDom, sBody, sBi)) := binDatas.get! idx
    let (tType, sType, p?) ← if tDom != sDom then
      let tType := tDom.instantiateRev tvars
      let sType := sDom.instantiateRev svars
      let (defEq, p?) ← isDefEq tType sType
      if !defEq then return (false, none)
      pure (some tType, some sType, p?)
    else pure (none, none, none)
    let tType := tType.getD (tDom.instantiateRev tvars)
    let sType := sType.getD (sDom.instantiateRev svars)
    let idt := ⟨← mkFreshId⟩
    let ids := ⟨← mkFreshId⟩
    let idteqs := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).toLocalContext.mkLocalDecl idt tName tType tBi) do
      withLCtx ((← getLCtx).toLocalContext.mkLocalDecl ids sName sType sBi) do
        let teqsType : PExpr := default -- TODO
        withLCtx ((← getLCtx).toLocalContext.mkLocalDecl idteqs default teqsType default) do
          withEqFVar ids idt teqsType do
            let tvars := tvars.push (.fvar idt)
            let svars := svars.push (.fvar ids)
            let teqsvars := teqsvars.push (.fvar idteqs)
            let domEqs := domEqs.push p?
            if _h : idx < binDatas.size - 1 then
              loop (idx + 1) tvars svars teqsvars domEqs
            else
              -- FIXME FIXME acc? may be some if `idteqs` was used in `isDefEqFVar`
              let tBody := tBody.instantiateRev tvars
              let sBody := sBody.instantiateRev tvars
              let mut (defEq, ptbodEqsbod?) ← isDefEq tBody sBody
              if !defEq then return (false, none)
              pure (true, ← f tBody sBody ptbodEqsbod? tvars.reverse svars.reverse teqsvars.reverse domEqs.reverse) -- FIXME can iterate backwards instead of reversing lists?
  termination_by (binDatas.size - 1) - idx
  loop 0 #[] #[] #[] #[]

/--
If `t` and `s` are lambda expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqLambda (t s : PExpr) : RecB :=
  let rec getData t s := 
    match t, s with
    | .lam tName tDom tBody tBi, .lam sName sDom sBody sBi => 
      #[((tName, tDom, tBody, tBi), (sName, sDom, sBody, sBi))] ++ getData tBody sBody
    | _, _ =>
      #[]
  isDefEqBinder (getData t s) fun fa gb pfaEqgb? as bs aEqbs pAEqBs? => do
    let mut pfaEqgb? := pfaEqgb?
    let mut fa := fa
    let mut gb := gb
    for (((a, b), aEqb), pAEqB?) in as.zip bs |>.zip aEqbs |>.zip pAEqBs? do
      if pAEqB?.isSome || pfaEqgb?.isSome then
        let (ALvl, A) ← getTypeLevel a
        let AType ← inferTypePure A
        let B ← inferTypePure b
        let u := ALvl

        let (UaLvl, Ua) ← getTypeLevel fa
        let Vb ← inferTypePure gb
        let v := UaLvl
        let U := LocalContext.mkForall (← getLCtx) #[a] Ua
        let V := LocalContext.mkForall (← getLCtx) #[b] Vb

        let hfg := LocalContext.mkForall (← getLCtx) #[a, b, aEqb] (pfaEqgb?.getD (mkHRefl UaLvl Ua fa))
        let hAB := pAEqB?.getD (mkRefl ALvl.succ AType A)

        let f := LocalContext.mkLambda (← getLCtx) #[a] fa |>.toPExpr
        let g := LocalContext.mkLambda (← getLCtx) #[b] gb |>.toPExpr
        pfaEqgb? := .some $ Lean.mkAppN (.const `FIXME [u, v]) #[A, B, U, V, f, g, hAB, hfg] |>.toPExpr -- TODO build application of `heqThm`
        fa := f
        gb := g
    pure pfaEqgb?

/--
If `t` and `s` are for-all expressions, checks that their domains are defeq and
recurses on the bodies, substituting in a new free variable for that binder
(this substitution is delayed for efficiency purposes using the `subst`
parameter). Otherwise, does a normal defeq check.
-/
def isDefEqForall (t s : PExpr) : RecB :=
  let rec getData t s := 
    match t, s with
    | .forallE tName tDom tBody tBi, .forallE sName sDom sBody sBi => 
      #[((tName, tDom, tBody, tBi), (sName, sDom, sBody, sBi))] ++ getData tBody sBody
    | _, _ =>
      #[]
  isDefEqBinder (getData t s) fun Ua Vb pUaEqVb? as bs aEqbs pAEqBs? => do
    let mut pUaEqVb? := pUaEqVb?
    let mut Ua := Ua
    let mut Vb := Vb
    for (((a, b), aEqb), pAEqB?) in as.zip bs |>.zip aEqbs |>.zip pAEqBs? do
      if pAEqB?.isSome || pUaEqVb?.isSome then
        let (ALvl, A) ← getTypeLevel a
        let AType ← inferTypePure A
        let B ← inferTypePure b
        let u := ALvl

        let (UaTypeLvl, UaType) ← getTypeLevel Ua
        let UaLvl := UaType.toExpr.sortLevel!
        let v := UaLvl

        let hUV := LocalContext.mkForall (← getLCtx) #[a, b, aEqb] (pUaEqVb?.getD (mkHRefl UaTypeLvl UaType Ua))
        let hAB := pAEqB?.getD (mkRefl ALvl.succ AType A)

        let U := LocalContext.mkForall (← getLCtx) #[a] Ua |>.toPExpr
        let V := LocalContext.mkForall (← getLCtx) #[b] Vb |>.toPExpr
        pUaEqVb? := .some $ Lean.mkAppN (.const `FIXME [u, v]) #[A, B, U, V, hAB, hUV] |>.toPExpr -- TODO build application of `heqThm`
        Ua := U
        Vb := V
    pure pUaEqVb?


def appHEqSymm? (t s : PExpr) (theqs? : Option PExpr) : RecM (Option PExpr) := do
  let some theqs := theqs? | return none
  let (lvl, tType) ← getTypeLevel t
  let (sType, _) ← inferType s
  pure $ Lean.mkAppN (.const `FIXME [lvl]) #[tType, sType, t, s, theqs] |>.toPExpr

def appHEqTrans? (t s r : PExpr) (theqs? sheqr? : Option PExpr) : RecM (Option PExpr) := do
  let (lvl, tType) ← getTypeLevel t
  let (sType, _) ← inferType s
  let (rType, _) ← inferType r
  match theqs?, sheqr? with
  | none, none => return none
  | .some theqs, .some sheqr => return Lean.mkAppN (.const `FIXME [lvl]) #[tType, sType, rType, t, s, r, theqs, sheqr] |>.toPExpr
  | none, .some sheqr => return sheqr
  | .some theqs, none => return theqs

def isDefEqFVar (idt ids : FVarId) : RecB := do
  if let some p := (← readThe Context).eqFVars.find? (idt, ids) then
    return (true, some p)
  else if let some p := (← readThe Context).eqFVars.find? (ids, idt) then
    -- TODO need to apply symm to p
    return (true, ← appHEqSymm? (.fvar idt) (.fvar ids) p)
  return (false, none)

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
  let res : Option (Bool × PExpr) ← match t, s with
  | .lam .., .lam .. => pure $ some $ ← isDefEqLambda t s
  | .fvar idt, .fvar ids => pure $ some $ ← isDefEqFVar idt ids
  | .forallE .., .forallE .. => pure $ some $ ← isDefEqForall t s
  | .sort a1, .sort a2 => pure $ some $ ((a1.isEquiv a2), none)
  | .mdata _ a1, .mdata _ a2 => pure $ some $ ← isDefEq a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure $ some ((a1 == a2), none)
  | _, _ => pure none
  let some (defeq, p?) := res | return (LBool.undef, none)
  pure (defeq.toLBool, p?)

/--
Assuming that `t` and `s` have the same constant heads, returns true if they
are applications with definitionally equal arguments (in which case they are
defeq), and false otherwise (deferring further defeq checking to caller).
-/
def isDefEqArgs (t s : Expr) : RecB := do
  match t, s with
  | .app tf ta, .app sf sa =>
    let (r, proofArg?) ← isDefEq ta sa
    if !r then return (false, none)
    
    let (r, proofFn?) ← isDefEqArgs tf sf
    return (r, sorry)  -- TODO construct proof (none if !r)
  | .app .., _ | _, .app .. => return (false, none)
  | _, _ => return (true, none)

/--
Checks if `t` and `s` are defeq after applying η-expansion to `s`.

Assuming that `s` has a function type `(x : A) -> B x`, it η-expands to
`fun (x : A) => s x` (which it is definitionally equal to by the η rule).
-/
def tryEtaExpansionCore (t s : Expr) : RecB := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf (← inferTypePure s) | return (false, none)
    isDefEq t (.lam name ty (.app s (.bvar 0)) bi) -- NOTE: same proof should be okay because of eta-expansion when typechecking
  else return (false, none)

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : Expr) : RecB := do
  match ← tryEtaExpansionCore t s with
  | ret@(true, _) => pure ret
  | (false, _) => tryEtaExpansionCore s t

/--
Checks if `t` and `s` are application-defeq (as in `isDefEqApp`)
after applying struct-η-expansion to `t`.

Assuming that `s` has a struct type `S` constructor `S.mk` and projection
functions `pᵢ : S → Tᵢ`, it struct-η-expands to `S.mk (p₁ s) ... (pₙ s)` (which
it is definitionally equal to by the struct-η rule).
-/
def tryEtaStructCore (t s : Expr) : RecB := do
  let .const f _ := s.getAppFn | return (false, none)
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return (false, none)
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return (false, none)
  unless isStructureLike env fInfo.induct do return (false, none)
  unless ← isDefEqPure (← inferTypePure t) (← inferTypePure s) do return (false, none)
  let args := s.getAppArgs
  let mut proofs : Array $ Option Expr := #[]
  for h : i in [fInfo.numParams:args.size] do
    let (r, proof?) ← isDefEq (.proj fInfo.induct (i - fInfo.numParams) t) (args[i]'h.2)
    unless r do return (false, none)
    -- TODO construct congruence expressions (the above isDefEq check should ensure a certain form)
    proofs := proofs ++ [proof?]
  let proof? := sorry -- TODO linearly construct proof from `proofs`
  return (true, proof?)

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : Expr) : RecB := do
  match ← tryEtaStructCore t s with
  | ret@(true, _) => pure ret
  | (false, _) => tryEtaStructCore s t

/--
Checks if applications `t` and `s` (should be WHNF) are defeq on account of
their function heads and arguments being defeq.
-/
def isDefEqApp (t s : Expr) : RecB := do
  unless t.isApp && s.isApp do return (false, none)
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  unless tArgs.size == sArgs.size do return (false, none)
  let (r, proofHead?) ← isDefEq tf sf
  let mut proof? := proofHead?
  unless r do return (false, none)
  for ta in tArgs, sa in sArgs do
    let (r, proofArg?) ← isDefEq tf sf
    -- TODO modify proof? according to proofArf?
    proof? := sorry
    unless r do return (false, none)
  return (true, proof?)

/--
Checks if `t` and `s` are definitionally equivalent according to proof irrelevance
(that is, they are proofs of the same proposition).
-/
def isDefEqProofIrrel (t s : PExpr) : RecLB := do
  let tType ← inferTypePure t
  let (prop, pprop?) ← isProp tType
  assert! pprop? == none
  if !prop then return (.undef, none)
  let sType ← inferTypePure s
  let (ret, pt?) ← isDefEq tType sType
  if ret == .true then
    let pt := pt?.getD (mkRefl 1 (.sort 0) tType)
    let p := Lean.mkAppN (.const `FIXME []) #[tType, sType, pt, t, s] |>.toPExpr
    return (.true, .none) -- FIXME return .some p
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

def tryUnfoldProjApp (e : Expr) : RecM (Option Expr) := do
  let f := e.getAppFn
  if !f.isProj then return none
  let e' ← whnfCore e
  return if e' != e then e' else none

/--
Performs a single step of δ-reduction on `tn`, `sn`, or both (according to
optimizations) followed by weak-head normalization (without further
δ-reduction). If the resulting terms have matching head constructors (excluding
non-α-equivalent applications and projections) returns whether `tn` and `sn`
are defeq. Otherwise, a return value indicates to the calling
`lazyDeltaReduction` that δ-reduction is to be continued.

If δ-reduction+weak-head-normalization cannot be continued (i.e. we have a
weak-head normal form (with cheapProj := true)), defers further defeq-checking
to `isDefEq`.
-/
def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := whnfCore (unfoldDefinition env e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .bool (true, sorry) -- TODO ???
    | .false => .bool (false, sorry)
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    -- FIXME hasn't whnfCore already been called on sn? so when would this case arise?
    if let some sn' ← tryUnfoldProjApp sn then
      cont tn sn'
    else
      cont (← delta tn) sn
  | none, some _ =>
    if let some tn' ← tryUnfoldProjApp tn then
      cont tn' sn
    else
      cont tn (← delta sn)
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      cont tn (← delta sn)
    else if hs.lt' ht then
      cont (← delta tn) sn
    else
      if tn.isApp && sn.isApp && (unsafe ptrEq dt ds) && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          let (r, proof?) ← isDefEqArgs tn sn
          if r then
            return .bool (true, proof?)
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : PExpr → Option PExpr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
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
    let p? := p?.map fun p => sorry
    pure (ret.toLBool, p?) -- TODO construct equality proof from proof?
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
def lazyDeltaReduction (tn sn : PExpr) : RecM ReductionStatus := loop tn sn 1000 where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let (r, proof?) ← isDefEqOffset tn sn
    if r != .undef then
      if (r == .true) then
        return .bool (true, proof?)
      else
        return .bool (false, none)
    if !tn.hasFVar && !sn.hasFVar then
      if let some tn' ← reduceNat tn then
        return .bool (← isDefEqCore tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool (← isDefEqCore tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      -- TODO does this case ever happen?
      return .bool (← isDefEqCore tn' sn)
    else if let some sn' ← reduceNative env sn then
      -- TODO does this case ever happen?
      return .bool (← isDefEqCore tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

/--
If `t` is a string literal and `s` is a string constructor application,
checks that they are defeq after turning `t` into a constructor application.
Otherwise, defers to the calling function.
-/
def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCorePure (.strLitToConstructor st) s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/--
Checks if `t` and `s` are defeq on account of both being of a unit type (a type
with one constructor without any fields or indices).
-/
-- NOTE: It is okay for this to be a non-congruence-proving function,
-- because any two instances of a unit type must be definitionally equal to a constructor application
def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf (← inferTypePure t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCorePure tType (← inferTypePure s)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : PExpr) : RecB := do
  let (r, pteqs?) ← quickIsDefEq t s (useHash := true)
  if r != .undef then return (r == .true, pteqs?)

  if !t.toExpr.hasFVar && s.toExpr.isConstOf ``true then
    let (t, p?) ← whnf t
    if t.toExpr.isConstOf ``true then return (true, p?)

  let mut (tn, ptn?) ← whnfCore t (cheapProj := true)
  let mut (sn, psn?) ← whnfCore s (cheapProj := true)

  let mkTrans? (ptneqsn? : Option PExpr) := do appHEqTrans? t sn s (← appHEqTrans? t tn sn ptn? ptneqsn?) (← appHEqSymm? s sn psn?)

  if !(unsafe ptrEq tn t && ptrEq sn s) then
    let (r, ptneqsn?) ← quickIsDefEq tn sn
    if r == .false then
      return (false, none)
    else if r == .true then
      return (true, ← mkTrans? ptneqsn?)

  let (r, p?) ← isDefEqProofIrrel tn sn
  if r != .undef then 
    if r == .true then
      return (true, ← mkTrans? p?)
    return (false, none)

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .bool b => return b
  | .unknown tn' sn' =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return (true, none)
  | .fvar tv, .fvar sv => if tv == sv then return (true, none)
  | .proj _ ti te, .proj _ si se =>
    if ti == si then
      -- optimized by `lazyDeltaReductionStep` using `cheapProj = true`
      let (r, proof?) ← isDefEq te se
      if r then
        -- TODO construct proof from proof?
        return (true, sorry)
  | _, _ => pure ()

  -- `lazyDeltaReductionStep` used `cheapProj = true`, so we may not have a complete WHNF
  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(unsafe ptrEq tnn tn && ptrEq snn sn) then
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    return ← isDefEqCore tnn snn

  -- tn and sn are both in WHNF
  match ← isDefEqApp tn sn with
  | ret@(true, _) => return ret
  | _ => pure ()
  match ← tryEtaExpansion tn sn with
  | ret@(true, _) => return ret
  | _ => pure ()
  match ← tryEtaStruct tn sn with
  | ret@(true, _) => return ret
  | _ => pure ()
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return (r == .true, none)
  if ← isDefEqUnitLike tn sn then return (true, none)
  return (false, none)

end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      whnfCore := fun e r p => whnfCore' e r p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      inferType := fun e i => inferType' e i (withFuel n) }

/--
Runs `x` with a limit on the recursion depth.
-/
def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

/--
With the level context `lps`, infers the type of expression `e` and checks that
`e` is well-typed according to Lean's typing judgment.

Use `inferType` to infer type alone.
-/
def check (e : Expr) (lps : List Name) : ME :=
  withReader ({ · with lparams := lps }) (inferType e (inferOnly := false)).run

@[inherit_doc whnf']
def whnf (e : Expr) : M Expr := (Inner.whnf e).run

/--
Infers the type of expression `e`. Note that this uses the optimization
`inferOnly := false`, and so should only be used for the purpose of type
inference on terms that are known to be well-typed. To typecheck terms for the
first time, use `check`.
-/
def inferType (e : Expr) : ME := (Inner.inferType e).run

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : MB := (Inner.isDefEq t s).run

@[inherit_doc ensureSortCore]
def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

@[inherit_doc ensureForallCore]
def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

/--
Ensures that `e` is defeq to some `e' := .sort (_ + 1)`, returning `e'`. If not,
throws an error with `s` (the expression required be a type).
-/
def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e).1 e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars body
  | it => do
    let itType ← whnf <| (← inferType <| it.instantiateRev fvars).1
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
        let arg := .fvar id
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] 1000 itType
  loop #[] e
