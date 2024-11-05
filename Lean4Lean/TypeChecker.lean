import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager

-- 72

namespace Lean

abbrev InferCache := ExprMap Expr

structure TypeChecker.Data where
usedProofIrrelevance : Bool := false
usedKLikeReduction : Bool := false
maxRecursionDepth : Nat := 0

structure TypeChecker.State where
  nid : Nat := 0
  fvarTypeToReusedNamePrefix : Std.HashMap Expr Name := {}
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  data : Data := {}
  whnfCoreCache : ExprMap Expr := {}
  fvarNormCache : Std.HashMap (Expr × Expr) (Expr × Expr) := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  numCalls : Nat := 0
  failure : Std.HashSet (Expr × Expr) := {}

inductive CallData where
|  isDefEqCore : Expr → Expr → CallData
|  whnfCore (e : Expr) (cheapRec : Bool) (cheapProj : Bool) : CallData
|  whnf (e : Expr) : CallData
|  inferType (e : Expr) (inferOnly : Bool) : CallData
deriving Inhabited

instance : ToString CallData where
toString
| .isDefEqCore t s     => s!"isDefEqCore ({t}) ({s})"
| .whnfCore e k p      => s!"whnfCore ({e}) {k} {p}"
| .whnf e              => s!"whnf ({e})"
| .inferType e d       => s!"inferType ({e}) ({d})"

def CallData.name : CallData → String
| .isDefEqCore ..     => "isDefEqCore"
| .whnfCore ..        => "whnfCore"
| .whnf ..            => "whnf"
| .inferType ..       => "inferType"

@[reducible]
def CallDataT : CallData → Type
| .isDefEqCore ..     => Bool
| .whnfCore ..        => Expr
| .whnf ..            => Expr
| .inferType ..       => Expr

structure TypeCheckerOpts where
  proofIrrelevance := true
  kLikeReduction := true

structure TypeChecker.Context where
  dbg : Nat := 0
  env : Environment
  opts : TypeCheckerOpts := {}
  lctx : LocalContext := {}
  safety : DefinitionSafety := .safe
  callId : Nat := 0
  trace : Bool := false
  dbgCallId : Option Nat := none
  callStack : Array (Nat × Nat × CallData) := #[]
  lparams : List Name := []

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException

def M.run (env : Environment) (x : M α)
   (safety : DefinitionSafety := .safe) (opts : TypeCheckerOpts := {}) (lctx : LocalContext := {}) (lparams : List Name := {}) (nid : Nat := 0) (fvarTypeToReusedNamePrefix : Std.HashMap Expr Name := {}) (trace := false) (state : State := {}) : Except KernelException (α × State) := do
  x {env, safety, lctx, opts, lparams, trace} |>.run {state with nid, fvarTypeToReusedNamePrefix}

def M.run' (env : Environment) (x : M α)
   (safety : DefinitionSafety := .safe) (opts : TypeCheckerOpts := {}) (lctx : LocalContext := {}) (lparams : List Name := {}) (nid : Nat := 0) (fvarTypeToReusedNamePrefix : Std.HashMap Expr Name := {}) (trace := false) : Except KernelException α := do
  x { env, safety, lctx, opts, lparams, trace} |>.run' {nid, fvarTypeToReusedNamePrefix}

instance : MonadEnv M where
  getEnv := return (← read).env
  modifyEnv _ := pure ()

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

def mkNewId : M Name := do
  let nid := (← get).nid
  modify fun st => { st with nid := st.nid + 1 }
  pure $ .mkNum `_kernel_fresh nid

def mkId (dom : Expr) : M Name := do
  if let some np := (← get).fvarTypeToReusedNamePrefix[dom]? then
    let mut count := 0
    while (← getLCtx).findFVar? (Expr.fvar $ .mk (Name.mkNum np count)) |>.isSome do
      count := count + 1
    pure $ Name.mkNum np count
  else
    let np ← mkNewId
    modify fun st => { st with fvarTypeToReusedNamePrefix := st.fvarTypeToReusedNamePrefix.insert dom np }
    pure $ Name.mkNum np 0

structure Methods where
  isDefEqCore : Nat → Expr → Expr → M Bool
  whnfCore (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : M Expr
  whnf (n : Nat) (e : Expr) : M Expr
  inferType (n : Nat) (e : Expr) (inferOnly : Bool) : M Expr

abbrev RecM := ReaderT Methods M

def callStackToStr : M String := do 
  let l := (← readThe Context).callStack.map fun d => s!"{d.1}/{d.2.1}"
  pure $ s!"{l}"

def traceM (msg : String) : M Unit := do
  if (← readThe Context).callId == (← readThe Context).dbgCallId then
    dbg_trace msg

def shouldTrace : M Bool := do
  pure $ (← readThe Context).trace && (← readThe Context).callStack.any (·.2.1 == (← readThe Context).dbgCallId)

def trace (msg : String) : RecM Unit := do
  if ← shouldTrace then
    dbg_trace msg

def dotrace (msg : Unit → RecM String) : RecM Unit := do
  if ← shouldTrace then
    trace (← msg ())

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | bool (b : Bool)

namespace Inner

def whnf (n : Nat) (e : Expr) : RecM Expr := fun m => m.whnf n e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withDbg [MonadWithReaderOf Context m] (i : Nat) (x : m α) : m α :=
  withReader (fun l => {l with dbg := i}) x

@[inline] def rctx [MonadReaderOf Context m] : m Context := (readThe Context)

@[inline] def withCallData [MonadWithReaderOf Context m] (i : Nat) (id : Nat) (d : CallData) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, id, d)}) x

@[inline] def withCallId [MonadWithReaderOf Context m] (id : Nat) (dbgCallId : Option Nat := none) (x : m α) : m α :=
  withReader (fun c => {c with callId := id, dbgCallId}) x

def ensureSortCore (e s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf 1 e
  if e.isSort then return e
  throw <| .typeExpected (← getEnv) (← getLCtx) s

def ensureForallCore (e s : Expr) : RecM Expr := do
  if e.isForall then return e
  let e' ← whnf 2 e
  if e'.isForall then return e'
  throw <| .funExpected (← getEnv) (← getLCtx) s

def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except KernelException Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other s!"unknown free variable '{name.name}'"

def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except KernelException Expr := do
  let e := Expr.const name ls
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
  return info.instantiateTypeLevelParams ls

def inferType (n : Nat) (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType n e inferOnly

def inferLambda (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkId d⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      if !inferOnly then
        _ ← ensureSortCore (← inferType 3 d inferOnly) d
      loop fvars body
  | e => do
    let r ← inferType 4 (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

def inferForall (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars us : Expr → RecM Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType 5 d inferOnly) d
    let us := us.push t1.sortLevel!
    let id := ⟨← mkId d⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us body
  | e => do
    let r ← inferType 6 (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!

def isDefEqCore (n : Nat) (t s : Expr) : RecM Bool := fun m => m.isDefEqCore n t s

/--
  Optimized version of Lean.Expr.containsFVar, assuming no bound vars in `e`.
-/
def _root_.Lean.Expr.containsFVar' (e : Expr) (fv : FVarId) : Bool :=
  (e.replaceFVar (.fvar fv) (Expr.bvar 0)).hasLooseBVars

def fvarNormalize (t s : Expr) : RecM (Expr × Expr) := do
  if ! (t.hasFVar || s.hasFVar) then return (t, s)
  -- if let some (t', s') := (← get).fvarNormCache.get? (t, s) then 
  --   return (t', s')

  let mut zeroFVarClasses : Std.HashMap Name (Option Nat) := default
  let mut tNorm := t
  let mut sNorm := s

  for fvar in (← getLCtx).getFVars do
    let fid := fvar.fvarId!
    let pref := fvar.fvarId!.name.getPrefix

    let n? := zeroFVarClasses.get? pref
    if let .some .none := n? then continue

    if t.containsFVar' fid || s.containsFVar' fid then
      let suff :=  match fid.name with
      | .num _ s   => s
      | _   => unreachable!
      if suff == 0 then
        zeroFVarClasses := zeroFVarClasses.insert pref none
        continue
      let n ← if let .some n := n? then
        pure n.get!
      else
        zeroFVarClasses := zeroFVarClasses.insert pref (.some suff)
        pure suff

      tNorm := tNorm.replaceFVar (.fvar $ .mk (.mkNum pref suff)) (.fvar $ .mk (.mkNum pref (suff - n)))
      sNorm := sNorm.replaceFVar (.fvar $ .mk (.mkNum pref suff)) (.fvar $ .mk (.mkNum pref (suff - n)))

  pure (tNorm, sNorm)

def isDefEq (n : Nat) (t s : Expr) : RecM Bool := do
  let r ← isDefEqCore n t s
  if r then
    let (tCache, sCache) ← fvarNormalize t s
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv tCache sCache }
  pure r

def inferApp (e : Expr) : RecM Expr := do
  e.withApp fun f args => do
  let mut fType ← inferType 8 f
  let mut j := 0
  for i in [:args.size] do
    match fType with
    | .forallE _ _ body _ =>
      fType := body
    | _ =>
      fType := fType.instantiateRevRange j i args
      fType := (← ensureForallCore fType e).bindingBody!
      j := i
  return fType.instantiateRevRange j args.size args

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

def inferLet (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars vals : Expr → RecM Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    let id := ⟨← mkNewId⟩
    withLCtx ((← getLCtx).mkLetDecl id name type val) do
      let fvars := fvars.push (.fvar id)
      let vals := vals.push val
      if !inferOnly then
        _ ← ensureSortCore (← inferType 9 type inferOnly) type
        let valType ← inferType 10 val inferOnly
        if !(← isDefEq 53 valType type) then
          throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type
      loop fvars vals body
  | e => do
    let r ← inferType 11 (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
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
    return (← getLCtx).mkForall fvars r

def isProp (e : Expr) : RecM Bool :=
  return (← whnf 12 (← inferType 13 e)) == .prop

def isValidProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecM Bool := do
  let type ← whnf 14 structType
  type.withApp fun I args => do
  let env ← getEnv
  let .const I_name I_levels := I | return false
  if typeName != I_name then return false
  let .inductInfo I_val ← env.get I_name | return false
  let [c] := I_val.ctors | return false
  if args.size != I_val.numParams + I_val.numIndices then return false
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels
  for i in [:I_val.numParams] do
    let .forallE _ _ b _ ← whnf 15 r | return false
    r := b.instantiate1 args[i]!
  let isPropType ← isProp type
  for i in [:idx] do
    let .forallE _ dom b _ ← whnf 16 r | return false
    if b.hasLooseBVars then
      if isPropType then if !(← isProp dom) then return false
      r := b.instantiate1 (.proj I_name i struct)
    else
      r := b
  let .forallE _ dom _ _ ← whnf 17 r | return false
  if isPropType then if !(← isProp dom) then return false
  return true

def inferProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecM Expr := do
  let e := Expr.proj typeName idx struct
  let type ← whnf 14 structType
  type.withApp fun I args => do
  let env ← getEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let [c] := I_val.ctors | fail
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels
  for i in [:I_val.numParams] do
    let .forallE _ _ b _ ← whnf 15 r | fail
    r := b.instantiate1 args[i]!
  let isPropType ← isProp type
  for i in [:idx] do
    let .forallE _ dom b _ ← whnf 16 r | fail
    if b.hasLooseBVars then
      if isPropType then if !(← isProp dom) then fail
      r := b.instantiate1 (.proj I_name i struct)
    else
      r := b
  let .forallE _ dom _ _ ← whnf 17 r | fail
  if isPropType then if !(← isProp dom) then fail
  return dom

inductive WhnfIndex where
| fn : WhnfIndex
| arg (i : Nat) : WhnfIndex
| proj (i : Nat) : WhnfIndex

def _root_.Lean.Expr.getWhnfAt' (l : List WhnfIndex) (e : Expr) : RecM Expr := do
  let e ← whnf 18 e
  match l with
  | i :: l =>
    match i with
    | .fn => getWhnfAt' l e.getAppFn
    | .arg i => getWhnfAt' l e.getAppArgs[i]!
    | .proj _ => match e with
      | .proj _ _ e' =>
        getWhnfAt' l e'
      | _ => unreachable!
  | [] => whnf 19 e

instance : OfNat WhnfIndex n where
ofNat := .arg n

def inferType' (e : Expr) (inferOnly : Bool) : RecM Expr := do
  if e.isBVar then
    throw <| .other
      s!"type checker does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert! !e.hasLooseBVars
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC)[e]? then
    -- dbg_trace s!"DBG[2]: TypeChecker.lean:267: r={r}, {e}"
    return r
  let r ← match e with
    | .lit l => pure l.type
    | .mdata _ e => inferType' e inferOnly
    | .proj s idx e => inferProj s idx e (← inferType' e inferOnly)
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      if !inferOnly then
        checkLevel (← readThe Context) l
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls inferOnly
    | .lam .. => inferLambda e inferOnly
    | .forallE .. => inferForall e inferOnly
    | .app f a =>
      if inferOnly then
        inferApp e
      else
        let fType ← ensureForallCore (← inferType' f inferOnly) e
        let dType := fType.bindingDomain!

        let aType ← try
          inferType' a inferOnly
        catch e =>
          -- dbg_trace s!"DBG4: {dType}\n"
          throw e

        -- trace s!"{(← rctx).callId}, {← callStackToStr}, {e.getAppArgs.size}, {e.getAppFn} \n\n{dType}\n\n{aType}"
        if !(← isDefEq 54 dType aType) then
          dbg_trace s!"DBG2: {f}\n"
          dbg_trace s!"DBG3: {a}"
          -- dbg_trace s!"DBG[2]: TypeChecker.lean:292 {(← aType.getWhnfAt [1, .fn])}\n"
          -- dbg_trace s!"DBG[3]: TypeChecker.lean:292 {(← dType.getWhnfAt [1, .fn, .proj 1])}\n"
          throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
        -- trace s!"{(← rctx).callId}"
        pure <| fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

def whnfCore (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCore 20 e cheapRec cheapProj

def reduceRecursor (e : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let env ← getEnv
  if env.header.quotInit then
    if let some r ← quotReduceRec e (whnf 21) then
      return r
  let whnf' e := if cheapRec then whnfCore e cheapRec cheapProj else whnf 22 e
  if let some (r, usedKLikeReduction) ← inductiveReduceRec env e whnf' (inferType 23) (isDefEq 55) (← readThe Context).opts.kLikeReduction then
    if usedKLikeReduction then
      modify fun s => {s with data := {s.data with usedKLikeReduction := true}}
    return r
  return none

def whnfFVar (e : Expr) (cheapRec cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapRec cheapProj
  return e

def reduceProj (idx : Nat) (struct : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let mut c ← (if cheapProj then whnfCore struct cheapRec cheapProj else whnf 24 struct)
  if let .lit (.strVal s) := c then
    c := .strLitToConstructor s
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

def whnfCore' (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapRec cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache[e]? then
    return r
  let rec save r := do
    if !cheapRec && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapRec cheapProj
  | .app .. =>
    e.withAppRev fun f0 rargs => do
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
      save <| ← whnfCore r cheapRec cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapRec cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapRec cheapProj then
      save <|← whnfCore m cheapRec cheapProj
    else
      save e

def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c _ := e.getAppFn then
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

def unfoldDefinitionCore (env : Environment) (e : Expr) : Option Expr := do
  if let .const _ ls := e then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        return d.instantiateValueLevelParams! ls
  none

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

def rawNatLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf 25 a) | return none
  let some v2 := rawNatLitExt? (← whnf 26 b) | return none
  return some <| .lit <| .natVal <| f v1 v2

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf 27 a) | return none
  let some v2 := rawNatLitExt? (← whnf 28 b) | return none
  return toExpr <| f v1 v2

def reduceNat (e : Expr) : RecM (Option Expr) := do
  if e.hasFVar then return none
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := rawNatLitExt? (← whnf 29 e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reduceBinNatOp Nat.pow a b
    -- if f == ``Nat.gcd then
    --   dbg_trace s!"DBG[1]: TypeChecker.lean:558 {rawNatLitExt? (← whnf 25 a)} {rawNatLitExt? (← whnf 25 b)}"
    --   return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
  return none


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
  if let some r := (← get).whnfCache[e]? then
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

def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom != sDom then
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq 56 tType sType) then return false
      pure (some sType)
    else pure none
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      let id := ⟨← mkId sType⟩
      withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
        isDefEqLambda tBody sBody (subst.push (.fvar id))
    else
      isDefEqLambda tBody sBody (subst.push default)
  | t, s => isDefEq 57 (t.instantiateRev subst) (s.instantiateRev subst)

def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom != sDom then
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq 58 tType sType) then return false
      pure (some sType)
    else pure none
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      let id := ⟨← mkId sType⟩
      withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
        isDefEqForall tBody sBody (subst.push (.fvar id))
    else
      isDefEqForall tBody sBody (subst.push default)
  | t, s => isDefEq 59 (t.instantiateRev subst) (s.instantiateRev subst)

def quickIsDefEq (t s : Expr) (useHash := false) : RecM LBool := do
  let (tCache, sCache) ← pure (t, s)
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (eqvManager := m)) =>
    let (b, m) := m.isEquiv useHash tCache sCache
    (b, .mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (eqvManager := m))
  then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq 60 a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

def isDefEqArgs (t s : Expr) : RecM Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEq 61 ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

def tryEtaExpansionCore (t s : Expr) : RecM Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf 30 (← inferType 31 s) | return false
    isDefEq 62 t (.lam name ty (.app s (.bvar 0)) bi)
  else return false

def tryEtaExpansion (t s : Expr) : RecM Bool :=
  tryEtaExpansionCore t s <||> tryEtaExpansionCore s t

def tryEtaStructCore (t s : Expr) : RecM Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless isStructureLike env fInfo.induct do return false
  unless ← isDefEq 63 (← inferType 32 t) (← inferType 33 s) do return false
  let args := s.getAppArgs
  for h : i in [fInfo.numParams:args.size] do
    let idx := (i - fInfo.numParams)
    if not (← readThe Context).opts.proofIrrelevance then
      let tType ← inferType 73 t
      if !(← isValidProj fInfo.induct idx t tType) then
        return false -- TODO would combining these conditions break the short-circuiting of the evaluation of `isValidProj`?
    unless ← isDefEq 64 (.proj fInfo.induct idx t) (args[i]'h.2) do return false
  return true

def tryEtaStruct (t s : Expr) : RecM Bool :=
  tryEtaStructCore t s <||> tryEtaStructCore s t

def isDefEqApp (t s : Expr) : RecM Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  unless tArgs.size == sArgs.size do return false
  unless ← isDefEq 65 tf sf do return false
  for ta in tArgs, sa in sArgs do
    unless ← isDefEq 66 ta sa do return false
  return true

def isDefEqProofIrrel (t s : Expr) : RecM LBool := do
  let tType ← inferType 34 t
  if !(← isProp tType) then return .undef
  let ret ← toLBoolM <| isDefEq 67 tType (← inferType 35 s)
  return ret
  -- pure .undef
  
def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
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

def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := whnfCore (unfoldDefinition env e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .bool true
    | .false => .bool false
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
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
          if ← isDefEqArgs tn sn then
            return .bool true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

def isDefEqOffset (t s : Expr) : RecM LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore 36 t' s'
  | _, _ => return .undef

def lazyDeltaReduction (tn sn : Expr) : RecM ReductionStatus := loop tn sn 1000 where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool (r == .true)
    if !tn.hasFVar && !sn.hasFVar then
      if let some tn' ← reduceNat tn then
        return .bool (← isDefEqCore 37 tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool (← isDefEqCore 38 tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      return .bool (← isDefEqCore 39 tn' sn)
    else if let some sn' ← reduceNative env sn then
      return .bool (← isDefEqCore 40 tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCore 41 (.strLitToConstructor st) s

def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf 42 (← inferType 43 t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCore 44 tType (← inferType 45 s)

def isDefEqCore' (t s : Expr) : RecM Bool := do
  let r ← quickIsDefEq t s (useHash := true)
  if r != .undef then return r == .true

  if !t.hasFVar && s.isConstOf ``true then
    if (← whnf 46 t).isConstOf ``true then return true

  let tn ← whnfCore t (cheapProj := true)
  let sn ← whnfCore s (cheapProj := true)

  if !(tn == t && sn == s) then
    let r ← quickIsDefEq tn sn
    if r != .undef then return r == .true

  if (← readThe Context).opts.proofIrrelevance then
    let r ← isDefEqProofIrrel tn sn
    if r != .undef then
      if r == .true then
        modify fun s => {s with data := {s.data with usedProofIrrelevance := true}}
      return r == .true

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .bool b => return b
  | .unknown tn sn =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj _ ti te, .proj _ si se =>
    if ti == si then if ← isDefEq 68 te se then return true
  | _, _ => pure ()

  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(tnn == tn && snn == sn) then
    return ← isDefEqCore 47 tnn snn

  if ← isDefEqApp tn sn then return true
  if ← tryEtaExpansion tn sn then return true
  if ← tryEtaStruct tn sn then return true
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return r == .true
  if ← isDefEqUnitLike tn sn then return true
  return false

end Inner
