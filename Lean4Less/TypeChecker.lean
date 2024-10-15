import Lean4Less.Quot import Lean4Less.Inductive.Reduce
import Lean4Less.EExpr

import Lean4Lean.Environment
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Util
import Lean4Lean.Instantiate
import Lean4Lean.TypeChecker

import Lean4Less.App

-- 94
-- mkId 13

namespace Lean4Less
open Lean

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException
abbrev MPE := M (PExpr × Option PExpr)
abbrev MEE := M (PExpr × Option EExpr)
abbrev MB := M (Bool × Option EExpr)
abbrev MLB := M (LBool × Option EExpr)

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

instance (priority := low) : MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (LocalDecl × EExpr)) M where
  withReader f := withReader fun s => { s with eqFVars := f s.eqFVars }

structure Methods where
  isDefEqCore : Nat → PExpr → PExpr → MB
  isDefEqCorePure : Nat → PExpr → PExpr → M Bool
  quickIsDefEq : Nat → PExpr → PExpr → Bool → MLB
  whnfCore (n : Nat) (e : PExpr) (cheapK := false) (cheapProj := false) : MEE
  whnf (n : Nat) (e : PExpr) (cheapK : Bool) : MEE
  whnfPure (n : Nat) (e : PExpr) : M PExpr
  inferType (n : Nat) (e : Expr) (dbg : Bool) : MPE
  inferTypePure (n : Nat) (e : PExpr) : M PExpr

abbrev RecM := ReaderT Methods M
abbrev RecPE := RecM (PExpr × (Option PExpr))
abbrev RecEE := RecM (PExpr × (Option EExpr))
abbrev RecB := RecM (Bool × (Option EExpr))
abbrev RecLB := RecM (LBool × (Option EExpr))

def traceM (msg : String) : M Unit := do
  if (← readThe Context).callId == (← readThe Context).dbgCallId then
    dbg_trace msg

def trace (msg : String) : RecM Unit := do
  if (← readThe Context).callId == (← readThe Context).dbgCallId then
    dbg_trace msg

def mkId (n : Nat) : RecM Name := do
  let id ← mkFreshId
  -- if id == "_kernel_fresh.879".toName then
  -- else if id == "_kernel_fresh.877".toName then
  modify fun st => { st with fvarRegistry := st.fvarRegistry.insert id n }
  pure id

def runLeanMinus (M : Lean.TypeChecker.M T) : RecM T := do
  let (ret, newState) ← Lean.TypeChecker.M.run (← getEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := false, proofIrrelevance := false}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (ngen := (← get).ngen) (state := (← get).leanMinusState) M
  modify fun s => {s with leanMinusState := newState, ngen := newState.ngen}
  pure ret

def runLeanMinusRecM (M : Lean.TypeChecker.RecM T) : RecM T := do
  let (ret, newState) ← Lean.TypeChecker.M.run (← getEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := false, proofIrrelevance := false}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (ngen := (← get).ngen) (state := (← get).leanMinusState)
    M.run
  modify fun s => {s with leanMinusState := newState, ngen := newState.ngen}
  pure ret

def runLeanRecM (M : Lean.TypeChecker.RecM T) : RecM T := do
  let (ret, _) ← Lean.TypeChecker.M.run (← getEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := true, proofIrrelevance := true}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (ngen := (← get).ngen)
    M.run
  pure ret

-- def runLean (M : Lean.TypeChecker.M T) : RecM T := do
--   Lean.TypeChecker.M.run' (← getEnv) (safety := (← readThe Context).safety) (opts := {kLikeReduction := true, proofIrrelevance := true}) (lctx := ← getLCtx) (lparams := (← readThe Context).lparams) (ngen := (← get).ngen) M

namespace Inner

/--
Reduces `e` to its weak-head normal form.
-/
def whnf (n : Nat) (e : PExpr) (cheapK := false) : RecEE := fun m => m.whnf n e (cheapK := cheapK)

def whnfPure (n : Nat) (e : PExpr) : RecM PExpr := fun m => m.whnfPure n e 

@[inline] def withPure [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with pure := true}) x

@[inline] def withCheapK [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with cheapK := true}) x

@[inline] def withCallData [MonadWithReaderOf Context m] (i : Nat) (d : CallData) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, d)}) x

@[inline] def withCallId [MonadWithReaderOf Context m] (id : Nat) (dbgCallId : Option Nat := none) (x : m α) : m α :=
  withReader (fun c => {c with callId := id, dbgCallId}) x

@[inline] def withCallIdx [MonadWithReaderOf Context m] (i : Nat) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, default)}) x

@[inline] def withForallOpt [MonadWithReaderOf Context m] (x : m α) : m α :=
  withReader (fun l => {l with forallOpt := true}) x

/--
Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not,
throws an error with `s` (the expression required be a sort).
NOTE: e must be a patched expression
-/
def ensureSortCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isSort e then return (e, none)
  let (e, p?) ← whnf 1 e
  if e.toExpr.isSort then return (e, p?)
  throw <| .typeExpected (← getEnv) default s

def assert (n : Nat) (b : Bool) : RecM Unit := do if not b then throw $ .other s!"assert fail {n}"

@[inherit_doc ensureSortCore]
def ensureSortCorePure (e : PExpr) (s : Expr) : RecM PExpr := do
  try
    let res ← runLeanMinus $ Lean.TypeChecker.ensureSort e.toExpr s
    pure res.toPExpr
  catch e =>
    throw e

/--
Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not,
throws an error with `s := f a` (the application requiring `f` to be of
function type).
-/
def ensureForallCore (e : PExpr) (s : Expr) : RecEE := do
  if Expr.isForall e then return (e, none)
  let (e, p?) ← whnf 2 e
  if e.toExpr.isForall then return (e, p?)
  throw <| .funExpected (← getEnv) (← getLCtx) s

@[inherit_doc ensureForallCore]
def ensureForallCorePure (e : PExpr) (s : Expr) : RecM PExpr := do
  try
    let res ← runLeanMinus $ Lean.TypeChecker.ensureForall e.toExpr s
    pure res.toPExpr
  catch e =>
    throw e

/--
Checks that `l` does not contain any level parameters not found in the context `tc`.
-/
def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}' {tc.lparams}"

def inferFVar (tc : Context) (name : FVarId) (idx : Option Nat) : Except KernelException PExpr := do
  if let some decl := tc.lctx.find? name then
    return decl.type.toPExpr
  throw <| .other s!"unknown free variable (index {idx}, name {name.name})"

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
def inferType (n : Nat) (e : Expr) (dbg := false) : RecPE := fun m => m.inferType n e dbg

def inferTypePure (n : Nat) (e : PExpr) : RecM PExpr := fun m => do
  let ret ← m.inferTypePure n e
  pure ret
/--
Gets the universe level of the sort that the type of `e` inhabits.
-/
def getTypeLevel (e : PExpr) : RecM (Level × PExpr) := do
  let eType ← inferTypePure 1 e
  let eTypeSort ← inferTypePure 2 eType
  let eTypeSort' ← ensureSortCorePure eTypeSort eType
  pure (eTypeSort'.toExpr.sortLevel!, eType)

def appHEqSymm (t s : PExpr) (theqs : EExpr) (info : Option (Level × PExpr × PExpr) := none) : RecM EExpr := do
  let (lvl, tType, sType) ← info.getDM do
    let (lvl, tType) ← getTypeLevel t
    let sType ← inferTypePure 3 s
    pure (lvl, tType, sType)
  pure $ theqs.reverse t s tType sType lvl

def appHEqSymm? (t s : PExpr) (theqs? : Option EExpr) : RecM (Option EExpr) := do
  let some theqs := theqs? | return none
  appHEqSymm t s theqs

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
def isDefEqCore (n : Nat) (t s : PExpr) : RecB := fun m => m.isDefEqCore n t s

def isDefEqCorePure (n : Nat) (t s : PExpr) : RecM Bool := fun m => m.isDefEqCorePure n t s

def quickIsDefEq (n : Nat) (t s : PExpr) (useHash : Bool := false) : RecLB := fun m => m.quickIsDefEq n t s useHash

@[inherit_doc isDefEqCore]
def isDefEq (n : Nat) (t s : PExpr) : RecB := do
  let r ← isDefEqCore n t s
  let (result, p?) := r
  if result then
    if let some p := p? then
      modify fun st => { st with isDefEqCache := st.isDefEqCache.insert (t, s) p }
    else
      modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  -- else if result && p?.isSome then
  pure r


def mkHRefl (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do
  pure $ .refl {u := lvl, A := T, a := t}

def isDefEqPure (n : Nat) (t s : PExpr) (fuel := 1000) : RecM Bool := do
  try
    let ret ← runLeanMinus $ Lean.TypeChecker.isDefEq t s fuel
    pure ret
  catch e =>
    match e with
    | .deepRecursion =>
      pure false -- proof irrelevance may be needed to avoid deep recursion (e.g. String.size_toUTF8)
    | _ => 
      dbg_trace s!"isDefEqPure error: {n}"
      throw e

def appPrfIrrelHEq (P Q : PExpr) (hPQ : EExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q, extra := .HEq {Q, hPQ}}

def appPrfIrrel (P : PExpr) (p q : PExpr) : RecM EExpr := do
  return .prfIrrel {P, p, q}

def appHEqTrans? (t s r : PExpr) (theqs? sheqr? : Option EExpr) : RecM (Option EExpr) := do
  match theqs?, sheqr? with
  | none, none => return none
  | .some theqs, .some sheqr =>
    let (lvl, tType) ← getTypeLevel t
    let sType ← inferTypePure 7 s
    let rType ← inferTypePure 8 r

    return .some $ .trans {u := lvl, A := tType, B := sType, C := rType, a := t, b := s, c := r, aEqb := theqs, bEqc := sheqr}
  | none, .some sheqr => return sheqr
  | .some theqs, none => return theqs


def meths : ExtMethods RecM := {
    isDefEq            := isDefEq
    isDefEqPure        := isDefEqPure
    whnf               := whnf
    mkId               := mkId
    whnfPure           := whnfPure
    mkHRefl            := mkHRefl
    getTypeLevel       := getTypeLevel
    ensureSortCorePure := ensureSortCorePure
    inferTypePure      := inferTypePure
    appPrfIrrelHEq     := appPrfIrrelHEq
    appPrfIrrel        := appPrfIrrel
    appHEqTrans?       := appHEqTrans?
    withPure           := withPure
    trace              := trace
  }

def lamCount : Expr → Nat
  | .lam _ _ b _ =>
    lamCount b + 1
  | _ => 0

def alignForAll (numBinds : Nat) (ltl ltr : Expr) : RecM (Expr × Expr × Nat) := do
  match numBinds with
  | numBinds' + 1 => do
    match (← whnfPure 11 ltl.toPExpr).toExpr, (← whnfPure 12 ltr.toPExpr).toExpr with
    | .forallE nl tdl tbl bil, .forallE nr tdr tbr bir => do
      let idl := ⟨← mkId 6⟩
      let idr := ⟨← mkId 7⟩
      withLCtx ((← getLCtx).mkLocalDecl idl nl tdl bil) do
        withLCtx ((← getLCtx).mkLocalDecl idr nr tdr bir) do
          let ntbl := tbl.instantiate1 (.fvar idl)
          let ntbr := tbr.instantiate1 (.fvar idr)
          let (atbl, atbr, n) ← alignForAll numBinds' ntbl ntbr
          let nltl := (← getLCtx).mkForall #[(.fvar idl)] atbl
          let nltr := (← getLCtx).mkForall #[(.fvar idr)] atbr
          pure (nltl, nltr, n + 1)
    | _, _ => pure (ltl, ltr, 0)
  | _ => pure (ltl, ltr, 0)

inductive WhnfIndex where
| fn : WhnfIndex
| arg (i : Nat) : WhnfIndex
| proj (i : Nat) : WhnfIndex

def _root_.Lean4Less.PExpr.getWhnfAt (l : List WhnfIndex) (e : PExpr) : RecM PExpr := do
  let e ← whnfPure 0 e
  match l with
  | i :: l =>
    match i with
    | .fn => getWhnfAt l e.toExpr.getAppFn.toPExpr
    | .arg i => getWhnfAt l e.toExpr.getAppArgs[i]!.toPExpr
    | .proj _ => match e.toExpr with
      | .proj _ _ e' =>
        getWhnfAt l e'.toPExpr
      | _ => unreachable!
  | [] => whnfPure 0 e

instance : OfNat WhnfIndex n where
ofNat := .arg n

def smartCast' (tl tr e : PExpr) (n : Nat) (p? : Option EExpr := none) : RecM ((Bool × Option EExpr) × PExpr) := do
  let getLvl tl tr := do
    let sort ← inferTypePure 13 tr
    let sort' ← ensureSortCorePure sort tl
    pure sort'.toExpr.sortLevel!

  let mkCast'' nm tl tr p e (prfVars prfVals : Array Expr) (lvl : Level) := do
    let app := Lean.mkAppN (← getConst nm [lvl]) #[tl, tr, p.toExpr, e]
    pure $ app.replaceFVars prfVars prfVals

  let mkCast' nm tl tr p e (prfVars prfVals : Array Expr) := do
    let lvl ← getLvl tl.toPExpr tr.toPExpr
    mkCast'' nm tl tr p e prfVars prfVals lvl

  let rec loop e tl tr (lamVars prfVars prfVals : Array Expr) p : RecM Expr := do
    pure ()
    match e, tl, tr, p with
    | .lam n _ b bi, .forallE _ _ tbl .., .forallE _ tdr tbr .., .forallE forallData =>
      let {A, a, UaEqVx, extra, u, ..} := forallData
      let id := ⟨← mkId 5⟩
      withLCtx ((← getLCtx).mkLocalDecl id n tdr bi) do
        let v := .fvar id

        let (newPrfVars, newPrfVals, vCast) ←
          match extra with
          | .AB {B, b, vaEqb, hAB} =>
            let hBA ← appHEqSymm A B hAB (info := .some (u, (Expr.sort (.succ u)).toPExpr, (Expr.sort (.succ u)).toPExpr))
            let vCast ← mkCast'' `L4L.castHEq B.toExpr A.toExpr hBA v prfVars prfVals u
            let vCastEqv ← mkCast'' `L4L.castOrigHEq B.toExpr A.toExpr hBA v prfVars prfVals u
            pure (#[a.toExpr, b.toExpr, vaEqb.aEqb.toExpr], #[vCast, v, vCastEqv], vCast)
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
      let cast ← mkCast' `L4L.castHEq tl tr p e prfVars prfVals
      pure $ (← getLCtx).mkLambda lamVars cast

  let tlEqtr? ← do
    pure ()
    if let some p := p? then
      pure $ (true, .some p)
    else
      let nLams := lamCount e
      let (tl', tr', nLams) ← try 
        alignForAll nLams tl tr
      catch ex =>
        dbg_trace s!"smartCast error: {n}, {nLams}"
        throw ex
      let tl' := tl'.toPExpr
      let tr' := tr'.toPExpr
      if nLams > 0 then
        isDefEqForall tl' tr' nLams
      else
        isDefEq (1000 + n) tl tr

  if let (true, some tlEqtr) := tlEqtr? then -- sanity check (TODO delete)
    let pT ← inferTypePure 0 tlEqtr
    let lvl ← getLvl tl tr
    let heq := (Lean.mkAppN (← getConst `HEq [.succ lvl]) #[(Expr.sort lvl).toPExpr, tl, (Expr.sort lvl).toPExpr, tr]).toPExpr
    if not (← isDefEqPure 0 pT heq) then
      dbg_trace s!"DBG[2]: TypeChecker.lean:292 {p?.isSome} {(← pT.getWhnfAt [1, .fn])}"
      dbg_trace s!"DBG[3]: TypeChecker.lean:292 {(← heq.getWhnfAt [1, .fn])}\n"
      dbg_trace s!"DBG[1]: TypeChecker.lean:657 {(← get).numCalls}"
      let (true, some tlEqtr) ← isDefEq (1000 + n) tl tr | unreachable!
      throw $ .other s!"cast equality does not have expected type"
  pure $ (tlEqtr?, (← tlEqtr?.2.mapM (fun (p : EExpr) => do pure (← loop e.toExpr tl.toExpr tr.toExpr #[] #[] #[] p).toPExpr)).getD e)

def smartCast (n : Nat) (tl tr e : PExpr) (p? : Option EExpr := none) : RecM (Bool × PExpr) := do
  let ret ← try
    smartCast' tl tr e n p?
  catch ex =>
    dbg_trace s!"smartCast error: {n}"
    throw ex
  pure (ret.1.1, ret.2)

def maybeCast (n : Nat) (p? : Option EExpr) (typLhs typRhs e : PExpr) : RecM PExpr := do
  pure $ (← p?.mapM (fun (p : EExpr) => do pure (← smartCast n typLhs typRhs e p).2)).getD e

def methsA (meths : ExtMethods m) : ExtMethodsA m := {
    meths with
    opt := true
    isDefEqForall := isDefEqForall' meths (explicit := true)
    -- alignForAll := alignForAll 
  }

/--
Infers the type of lambda expression `e`.
-/
def inferLambda (e : Expr) (dbg := false) : RecPE := loop #[] false e where
  loop fvars domPatched : Expr → RecPE -- TODO OK that fvars is not `Array PExpr`?
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let (sort, d'?) ← inferType 14 d
    let (sort', p?) ← ensureSortCore sort d
    let d' ← maybeCast 20 p? sort sort' (d'?.getD d.toPExpr)

    let id := ⟨← mkId 8⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let e := e.instantiateRev fvars
    let (r, e'?) ← inferType 15 e dbg
    let e' := e'?.getD e.toPExpr
    let r := r.toExpr.cheapBetaReduce |>.toPExpr
    let (rSort) ← inferTypePure 16 r
    let (rSort', p?) ← ensureSortCore rSort r -- TODO need to test this
    let r' ← maybeCast 21 p? rSort rSort' r

    let patch ←
      if domPatched || e'?.isSome then do
        pure $ some $ ((← getLCtx).mkLambda fvars e').toPExpr
      else 
        pure none

    -- TODO only return .some if any of the fvars had domains that were patched, or if e'? := some e'
    return (( (← getLCtx).mkForall fvars r').toPExpr, patch)

/--
Infers the type of for-all expression `e`.
-/
def inferForall (e : Expr) : RecPE := loop #[] #[] false e where
  loop fvars us domPatched : Expr → RecPE
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let (sort, d'?) ← inferType 17 d
    let (sort', p?) ← ensureSortCore sort d
    let lvl := sort'.toExpr.sortLevel!
    let d' ← maybeCast 22 p? sort sort' (d'?.getD d.toPExpr)

    let us := us.push lvl
    let id := ⟨← mkId 9⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d' bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us (domPatched || d'?.isSome || p?.isSome) body
  | e => do
    let e := e.instantiateRev fvars
    let (sort, e'?) ← inferType 18 e
    let (sort', p?) ← ensureSortCore sort e
    let lvl := sort'.toExpr.sortLevel!
    let e' ← maybeCast 23 p? sort sort' (e'?.getD e.toPExpr)

    let patch? ←
      if domPatched || e'?.isSome || p?.isSome then do
        pure $ .some $ ((← getLCtx).mkForall fvars e').toPExpr
      else
        pure none
    return ((Expr.sort <| us.foldr mkLevelIMax' lvl ).toPExpr, patch?)

/--
Infers the type of application `e`, assuming that `e` is already well-typed.
-/
def inferApp (e : PExpr) : RecM PExpr := do
  e.toExpr.withApp fun f args => do
  let f := f.toPExpr
  let args := args.map (·.toPExpr)
  let mut fType ← inferTypePure 19 f
  let mut j := 0
  for i in [:args.size] do
    match fType.toExpr with
    | .forallE _ _ body _ =>
      fType := body.toPExpr
    | _ =>
      fType := fType.toExpr.instantiateRevRange j i args |>.toPExpr
      let fType' ← ensureForallCorePure fType e
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
    let (sort, type'?) ← inferType 20 type 
    let (sort', pType?) ← ensureSortCore sort type
    let type' ← maybeCast 16 pType? sort sort' (type'?.getD type.toPExpr)
    let val := val.instantiateRev fvars
    let (valType, val'?) ← inferType 21 val 
    let val' := val'?.getD val.toPExpr
    let ((true, pVal?), valC') ← smartCast' valType type' val' 17 |
      throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type'
    let id := ⟨← mkId 10⟩
    withLCtx ((← getLCtx).mkLetDecl id name type' valC') do
      let fvars := fvars.push (.fvar id)
      let vals := vals.push valC'
      loop fvars vals (typePatched || type'?.isSome || pType?.isSome || val'?.isSome || pVal?.isSome) body
  | e => do
    let (r, e'?) ← inferType 22 (e.instantiateRev fvars)
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

/--
Checks if the type of `e` is definitionally equal to `Prop`.
-/
def isPropPure (e : PExpr) : RecM Bool := do
  let t ← inferTypePure 23 e
  let t' ← whnfPure 24 t
  return t' == Expr.prop.toPExpr

/--
Infers the type of structure projection `e`.

FIXME: This does a lot of checking on the struct constructor type itself,
shouldn't that belong in Inductive/Add.lean instead?
-/
def inferProj (typeName : Name) (idx : Nat) (struct : PExpr) (patched : Bool) (structType : PExpr) : RecPE := do
  let e := Expr.proj typeName idx struct
  let (type, pType?) ← whnf 25 structType
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
    let .mk (.forallE _ _ b _) ← whnfPure 26 r | fail -- FIXME use ensureForall?
    r := b.instantiate1 args[i]! |>.toPExpr
  let isPropType := ← isPropPure type
  for i in [:idx] do
    let .mk (.forallE _ dom b _) ← whnfPure 27 r | fail -- FIXME use ensureForall?
    if b.hasLooseBVars then
      -- prop structs cannot have non-prop dependent fields
      let isPropDom ← isPropPure dom.toPExpr
      if isPropType then if !isPropDom then fail
      r := b.instantiate1 (.proj I_name i struct) |>.toPExpr
    else
      r := b.toPExpr
  let (.mk (.forallE _ dom _ _)) ← whnfPure 28 r | fail -- FIXME use ensureForall?
  let isPropDom ← isPropPure dom.toPExpr
  if isPropType then if !isPropDom then fail
  let patched := patched || pType?.isSome
  let patch := if patched then some (Expr.proj typeName idx struct).toPExpr else none
  return (dom.toPExpr, patch)

@[inherit_doc inferType]
def inferType' (e : Expr) (_dbg := false) : RecPE := do
  -- if (← readThe Context).const == `eq_of_heq' then
  --   dbg_trace s!"started e={e}"
  if e.isBVar then
    throw <| .other
      s!"patcher does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert 5 $ !e.hasLooseBVars
  let state ← get
  if let some r := state.inferTypeC[e]? then
    return r
  let (r, ep?) ← match e with
    | .lit l => pure (l.type.toPExpr, none)
    | .mdata _ e => inferType' e
    | .proj s idx e =>
      let (t, e'?) ← inferType' e
      let e' := e'?.getD e.toPExpr
      inferProj s idx e' e'?.isSome t
    | .fvar n => pure (← inferFVar (← readThe Context) n ((← get).fvarRegistry.get? n.name), none)
    | .mvar _ => throw <| .other "patcher does not support meta variables"
    | .bvar _ => throw $ .other "unreachable 1"
    | .sort l =>
      checkLevel (← readThe Context) l
      pure <| (Expr.sort (.succ l) |>.toPExpr, none)
    | .const c ls => pure (← inferConstant (← readThe Context) c ls, none)
    | .lam .. => inferLambda e false
    | .forallE .. => inferForall e
    | .app f a =>
      let (fType, f'?) ← inferType' f
      let (fType', pf'?) ← ensureForallCore fType f
      let f' ← maybeCast 18 pf'? fType fType' (f'?.getD f.toPExpr)
      -- if (← readThe Context).const == `eq_of_heq' then if let .lam _ (.const `Ty _) _ _ := a then

      let (aType, a'?) ← inferType' a

      let dType := Expr.bindingDomain! fType' |>.toPExpr
      -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
      -- for some universe level `l`, so this use of `isDefEq` is valid
      let ((true, pa'?), a') ← smartCast' aType dType (a'?.getD a.toPExpr) 19 |
        -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
        dbg_trace s!"dbg: {e}"
        throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType' aType

      let patch := if f'?.isSome || a'?.isSome || pf'?.isSome || pa'?.isSome then .some (Expr.app f' a').toPExpr else none
      pure ((Expr.bindingBody! fType').instantiate1 a' |>.toPExpr, patch)
    | .letE .. => inferLet e
  modify fun s => { s with inferTypeC := s.inferTypeC.insert e (r, ep?) }
  return (r, ep?)

def inferTypePure' (e : PExpr) : RecM PExpr := do -- TODO make more efficient
  let eT ← runLeanMinus $ Lean.TypeChecker.inferTypeCheck e.toExpr
  pure eT.toPExpr

/--
Reduces `e` to its weak-head normal form, without unfolding definitions. This
is a conservative version of `whnf` (which does unfold definitions), to be used
for efficiency purposes.

Setting `cheapK` or `cheapProj` to `true` will cause the major premise/struct
argument to be reduced "lazily" (using `whnfCore` rather than `whnf`) when
reducing recursor applications/struct projections. This can be a useful
optimization if we're checking the definitional equality of two recursor
applications/struct projections of the same recursor/projection, where we
might save some work by directly checking if the major premises/struct
arguments are defeq (rather than eagerly applying a recursor rule/projection).
-/
def whnfCore (n : Nat) (e : PExpr) (cheapK := false) (cheapProj := false) : RecEE :=
  fun m => m.whnfCore n e cheapK cheapProj

/--
Gets the weak-head normal form of the free variable `e`,
which is the weak-head normal form of its definition if `e` is a let variable and itself if it is a lambda variable.
-/
def whnfFVar (e : PExpr) (cheapK : Bool) (cheapProj : Bool) : RecEE := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.toExpr.fvarId! then
    return ← whnfCore 29 v.toPExpr cheapK cheapProj
  return (e, none)

def appProjThm? (structName : Name) (projIdx : Nat) (struct structN : PExpr) (structEqstructN? : Option EExpr) : RecM (Option EExpr) := do
  structEqstructN?.mapM fun _ => do
    let env ← getEnv
    let structNType ← whnfPure 30 (← inferTypePure 31 structN)
    let structType ← whnfPure 32 (← inferTypePure 33 struct)
    let structTypeC := if structType.toExpr.isApp then structType.toExpr.withApp fun f _ => f else structType.toExpr
    let .const typeC lvls := structTypeC | unreachable!
    let .inductInfo {numParams, numIndices, type, levelParams, ..} ← env.get typeC | unreachable!
    let type := type.instantiateLevelParams levelParams lvls
    assert! numIndices == 0
    let paramsN := structNType.toExpr.getAppArgs
    let params := structType.toExpr.getAppArgs

    let rec loop remType (paramVars : Array Expr) n := do
      match (← whnfPure 34 remType.toPExpr).toExpr, n with
      | .forallE n d b i, m + 1 =>
        let idr := ⟨← mkId 11⟩
        withLCtx ((← getLCtx).mkLocalDecl idr n d i) do
          let rVar := (.fvar idr)
          let remCtorType := b.instantiate1 rVar
          let paramVars := paramVars.push rVar
          loop remCtorType paramVars m
      | _, 0 =>
        let structType := Lean.mkAppN structTypeC paramVars
        let ids := ⟨← mkId 12⟩
        withLCtx ((← getLCtx).mkLocalDecl ids default structType default) do
          let s := Expr.fvar ids

          let f := (← getLCtx).mkLambda (paramVars ++ #[s]) (.proj structName projIdx s) |>.toPExpr
          let mut targsEqsargs? := default
          targsEqsargs? := targsEqsargs?.insert numParams structEqstructN?
          let (true, ret?) ← isDefEqApp methsA (Lean.mkAppN f (params ++ #[struct.toExpr])).toPExpr (Lean.mkAppN f (paramsN ++ #[structN.toExpr])).toPExpr targsEqsargs? (some none) | unreachable!

          pure $ ret?.get!
      | _, _ => unreachable!

    loop type #[] numParams

/--
Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a
constructor application).
-/
def reduceProj (structName : Name) (projIdx : Nat) (struct : PExpr) (cheapK : Bool) (cheapProj : Bool) : RecM (Option (PExpr × Option EExpr)) := do
  let mut (structN, structEqc?) ← (if cheapProj then whnfCore 35 struct cheapK cheapProj else whnf 305 struct (cheapK := cheapK))

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

-- def mkRefl (lvl : Level) (T : PExpr) (t : PExpr) : RecM EExpr := do
--   pure $ Lean.mkAppN (← getConst `Eq.refl [lvl]) #[T, t] |>.toEExprD


@[inherit_doc whnfCore]
private def _whnfCore' (e' : Expr) (cheapK := false) (cheapProj := false) : RecEE := do
  -- TODO whnfPure optimization
  let e := e'.toPExpr
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return (e, none)
  | .mdata _ e => return ← _whnfCore' e cheapK cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return (e, none)
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache.get? e then -- FIXME important to optimize this -- FIXME should this depend on cheapK?
    return r
  let rec save r := do
    if !cheapK && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
      if cheapK && r.2.isNone then
        modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => throw $ .other "unreachable 9"
  | .fvar _ => return ← whnfFVar e cheapK cheapProj
  | .app .. => -- beta-reduce at the head as much as possible, apply any remaining `rargs` to the resulting expression, and re-run `whnfCore`
    e'.withAppRev fun f0 rargs => do
    let f0 := f0.toPExpr
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let (f, pf0Eqf?) ← whnfCore 52 f0 cheapK cheapProj
    let frargs := f.toExpr.mkAppRevRange 0 rargs.size rargs |>.toPExpr

    let (frargs', rargs', eEqfrargs'?) ←
      if pf0Eqf?.isSome then -- FIXME the type may have changed, even if this is none
        let f0T ← inferTypePure 91 f0
        let fT ← inferTypePure 92 f
        if ! (← isDefEqPure 93 f0T fT) then
          -- patch to cast rargs as necessary to agree with type of f
          let (_, frargs'?) ← inferType 53 frargs -- FIXME can result in redundant casts?
          let frargs' := frargs'?.getD frargs
          let rargs' := frargs'.toExpr.getAppArgs[f.toExpr.getAppArgs.size:].toArray.reverse
          assert 10 $ rargs'.size == rargs.size
          let (.true, data?) ← isDefEqApp'' methsA f0 f (rargs.map (·.toPExpr)).reverse (rargs'.map (·.toPExpr)).reverse (tfEqsf? := pf0Eqf?) |
            throw $ .other "unreachable 10"
          let eEqfrargs'? := data?.map (·.1)
          pure (frargs', rargs', eEqfrargs'?)
        else
          pure (frargs, rargs, none)
      else
        pure (frargs, rargs, none)


    if let (.lam _ _ body _) := f.toExpr then
      -- if e'.isApp then if let .const `Bool.casesOn _ := e'.withApp fun f _ => f then
      let rec loop m (f : Expr) : RecEE :=
        let cont := do
          let r := f.instantiateRange (rargs'.size - m) rargs'.size rargs'
          let r := r.mkAppRevRange 0 (rargs'.size - m) rargs' |>.toPExpr
          let (r', rEqr'?) ← whnfCore 54 r cheapK cheapProj
          let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? rEqr'?
          save (r', eEqr'?)
        if let .lam _ _ body _ := f then
          if m < rargs'.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if f == f0 then
      if let some (r, eEqr?) ← reduceRecursor e cheapK then
        let (r', rEqr'?) ← whnfCore 55 r cheapK cheapProj
        let eEqr'? ← appHEqTrans? e r r' eEqr? rEqr'?
        pure (r', eEqr'?)
      else
        pure (e, none)
    else
      -- FIXME replace with reduceRecursor? adding arguments can only result in further normalization if the head reduced to a partial recursor application
      let (r', frargsEqr'?) ← whnfCore 56 frargs' cheapK cheapProj
      let eEqr'? ← appHEqTrans? e frargs' r' eEqfrargs'? frargsEqr'?
      save (r', eEqr'?)
  | .letE _ _ val body _ =>
    save <|← whnfCore 57 (body.instantiate1 val).toPExpr cheapK cheapProj
  | .proj typeName idx s =>
    if let some (m, eEqm?) ← reduceProj typeName idx s.toPExpr cheapK cheapProj then
      let (r', mEqr'?) ← whnfCore 58 m cheapK cheapProj
      let eEqr'? ← appHEqTrans? e m r' eEqm? mEqr'?
      save (r', eEqr'?)
    else
      save (e, none)

@[inherit_doc whnfCore]
def whnfCore' (e : PExpr) (cheapK := false) (cheapProj := false) : RecEE :=
  _whnfCore' e cheapK cheapProj

@[inherit_doc whnf]
private def _whnf' (e' : Expr) (cheapK := false) : RecEE := do
  let e := e'.toPExpr
  -- Do not cache easy cases
  match e' with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return (e, none)
  | .mdata _ e => return ← _whnf' e (cheapK := cheapK)
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return (e, none)
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  -- if let some r := (← get).whnfCache.get? (e, cheapK) then
  --   return r
  let rec loop le eEqle?
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let (ler, leEqler?) ← whnfCore' le (cheapK := cheapK)
    let eEqler? ← appHEqTrans? e le ler eEqle? leEqler?
    if let some (ler', lerEqler'?) ← reduceNative env ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    if let some (ler', lerEqler'?) ← reduceNat ler then return (ler', ← appHEqTrans? e ler ler' eEqler? lerEqler'?)
    let some leru := unfoldDefinition env ler | return (ler, eEqler?)
    loop leru eEqler? fuel
  let r ← loop e none 1000
  modify fun s => { s with whnfCache := s.whnfCache.insert (e, cheapK) r }
  return r

@[inherit_doc whnf]
def whnf' (e : PExpr) (cheapK := false) : RecEE := _whnf' e (cheapK := cheapK)

def whnfPure' (e : PExpr) : RecM PExpr := do
  let leanMinusWhnf ← runLeanMinus $ Lean.TypeChecker.whnf e.toExpr
  pure leanMinusWhnf.toPExpr

end Inner
