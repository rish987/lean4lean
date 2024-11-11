import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext

namespace Lean4Less
open Lean
open Lean4Less.TypeChecker

section

variable [Monad m] [MonadExcept KernelException M] (env : Environment)
  (meth : ExtMethodsR m)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : PExpr) (nparams : Nat) : Option (PExpr × Name) :=
  type.toExpr.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return (mkAppRange (.const name ls) 0 nparams args |>.toPExpr, name)

/--
When `e` has the type of a K-like inductive, converts it into a constructor
application.

For instance if we have `e : Eq a a`, it is converted into `Eq.refl a` (which
it is definitionally equal to by proof irrelevance). Note that the indices of
`e`'s type must match those of the constructor application (for instance,
`e : Eq a b` cannot be converted if `a` and `b` are not defeq).
-/
def toCtorWhenK (rval : RecursorVal) (e : PExpr) : m (PExpr × Option (EExpr)) := do
  assert! rval.k
  let type ← meth.whnfPure 101 (← meth.inferTypePure 102 e)
  let .const typeI _ := type.toExpr.getAppFn | return (e, none)
  if typeI != rval.getMajorInduct then return (e, none)
  if type.toExpr.hasExprMVar then
    let typeArgs := type.toExpr.getAppArgs
    for h : i in [rval.numParams:typeArgs.size] do
      if (typeArgs[i]'h.2).hasExprMVar then return (e, none)
  let some (newCtorApp, newCtorName) := mkNullaryCtor env type rval.numParams | return (e, none)
  if let (.const ctorName _) := e.toExpr.getAppFn then
    if ctorName == newCtorName then
      if let true ← meth.isDefEqPure 103 e newCtorApp then
        return (e, none)
  let appType ← meth.inferTypePure 104 newCtorApp
  -- check that the indices of types of `e` and `newCtorApp` match
  let (true, pt?) ← meth.isDefEq 105 type appType | return (e, none)
  let prf? ← meth.isDefEqProofIrrel' e newCtorApp type appType pt?

  return (newCtorApp, prf?)

def expandEtaStruct (eType e : PExpr) : (PExpr × Option EExpr) :=
  eType.toExpr.withApp fun I args => Id.run do
  let .const I ls := I | return (e, none)
  let some ctor := getFirstCtor env I | return (e, none)
  let some (.ctorInfo info) := env.find? ctor | unreachable!
  let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
  for i in [:info.numFields] do
    result := .app result (.proj I i e)
  pure (result.toPExpr, none)

/--
When `e` is of struct type, converts it into a constructor application using
projections.

For instance if we have `e : String`, it is converted into
`String.mk (String.data e)` (which is definitionally equal to `e` by struct
eta).
-/
def toCtorWhenStruct (inductName : Name) (e : PExpr) : m (PExpr × Option EExpr) := do
  if !isStructureLike env inductName || (e.toExpr.isConstructorApp?' env).isSome then
    return (e, none)
  let eType ← meth.whnfPure 107 (← meth.inferTypePure 106 e)
  if !eType.toExpr.getAppFn.isConstOf inductName then return (e, none)
  if (← meth.whnf 108 (← meth.inferTypePure 109 eType)).1 == Expr.prop.toPExpr then return (e, none)
  return expandEtaStruct env eType e

def getRecRuleFor (rval : RecursorVal) (major : Expr) : Option RecursorRule := do
  let .const fn _ := major.getAppFn | none
  rval.rules.find? (·.ctor == fn)

/--
Performs recursor reduction on `e` (returning `none` if not applicable).

For recursor reduction to occur, `e` must be a recursor application where the
major premise is either a complete constructor application or of a K- or
structure-like inductive type (in which case it is converted into an equivalent
constructor application). The reduction is done by applying the
`RecursorRule.rhs` associated with the constructor to the parameters from the
recursor application and the fields of the constructor application.
-/
def inductiveReduceRec [Monad m] [MonadWithReaderOf LocalContext m] [MonadLCtx m] [MonadExcept KernelException m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) m] (env : Environment) (e : PExpr) (cheapK : Bool := false)
    : m (Option (PExpr × Option EExpr)) := do
  let recFn := e.toExpr.getAppFn
  let .const recFnName ls := recFn | return none
  let some (.recInfo info) := env.find? recFnName | return none
  let recType := info.type.instantiateLevelParams info.levelParams ls
  let recArgs := e.toExpr.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let major := major'.toPExpr
  let (majorWhnf, majorEqmajorWhnf?) ← meth.whnf 110 major
  let (majorKWhnf, majorWhnfEqmajorKWhnf?) ← if info.k && not cheapK then toCtorWhenK env meth info majorWhnf else pure (majorWhnf, none)
  let majorEqmajorKWhnf? ← meth.appHEqTrans? major majorWhnf majorKWhnf majorEqmajorWhnf? majorWhnfEqmajorKWhnf?
  let (majorMaybeCtor, majorKWhnfEqMajorMaybeCtor?) ← match majorKWhnf.toExpr with
    | .lit l => pure (l.toConstructor.toPExpr, none)
    | _ => toCtorWhenStruct env meth info.getMajorInduct majorKWhnf
  let majorEqMajorMaybeCtor? ← meth.appHEqTrans? major majorKWhnf majorMaybeCtor majorEqmajorKWhnf? majorKWhnfEqMajorMaybeCtor?
  -- (majorIdx, majorEqMajorMaybeCtor?)
  let some rule := getRecRuleFor info majorMaybeCtor | return none
  let majorArgs := majorMaybeCtor.toExpr.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  let getNestedType (t' : PExpr) := do
    let t? := t'.toExpr.find? fun
        | e@(.app ..) => 
          let fn := e.getAppFn
          if let .const n .. := fn then
             info.all.any (· == n)
          else
            false
        | .const n .. => info.all.any (· == n)
        | _ => false
    pure t?.get!

  let type ← getNestedType $ ← meth.whnfPure 111 $ ← meth.inferTypePure 112 major
  let newType ← getNestedType $ ← meth.whnfPure 112 (← meth.inferTypePure 113 majorMaybeCtor)
  let typeArgs := type.getAppArgs
  let newTypeArgs := newType.getAppArgs
  let mut argEqs? : Array (Option EExpr) := #[]
  for (arg, newArg) in typeArgs.zip newTypeArgs do
    let (arg, newArg) := (arg.toPExpr, newArg.toPExpr)
    let (true, p?) ← meth.isDefEq 136 arg newArg | panic! ""
    argEqs? := argEqs?.push p?

  let (paramEqs?, indEqs?) ←
      pure (argEqs?[:info.numParams].toArray, argEqs?[info.numParams:].toArray)

  let (params, _indices) ←
      pure (typeArgs[:info.numParams].toArray, typeArgs[info.numParams:].toArray)
  let (newParams, newIndices) ←
      pure (newTypeArgs[:info.numParams].toArray, newTypeArgs[info.numParams:].toArray)

  let numMotivesMinors := info.numMotives + info.numMinors
  let motivesMinors? ← do
    if paramEqs?.any (·.isSome) then
      pure $ some (← replaceParams meth recType params newParams recArgs[info.numParams:info.numParams + numMotivesMinors])
    else
      pure none

  let mut newRecArgs := recArgs.set! majorIdx majorMaybeCtor
  let mut map := .insert default majorIdx majorEqMajorMaybeCtor?

  for idx in [:paramEqs?.size] do
    let paramEq? := paramEqs?[idx]!
    map := map.insert idx paramEq?
    newRecArgs := newRecArgs.set! idx newParams[idx]!

  let motivesStartIdx := info.numParams
  if let some motivesMinors := motivesMinors? then
    for idx in [:numMotivesMinors] do
      let (newMotiveMinor, p?) := motivesMinors[idx]!
      let recIdx := motivesStartIdx + idx
      map := map.insert recIdx p?
      newRecArgs := newRecArgs.set! recIdx newMotiveMinor
  else
    for idx in [:numMotivesMinors] do
      let recIdx := motivesStartIdx + idx
      map := map.insert recIdx .none

  let indicesStartIdx := info.numParams + numMotivesMinors
  for idx in [:indEqs?.size] do
    let indEq? := indEqs?[idx]!
    let recIdx := indicesStartIdx + idx
    map := map.insert recIdx indEq?
    newRecArgs := newRecArgs.set! recIdx newIndices[idx]!

  let e' := (mkAppN recFn recArgs[:majorIdx + 1]) |>.toPExpr
  let eNewMajor' := mkAppN recFn newRecArgs[:majorIdx + 1] |>.toPExpr
  -- try
  --   _ ← meth.inferTypePure 10001 eNewMajor'
  -- let (_, eNewMajor?) := (← meth.inferType 121 eNewMajor') -- cast remaining args as necessary
  -- let eNewMajor := eNewMajor?.getD eNewMajor'
  let (.true, eEqeNewMajor'?) ← meth.isDefEqApp 2 e' eNewMajor' map | unreachable!

  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx newRecArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs

  if let some eEqeNewMajor' := eEqeNewMajor'? then
    dbg_trace s!"DBG[1]: Reduce.lean:196 (after if let some eEqeNewMajor := eEqeNewMajor…)"
    let eType' ← meth.inferTypePure 129 e'
    dbg_trace s!"DBG[3]: Reduce.lean:198 (after let eType := (← meth.inferTypeLean 129…)"
    let eNewMajorType' ← meth.inferTypePure 121 eNewMajor'
    dbg_trace s!"DBG[2]: Reduce.lean:198 (after let eNewMajorType := (← meth.inferType…)"
    let sort ← meth.whnfPure 135 (← meth.inferTypePure 134 eType')
    let .sort lvl := sort.toExpr | unreachable!
    let idrV := .mk (← meth.mkId 130 eType')
    withLCtx ((← getLCtx).mkLocalDecl idrV default eType' default) do
      let some rVl := (← getLCtx).find? idrV | unreachable!
      let rV := rVl.toExpr
      let idfV := .mk (← meth.mkId 131 eNewMajorType')
      withLCtx ((← getLCtx).mkLocalDecl idfV default eNewMajorType' default) do
        let some fVl := (← getLCtx).find? idfV | unreachable!
        let fV := fVl.toExpr

        let rVEqfVType := mkAppN (.const `HEq [lvl]) #[eType', eNewMajorType', rV, fV]
        let fVEqrVType := mkAppN (.const `HEq [lvl]) #[eNewMajorType', eType', fV, rV]
        let idrVEqfV := ⟨← meth.mkId 132 rVEqfVType⟩
        withLCtx ((← getLCtx).mkLocalDecl idrVEqfV default rVEqfVType default) do
          let idfVEqrV := ⟨← meth.mkId 133 fVEqrVType⟩
          withLCtx ((← getLCtx).mkLocalDecl idfVEqrV default fVEqrVType default) do
            let some rVEqfV := (← getLCtx).find? idrVEqfV | unreachable!
            let some fVEqrV := (← getLCtx).find? idfVEqrV | unreachable!
            withEqFVar idrV idfV { aEqb := rVEqfV, bEqa := fVEqrV, a := rV.toPExpr, b := fV.toPExpr, A := eType', B := eNewMajorType', u := lvl } do
              let some rVEqfVl := (← getLCtx).find? idrVEqfV | unreachable!
              let rVEqfV := rVEqfVl.toExpr -- TODO create fvar with type HEq fV rV

              let mut fType := eNewMajorType'

              let mut r := rV
              let mut f := fV

              if majorIdx + 1 < recArgs.size then
                for idx in [majorIdx + 1:recArgs.size] do
                  let (domType, nfType', fType', fTypeEqfType'?) ← match (← meth.whnfPure 122 fType).toExpr with
                    | .forallE _ d  b _=> pure (d, b, fType, none)
                    | T =>
                      -- let ret ← meth.whnf 126 T.toPExpr 
                      -- match ret with
                      -- | (.mk (.forallE _ d  b _), fTypeEqfType'?) =>
                      --   pure (d, b, ret.1, fTypeEqfType'?)
                      -- | _ =>
                        -- let test ← meth.whnf 0 fType
                        throw $ .other s!"unreachable (Reduce.lean)\n{T}\n\n{eNewMajor'}\n\n{e'}"
                  let arg := recArgs[idx]!.toPExpr
                  let argType ← meth.inferTypePure 123 arg
                  let (true, argTypeEqDomType?) ← meth.isDefEq 127 argType domType.toPExpr | unreachable!

                  let f' ← meth.maybeCast 125 fTypeEqfType'? fType fType' f.toPExpr
                  let arg' ← meth.maybeCast 124 argTypeEqDomType? argType domType.toPExpr arg

                  fType := (nfType'.instantiate1 arg').toPExpr
                  
                  r := r.app arg
                  f := f'.app arg'

              -- _ ← meth.inferTypePure 5000 r.toPExpr -- sanity check TODO remove
              -- _ ← meth.inferTypePure 6000 f.toPExpr -- sanity check TODO remove

              let (.true, rEqf?) ← meth.isDefEq 128 r.toPExpr f.toPExpr | unreachable!

              let newe := f.replaceFVar fV rhs -- TODO substitute in f: fV for rhs

              let eEqeNewMajor? ← rEqf?.mapM (fun rEqf => do
                let rEqf := rEqf.replaceFVars #[rV.toPExpr, fV.toPExpr] #[e', eNewMajor']
                let rEqf := rEqf.replaceFVarE rVEqfV.toPExpr (.mk eEqeNewMajor') |>.run
                -- assert! not (rEqf.toExpr.containsFVar' idrV)
                -- assert! not (rEqf.toExpr.containsFVar' idfV)
                -- _ ← meth.inferTypePure 8000 rEqf.toExpr.toPExpr -- sanity check TODO remove
                pure rEqf
                ) -- TODO substitute in rEqf?: fV for eNewMajor', rV for e', rVEqfV for eEqeNewMajor'

              -- _ ← meth.inferTypePure 7000 newe.toPExpr -- sanity check TODO remove

              assert! not (newe.containsFVar' idrV)
              assert! not (newe.containsFVar' idfV)
              return .some (newe.toPExpr, eEqeNewMajor?)
  else
    let newe := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs |>.toPExpr
    return .some (newe, none)

end
