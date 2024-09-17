import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext

open Lean

section
namespace Lean4Less.TypeChecker.Inner

structure ExtMethodsA (m : Type → Type u) extends ExtMethods m where
  opt : Bool := true

variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (HashMap (FVarId × FVarId) (FVarId × FVarId)) m] (env : Environment)
  (meth : ExtMethodsA m)

def mkAppEqProof? (aVars bVars : Array PExpr) (Uas Vbs : Array PExpr) (ds? : Array (Option (FVarId × FVarId × EExpr))) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (fEqg? : Option EExpr := none)
: m (Option EExpr) := do
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
        let A ← meth.inferTypePure aVar 201

        let lctx ← getLCtx

        let (u, _) ← meth.getTypeLevel aVar

        let Ua := Uas[idx]!
        let Vb := Vbs[idx]!

        let (defEq, UaEqVb?) ← meth.isDefEq Ua Vb
        assert! defEq

        let (UaTypeLvl, UaType) ← meth.getTypeLevel Ua
        let UaType ← meth.whnfPure UaType
        let v := UaType.toExpr.sortLevel!

        let (U, V) := ((Ua, aVar), (Vb, bVar))

        let extra ← if let .some (idaEqb, idbEqa, hAB) := d? then
          let B ← meth.inferTypePure bVar 202

          let some fEqg := fEqg? | unreachable!
          let some aEqb := aEqb? | unreachable!

          -- Ua and Vb may still contain references to a and b despite being
          -- defeq (if dep == true), so we need to consider this case, and
          -- cannot immediately fall back to .AB (which has no dependent variant)
          let dep := Ua.toExpr.containsFVar aVar.toExpr.fvarId! || Vb.toExpr.containsFVar bVar.toExpr.fvarId!

          if UaEqVb?.isSome || dep then
            let UaEqVb ← UaEqVb?.getDM $ meth.mkHRefl UaTypeLvl UaType Ua
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

    f ← meth.whnfPure (f.toExpr.app a |>.toPExpr)
    g ← meth.whnfPure (g.toExpr.app b |>.toPExpr)
  pure fEqg?

structure BinderData where
name : Name
dom : PExpr
info : BinderInfo
deriving Inhabited

def mkAppEqProof (T S : PExpr) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (fEqg? : Option EExpr := none) : m (Option EExpr) := do
  let rec loop idx T S aVars bVars Uas Vbs ds? : m (Option EExpr) := do
    let (T', dA, S', dB) ← match (← meth.whnfPure T).toExpr, (← meth.whnfPure S).toExpr with
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
    let aType ← meth.inferTypePure a 203
    let bType ← meth.inferTypePure b 204
    let .true ← meth.isDefEqPure A aType | do
      throw $ .other s!"expected: {A}\n inferred: {aType}"
    let .true ← meth.isDefEqPure B bType | do
      -- let app := Lean.mkAppN g.toExpr (bs[:5].toArray.map PExpr.toExpr)
      -- let appType ← meth.whnfPure $ ← meth.inferTypePure app.toPExpr 205
      -- let .forallE _ _domType _ _ := appType.toExpr | unreachable!
      -- dbg_trace s!""
      -- dbg_trace s!"app: {appType}"
      -- dbg_trace s!"b: {bType}"
      -- dbg_trace s!"dom: {domType}"
      -- dbg_trace s!"eq: {← isDefEqPure bType domType.toPExpr}"
      -- dbg_trace s!"app b: {← whnfPure $ ← inferTypePure (app.app b).toPExpr}"
      -- dbg_trace s!""
      throw $ .other s!"expected: {B}\n inferred: {bType}"

    let AEqB? ← if A != B then
      let (defEq, AEqB?) ← meth.isDefEq A B
      -- if idx == 0 then
      assert! defEq
      pure AEqB?
    else pure (none)

    let sort ← meth.inferTypePure A 206
    let .sort lvl := (← meth.ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"
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
          mkAppEqProof? meth aVars bVars Uas Vbs ds? as bs asEqbs? f g fEqg?

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
              withEqFVar ida idb (idaEqb, idbEqa) do
                let d := (idaEqb, idbEqa, AEqB)
                cont (.some d) bVar
      else
        cont none aVar
  termination_by (as.size - 1) - idx

  if as.size > 0 then
    loop 0 T S #[] #[] #[] #[] #[]
  else
    pure none

def forallAbs (max : Nat) (tfT sfT : Expr) : m
    (PExpr × Array (FVarId × Name × PExpr) × Array PExpr ×
     PExpr × Array (FVarId × Name × PExpr) × Array PExpr ×
     Array (Option EExpr) × HashSet Nat) := do
  let rec loop tfT sfT tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms (absArgs' : HashSet Nat) idx' (origDomVars origDomVarsAbs : Array (FVarId × FVarId)) (origDomVarsRefs : HashMap (FVarId × FVarId) (HashSet (FVarId × FVarId))) (origDomVarsToNewDomVars : HashMap (FVarId × FVarId) (FVarId × FVarId)) := do

    let withMaybeAbs tType sType tTypeEqsType? f (tName := `tT) (sName := `sT) (tBi := default) (sBi := default) := do 
      if tTypeEqsType?.isSome || origDomVarsAbs.any (tType.containsFVar ·.1) || origDomVarsAbs.any (sType.containsFVar ·.2) then
        let mut depVars := #[]
        let mut origDepVars := #[]
        let mut origDepVarsSet : HashSet (FVarId × FVarId) := default
        for (tvar, svar) in origDomVars do
          if tType.containsFVar tvar || sType.containsFVar svar then
            origDepVarsSet := origDepVarsSet.insert (tvar, svar)
            for (tvar', svar') in origDomVarsRefs.find! (tvar, svar) do
              origDepVarsSet := origDepVarsSet.insert (tvar', svar')

        for (tvar, svar) in origDomVars do
          if origDepVarsSet.contains (tvar, svar) then
            depVars := depVars.push $ origDomVarsToNewDomVars.find! (tvar, svar)
            origDepVars := origDepVars.push $ (tvar, svar)

        let tsort ← meth.ensureSortCorePure (← meth.inferTypePure tType.toPExpr 207) tType.toPExpr
        let Mt := (← getLCtx).mkForall (depVars.map fun (tvar, _) => (Expr.fvar tvar)) tsort
        let MtNamePrefix := tName.getRoot.toString ++ "T" |>.toName
        let MtName := tName.replacePrefix (tName.getRoot) MtNamePrefix
        let MtVar := (⟨← mkFreshId⟩, MtName, Mt.toPExpr)
        let ssort ← meth.ensureSortCorePure (← meth.inferTypePure sType.toPExpr 208) sType.toPExpr
        let Ms := (← getLCtx).mkForall (depVars.map fun (_, svar) => (Expr.fvar svar)) ssort
        let MsNamePrefix := sName.getRoot.toString ++ "T" |>.toName
        let MsName := sName.replacePrefix (sName.getRoot) MsNamePrefix
        let MsVar := (⟨← mkFreshId⟩, MsName, Ms.toPExpr)

        withLCtx ((← getLCtx).mkLocalDecl MtVar.1 MtVar.2.1 MtVar.2.2 tBi) do
          withLCtx ((← getLCtx).mkLocalDecl MsVar.1 MsVar.2.1 MsVar.2.2 sBi) do
            let tDomsVars := tDomsVars.push MtVar
            let sDomsVars := sDomsVars.push MsVar
            let tDom := (← getLCtx).mkLambda (origDepVars.map fun (tvar, _) => (Expr.fvar tvar)) tType |>.toPExpr
            let sDom := (← getLCtx).mkLambda (origDepVars.map fun (_, svar) => (Expr.fvar svar)) sType |>.toPExpr
            let tDoms := tDoms.push tDom
            let sDoms := sDoms.push sDom
            let (true, tDomEqsDom?) ← meth.isDefEq tDom sDom | unreachable!
            let tDomsEqsDoms := tDomsEqsDoms.push tDomEqsDom?
            let newtType := Lean.mkAppN (.fvar MtVar.1) (depVars.map (.fvar ·.1))
            let newsType := Lean.mkAppN (.fvar MsVar.1) (depVars.map (.fvar ·.2))
            f (.some (newtType, newsType)) tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms
      else
        f none tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms

    let cont tBod sBod := do 
      let (true, tBodEqsBod?) ← meth.isDefEq tBod.toPExpr sBod.toPExpr | unreachable!
      withMaybeAbs tBod sBod tBodEqsBod? fun newtsBod? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
        let (newtBod, newsBod) := newtsBod?.getD (tBod, sBod)
        let mut newDomVars := #[]
        for tsvar in origDomVars do
          newDomVars := newDomVars.push (origDomVarsToNewDomVars.find! tsvar)
        pure ((← getLCtx).mkForall (newDomVars.map (fun ((tvar, _) : FVarId × FVarId) => .fvar tvar)) newtBod |>.toPExpr, tDomsVars, tDoms, (← getLCtx).mkForall (newDomVars.map (fun ((_, svar) : FVarId × FVarId) => .fvar svar)) newsBod |>.toPExpr, sDomsVars, sDoms, tDomsEqsDoms, absArgs')

    if idx' < max then
      match (← meth.whnfPure tfT.toPExpr).toExpr, (← meth.whnfPure sfT.toPExpr).toExpr with
        | .forallE tName tDom tBod tBi, .forallE sName sDom sBod sBi =>
          let mut refs := default
          for (tvar, svar) in origDomVars do
            if tDom.containsFVar tvar || sDom.containsFVar svar then
              refs := refs.insert (tvar, svar)
              for (tvar', svar') in origDomVarsRefs.find! (tvar, svar) do
                refs := refs.insert (tvar', svar')

          let idt := ⟨← mkFreshId⟩

          let (true, tDomEqsDom?) ← meth.isDefEq tDom.toPExpr sDom.toPExpr | unreachable!

          let cont' ids := do
            let tBod := tBod.instantiate1 (.fvar idt)
            let sBod := sBod.instantiate1 (.fvar ids)
            let origDomVarsRefs := origDomVarsRefs.insert (idt, ids) refs
            let origDomVars := origDomVars.push (idt, ids)
            withMaybeAbs tDom sDom tDomEqsDom? (fun newtsDom? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
                if let some (newtDom, newsDom) := newtsDom? then
                  let origDomVarsAbs := origDomVarsAbs.push (idt, ids)
                  let idnewt := ⟨← mkFreshId⟩
                  let idnews := ⟨← mkFreshId⟩
                  withLCtx ((← getLCtx).mkLocalDecl idnewt tName newtDom tBi) do
                    withLCtx ((← getLCtx).mkLocalDecl idnews sName newsDom sBi) do
                      let origDomVarsToNewDomVars := origDomVarsToNewDomVars.insert (idt, ids) (idnewt, idnews)
                      let absArgs' := absArgs'.insert idx'
                      loop tBod sBod tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms absArgs' (idx' + 1) origDomVars origDomVarsAbs origDomVarsRefs origDomVarsToNewDomVars
                else
                  let origDomVarsToNewDomVars := origDomVarsToNewDomVars.insert (idt, ids) (idt, ids)
                  loop tBod sBod tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms absArgs' (idx' + 1) origDomVars origDomVarsAbs origDomVarsRefs origDomVarsToNewDomVars
              )
              tName sName

          withLCtx ((← getLCtx).mkLocalDecl idt tName tDom tBi) do
            if tDomEqsDom?.isSome then
              let ids := ⟨← mkFreshId⟩
              let idtEqs := ⟨← mkFreshId⟩
              let idsEqt := ⟨← mkFreshId⟩
              let sort ← meth.inferTypePure tDom.toPExpr 209
              let .sort lvl := (← meth.ensureSortCorePure sort tDom).toExpr | unreachable!
              let teqsType := mkAppN (.const `HEq [lvl]) #[tDom, (.fvar idt), sDom, (.fvar ids)]
              let seqtType := mkAppN (.const `HEq [lvl]) #[sDom, (.fvar ids), tDom, (.fvar idt)]
              withLCtx ((← getLCtx).mkLocalDecl ids sName sDom sBi) do
                withLCtx ((← getLCtx).mkLocalDecl idtEqs default teqsType default) do
                  withLCtx ((← getLCtx).mkLocalDecl idsEqt default seqtType default) do
                    withEqFVar idt ids (idtEqs, idsEqt) do
                      cont' ids
            else
              cont' idt
        | tBod, sBod =>
          cont tBod sBod
    else
      cont tfT sfT
  loop tfT sfT #[] #[] #[] #[] #[] default 0 #[] #[] default default


def isDefEqAppOpt''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, tfEqsf?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
    else meth.isDefEq tf sf | return (false, none)

  let mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs _tArgsVars _sArgsVars tBodT sBodT tEtaVars sEtaVars idx := do -- FIXME why do I have to pass in the mutable variables?
    let tLCtx := tVars.foldl (init := (← getLCtx)) fun acc (id, n, (type : PExpr)) => LocalContext.mkLocalDecl acc id n type default
    let sLCtx := sVars.foldl (init := (← getLCtx)) fun acc (id, n, (type : PExpr)) => LocalContext.mkLocalDecl acc id n type default
    let tVars' := tVars[:tVars.size - tEtaVars].toArray
    let sVars' := sVars[:sVars.size - sEtaVars].toArray
    let tBodArgs' := tBodArgs[:tBodArgs.size - tEtaVars].toArray
    let sBodArgs' := sBodArgs[:sBodArgs.size - sEtaVars].toArray
    let tf' := tLCtx.mkLambda (tVars'.map (.fvar ·.1)) (Lean.mkAppN tBodFun (tBodArgs'.map (·.toExpr)))
    let sf' := sLCtx.mkLambda (sVars'.map (.fvar ·.1)) (Lean.mkAppN sBodFun (sBodArgs'.map (·.toExpr)))
    let tfType := tLCtx.mkForall (tVars.map (.fvar ·.1)) tBodT
    let sfType := sLCtx.mkForall (sVars.map (.fvar ·.1)) sBodT
    let ret ← mkAppEqProof meth tfType.toPExpr sfType.toPExpr tArgs' sArgs' taEqsas' tf'.toPExpr sf'.toPExpr
    pure (ret, (Lean.mkAppN tf (tArgs[:idx].toArray.map (·.toExpr))).toPExpr, (Lean.mkAppN sf (sArgs[:idx].toArray.map (·.toExpr))).toPExpr) -- FIXME reduce redexes in last two values (construct partial application directly)

  let mut taEqsaDatas := #[]

  let mut tBodFun : PExpr := tf
  let mut tBodArgs : Array PExpr := #[]
  let mut sBodFun : PExpr := sf
  let mut sBodArgs : Array PExpr := #[]
  let mut tArgs' := #[]
  let mut sArgs' := #[]
  let mut tVars : Array (FVarId × Name × PExpr) := #[]
  let mut sVars : Array (FVarId × Name × PExpr) := #[]
  let mut tArgsVars : Array FVarId := #[]
  let mut sArgsVars : Array FVarId := #[]
  let mut tEtaVars : Nat := 0 -- number of vars that can be eliminated from the lambda by eta reduction
  let mut sEtaVars : Nat := 0
  let mut absArgs : HashSet Nat := default
  let mut tfT ← meth.inferTypePure tBodFun 210
  let mut sfT ← meth.inferTypePure sBodFun 211
  let mut tBodT := tfT
  let mut sBodT := sfT
  let mut taEqsas' := #[]

  -- assert! tfEqsf?.isNone -- FIXME

  for idx in [:tArgs.size] do
    let (tBodDom, tDomName, sBodDom, sDomName) ← do
      let ok? ←
        if idx == 0 && tfEqsf?.isSome then
          pure none
        else
          let tBodT' ← meth.whnfPure tBodT
          let sBodT' ← meth.whnfPure sBodT
          match tBodT'.toExpr, sBodT'.toExpr with
            | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
              if tArgsVars.any fun id => tDom.containsFVar id || sArgsVars.any fun id => sDom.containsFVar id then
                absArgs := absArgs.insert idx
              pure $ .some (tDom, tDomName, sDom, sDomName)
            | _, _ => pure none

      if let .some (tBodDom, tDomName, sBodDom, sDomName) := ok? then
        pure (tBodDom.toPExpr, tDomName, sBodDom.toPExpr, sDomName)
      else
        let (tfEqsf'?, tf, sf) ←
          if idx == 0 && tfEqsf?.isSome then
            pure (tfEqsf?, tf, sf)
          else
            mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars idx

        -- TODO
        let ((tfVar : FVarId × Name × PExpr), tfTAbsDomsVars, tfTAbsDoms, (sfVar : FVarId × Name × PExpr), sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs') ← do
          let (tfType, tfTAbsDomsVars, tfTAbsDoms, sfType, sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgsOffset') ← forallAbs meth (tArgs.size - idx) tfT.toExpr sfT.toExpr
          let mut absArgs' := default
          for pos in absArgsOffset' do
            absArgs' := absArgs'.insert (pos + idx)
          pure ((⟨← mkFreshId⟩, `f, tfType), tfTAbsDomsVars, tfTAbsDoms, (⟨← mkFreshId⟩, `g, sfType), sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs')

        tBodFun := Expr.fvar tfVar.1 |>.toPExpr
        sBodFun := Expr.fvar sfVar.1 |>.toPExpr
        tBodArgs := #[]
        sBodArgs := #[]
        tBodT := tfVar.2.2
        sBodT := sfVar.2.2
        taEqsas' := tfTAbsDomsEqsfTAbsDoms? ++ #[tfEqsf'?]
        tArgs' := tfTAbsDoms ++ #[tf]
        sArgs' := sfTAbsDoms ++ #[sf]
        tArgsVars := #[]
        sArgsVars := #[]
        tVars := tfTAbsDomsVars ++ #[tfVar]
        sVars := sfTAbsDomsVars ++ #[sfVar]
        tEtaVars := 0
        sEtaVars := 0
        absArgs := absArgs'

        let tBodT' ← meth.whnfPure tBodT
        let sBodT' ← meth.whnfPure sBodT
        match tBodT'.toExpr, sBodT'.toExpr with
          | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
            pure $ (tDom.toPExpr, tDomName, sDom.toPExpr, sDomName)
          | _, _ => unreachable!

    let ta := tArgs[idx]!
    let sa := sArgs[idx]!

    let mut taEqsa? := none
    if let some _p? := targsEqsargs?.find? idx then
      taEqsa? := _p?
    else
      let (.true, _p?) ← meth.isDefEq ta sa | return (false, none)
      taEqsa? := _p?
    let taEqsaData? := taEqsa?.map (ta, sa, ·)
    taEqsaDatas := taEqsaDatas.push taEqsaData?

    let (tBoda, sBoda) ← if taEqsa?.isSome || absArgs.contains idx then
      tArgs' := tArgs'.push ta
      sArgs' := sArgs'.push sa
      taEqsas' := taEqsas'.push taEqsa?

      let tVar := (⟨← mkFreshId⟩, tDomName, tBodDom)
      let sVar := (⟨← mkFreshId⟩, sDomName, sBodDom)

      tVars := tVars.push tVar
      sVars := sVars.push sVar
      tArgsVars := tArgsVars.push tVar.1
      sArgsVars := sArgsVars.push sVar.1
      tEtaVars := tEtaVars + 1
      sEtaVars := sEtaVars + 1

      pure (Expr.fvar tVar.1 |>.toPExpr, Expr.fvar sVar.1 |>.toPExpr)
    else 
      tEtaVars := 0
      sEtaVars := 0
      pure (ta, sa)

    tBodArgs := tBodArgs.push tBoda
    sBodArgs := sBodArgs.push sBoda

    (tfT, sfT) ← match (← meth.whnfPure tfT).toExpr, (← meth.whnfPure sfT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        pure $ (tBody.instantiate1 ta |>.toPExpr, sBody.instantiate1 sa |>.toPExpr)
      | _, _ => unreachable!

    (tBodT, sBodT) ← match (← meth.whnfPure tBodT).toExpr, (← meth.whnfPure sBodT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        pure $ (tBody.instantiate1 tBoda |>.toPExpr, sBody.instantiate1 sBoda |>.toPExpr)
      | _, _ => unreachable!

  let (tEqs?, _, _) ← mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars tArgs'.size
  -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
  return (true, (tEqs?.map fun tEqs => (tEqs, taEqsaDatas)))

def isDefEqApp''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, _ret?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
    else meth.isDefEq tf sf | return (false, none)

  let mut taEqsas := #[]
  let mut idx := 0
  for ta in tArgs, sa in sArgs do
    let mut p? := none
    if let some _p? := targsEqsargs?.find? idx then
      p? := _p?
    else
      let (.true, _p?) ← meth.isDefEq ta sa | return (false, none)
      p? := _p?
    taEqsas := taEqsas.push (p?.map (ta, sa, ·))
    idx := idx + 1

  let mut tfT ← meth.inferTypePure tf 212
  let mut sfT ← meth.inferTypePure sf 213

  let tEqs? ← mkAppEqProof meth tfT sfT tArgs sArgs (taEqsas.map (·.map (·.2.2))) tf sf _ret?

  -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
  return (true, (tEqs?.map fun tEqs => (tEqs, taEqsas)))

def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do

  if meth.opt then
    isDefEqAppOpt''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?
  else
    isDefEqApp''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?

/--
Checks if applications `t` and `s` (should be WHNF) are defeq on account of
their function heads and arguments being defeq.
-/
def isDefEqApp' (t s : PExpr)
   (targsEqsargs? : HashMap Nat (Option EExpr) := default) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless t.toExpr.isApp && s.toExpr.isApp do return (false, none)
  t.toExpr.withApp fun tf tArgs =>
  s.toExpr.withApp fun sf sArgs => 
    let tf := tf.toPExpr
    let sf := sf.toPExpr
    let tArgs := tArgs.map (·.toPExpr)
    let sArgs := sArgs.map (·.toPExpr)
    isDefEqApp'' meth tf sf tArgs sArgs targsEqsargs?

def isDefEqApp (t s : PExpr) (targsEqsargs? : HashMap Nat (Option EExpr) := default) : m (Bool × Option EExpr) := do
  let (isDefEq, data?) ← isDefEqApp' meth t s targsEqsargs?
  pure (isDefEq, data?.map (·.1))
