import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext

-- 238
-- mkId 216

open Lean

section
namespace Lean4Less.TypeChecker.Inner

structure ExtMethodsA (m : Type → Type u) extends ExtMethods m where
  isDefEqForall (t s : PExpr) (numBinds : Nat) (f : Option EExpr → m (Option T)) : m (Bool × Option T)
  alignForAll (numBinds : Nat) (ltl ltr : Expr) : m (Expr × Expr)
  opt : Bool := true

variable [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) (LocalDecl × EExpr)) m] (env : Environment)
  (meth : ExtMethodsA m)

def mkAppEqProof? (aVars bVars : Array LocalDecl) (us vs : Array Level) (Uas Vbs : Array PExpr) (UasEqVbs? : Array (Option EExpr))(ds? : Array (Option (LocalDecl × LocalDecl × EExpr))) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (fEqg? : Option EExpr := none)
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
        let u := us[idx]!
        let v := vs[idx]!
        let d? := ds?[idx]!
        let A := aVar.type.toPExpr

        let Ua := Uas[idx]!
        let Vb := Vbs[idx]!

        let UaEqVb? := UasEqVbs?[idx]!

        let (U, V) := ((Ua, aVar), (Vb, bVar))

        let extra ← if let .some (vaEqb, vbEqa, hAB) := d? then
          let B := bVar.type.toPExpr

          let some fEqg := fEqg? | unreachable!
          let some aEqb := aEqb? | unreachable!

          -- Ua and Vb may still contain references to a and b despite being
          -- defeq (if dep == true), so we need to consider this case, and
          -- cannot immediately fall back to .AB (which has no dependent variant)
          let dep := Ua.containsFVar' aVar || Vb.containsFVar' bVar

          if UaEqVb?.isSome || dep then
            let UaEqVb ← UaEqVb?.getDM $ meth.mkHRefl v.succ (Expr.sort v).toPExpr Ua
            let hUV := {a := aVar, UaEqVb, extra := .some {b := bVar, vaEqb := {aEqb := vaEqb, bEqa := vbEqa}}}
            pure $ .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb}
          else
            assert! not dep
            pure $ .AB {B, hAB, g, fEqg, b, aEqb}
        else
          if let .some UaEqVb := UaEqVb? then
            let some fEqg := fEqg? | unreachable!
            let hUV := {a := aVar, UaEqVb, extra := .none}
            dbg_trace s!"DBG[2]: App.lean:69: aVar={aVar.type}"
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

        pure $ .some $ .app {u, v, A, U, f, a, extra}
      else
        pure none
    f := f.toExpr.app a |>.toPExpr
    g := g.toExpr.app b |>.toPExpr
  pure fEqg?

structure BinderData where
name : Name
dom : PExpr
info : BinderInfo
deriving Inhabited

def mkAppEqProof (T S : PExpr) (TEqS? : Option EExpr) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (fEqg? : Option EExpr := none) : m (Option EExpr) := do
  let rec loop idx T S aVars bVars Uas Vbs UasEqVbs? ds? us vs : m (Option EExpr) := do
    let (T', dA, S', dB) ← match (← meth.whnfPure 205 T).toExpr, (← meth.whnfPure 206 S).toExpr with
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
    let aType ← meth.inferTypePure 207 a
    let bType ← meth.inferTypePure 208 b
    let .true ← meth.isDefEqPure 209 A aType | do
      throw $ .other s!"expected: {A}\n inferred: {aType}"
    let .true ← meth.isDefEqPure 210 B bType | do
      -- let app := Lean.mkAppN g.toExpr (bs[:5].toArray.map PExpr.toExpr)
      -- let appType ← meth.whnfPure $ ← meth.inferTypePure app.toPExpr 205
      -- let .forallE _ _domType _ _ := appType.toExpr | unreachable!
      -- meth.trace s!""
      -- meth.trace s!"app: {appType}"
      -- meth.trace s!"b: {bType}"
      -- meth.trace s!"dom: {domType}"
      -- meth.trace s!"eq: {← isDefEqPure bType domType.toPExpr}"
      -- meth.trace s!"app b: {← whnfPure $ ← inferTypePure (app.app b).toPExpr}"
      -- meth.trace s!""
      throw $ .other s!"expected: {B}\n inferred: {bType}"

    let AEqB? ←
      if A != B then
        let (defEq, AEqB?) ← meth.isDefEq 211 A B
        assert! defEq
        if AEqB?.isSome then
          if asEqbs?[idx]!.isSome then
            -- if idx == 0 then
            pure AEqB?
          else
            assert! ← meth.isDefEqPure 212 A B
            pure none
        else pure none
      else pure none

    let sort ← meth.inferTypePure 213 A
    let .sort u := (← meth.ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"
    let ida := ⟨← meth.mkId 201⟩
    withLCtx ((← getLCtx).mkLocalDecl ida aName A aBi) do
      let some aVar := (← getLCtx).find? ida | unreachable!

      let cont d? bVar := do 
        let ds? := ds?.push d?
        let Ua := (T'.instantiate1 aVar.toExpr).toPExpr
        let Vb := (S'.instantiate1 bVar.toExpr).toPExpr
        let sort ← meth.inferTypePure 238 Ua
        let .sort v := (← meth.ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"

        let us := us.push u
        let vs := vs.push v

        let aVars := aVars.push aVar
        let bVars := bVars.push bVar
        let Uas := Uas.push Ua
        let Vbs := Vbs.push Vb
        let (defEq, UaEqVb?) ← meth.isDefEq 202 Ua Vb
        if let some UaEqVb := UaEqVb? then
          dbg_trace s!"DBG[3]: App.lean:169 {Ua}, {Vb}, {UaEqVb}"
        assert! defEq
        let UasEqVbs? := UasEqVbs?.push UaEqVb?
        if _h : idx < as.size - 1 then
          loop (idx + 1) T S aVars bVars Uas Vbs UasEqVbs? ds? us vs
        else
          let ret ← mkAppEqProof? meth aVars bVars us vs Uas Vbs UasEqVbs? ds? as bs asEqbs? f g fEqg?
          pure ret

      if let some AEqB := AEqB? then 
        let idb := ⟨← meth.mkId 202⟩
        let idaEqb := ⟨← meth.mkId 203⟩
        let idbEqa := ⟨← meth.mkId 204⟩
        withLCtx ((← getLCtx).mkLocalDecl idb bName B bBi) do
          let some bVar := (← getLCtx).find? idb | unreachable!
          let teqsType := mkAppN (.const `HEq [u]) #[A, aVar.toExpr, B, bVar.toExpr]
          let seqtType := mkAppN (.const `HEq [u]) #[B, bVar.toExpr, A, aVar.toExpr]
          withLCtx ((← getLCtx).mkLocalDecl idaEqb default teqsType default) do
            withLCtx ((← getLCtx).mkLocalDecl idbEqa default seqtType default) do
              let some vaEqb := (← getLCtx).find? idaEqb | unreachable!
              let some vbEqa := (← getLCtx).find? idbEqa | unreachable!
              withEqFVar ida idb (vaEqb, (vaEqb.toExpr.toEExpr.reverse aVar.toExpr.toPExpr bVar.toExpr.toPExpr A B u)) do
                let d := (vaEqb, vbEqa, AEqB)
                cont (.some d) bVar
      else
        cont none aVar
  termination_by (as.size - 1) - idx

  if as.size > 0 then
    loop 0 T S #[] #[] #[] #[] #[] #[] #[] #[]
  else
    pure none

-- TODO generalize so can also be used for lambdas
def forallAbs (max : Nat) (tfT sfT : Expr) : m
    (PExpr × Array (FVarId × Name × PExpr) × Array PExpr ×
     PExpr × Array (FVarId × Name × PExpr) × Array PExpr ×
     Array (Option EExpr) × Std.HashSet Nat) := do
  let rec loop tfT sfT tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms (absArgs' : Std.HashSet Nat) idx' (origDomVars origDomVarsAbs : Array (FVarId × FVarId)) (origDomVarsRefs : Std.HashMap (FVarId × FVarId) (Std.HashSet (FVarId × FVarId))) (origDomVarsToNewDomVars : Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) := do

    let withMaybeAbs tType sType tTypeEqsType? f (tName := `tT) (sName := `sT) (tBi := default) (sBi := default) := do 
      if tTypeEqsType?.isSome || origDomVarsAbs.any (tType.containsFVar' ·.1) || origDomVarsAbs.any (sType.containsFVar' ·.2) then
        dbg_trace s!"DBG[4]: App.lean:211: origDomVarsAbs={origDomVarsAbs.map (·.1.name)}"
        dbg_trace s!"DBG[4]: App.lean:211: origDomVarsAbs={origDomVarsAbs.map (·.2.name)}"
        let mut depVars := #[]
        let mut origDepVars := #[]
        let mut origDepVarsSet : Std.HashSet (FVarId × FVarId) := default
        for (tvar, svar) in origDomVars do
          if tType.containsFVar' tvar || sType.containsFVar' svar then
            origDepVarsSet := origDepVarsSet.insert (tvar, svar)
            for (tvar', svar') in origDomVarsRefs.get! (tvar, svar) do
              origDepVarsSet := origDepVarsSet.insert (tvar', svar')

        for (tvar, svar) in origDomVars do
          if origDepVarsSet.contains (tvar, svar) then
            depVars := depVars.push $ origDomVarsToNewDomVars.get! (tvar, svar)
            origDepVars := origDepVars.push $ (tvar, svar)

        let tsort ← meth.ensureSortCorePure (← meth.inferTypePure 214 tType.toPExpr) tType.toPExpr
        let Mt := (← getLCtx).mkForall (depVars.map fun (tvar, _) => (Expr.fvar tvar)) tsort
        let MtNamePrefix := tName.getRoot.toString ++ "T" |>.toName
        let MtName := tName.replacePrefix (tName.getRoot) MtNamePrefix
        let MtVar := (⟨← meth.mkId 205⟩, MtName, Mt.toPExpr)
        let ssort ← meth.ensureSortCorePure (← meth.inferTypePure 215 sType.toPExpr) sType.toPExpr
        let Ms := (← getLCtx).mkForall (depVars.map fun (_, svar) => (Expr.fvar svar)) ssort
        let MsNamePrefix := sName.getRoot.toString ++ "T" |>.toName
        let MsName := sName.replacePrefix (sName.getRoot) MsNamePrefix
        let MsVar := (⟨← meth.mkId 206⟩, MsName, Ms.toPExpr)

        withLCtx ((← getLCtx).mkLocalDecl MtVar.1 MtVar.2.1 MtVar.2.2 tBi) do
          withLCtx ((← getLCtx).mkLocalDecl MsVar.1 MsVar.2.1 MsVar.2.2 sBi) do
            let tDomsVars := tDomsVars.push MtVar
            let sDomsVars := sDomsVars.push MsVar
            let tDom := (← getLCtx).mkLambda (origDepVars.map fun (tvar, _) => (Expr.fvar tvar)) tType |>.toPExpr
            let sDom := (← getLCtx).mkLambda (origDepVars.map fun (_, svar) => (Expr.fvar svar)) sType |>.toPExpr
            let tDoms := tDoms.push tDom
            let sDoms := sDoms.push sDom
            let (true, tDomEqsDom?) ← meth.isDefEq 216 tDom sDom | unreachable!
            let tDomsEqsDoms := tDomsEqsDoms.push tDomEqsDom?
            let newtType := Lean.mkAppN (.fvar MtVar.1) (depVars.map (.fvar ·.1))
            let newsType := Lean.mkAppN (.fvar MsVar.1) (depVars.map (.fvar ·.2))
            f (.some (newtType, newsType)) tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms
      else
        f none tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms

    let cont tBod sBod := do 
      let (true, tBodEqsBod?) ← meth.isDefEq 217 tBod.toPExpr sBod.toPExpr | unreachable!
      withMaybeAbs tBod sBod tBodEqsBod? fun newtsBod? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
        let (newtBod, newsBod) := newtsBod?.getD (tBod, sBod)
        let mut newDomVars := #[]
        for tsvar in origDomVars do
          newDomVars := newDomVars.push (origDomVarsToNewDomVars.get! tsvar)
        pure ((← getLCtx).mkForall (newDomVars.map (fun ((tvar, _) : FVarId × FVarId) => .fvar tvar)) newtBod |>.toPExpr, tDomsVars, tDoms, (← getLCtx).mkForall (newDomVars.map (fun ((_, svar) : FVarId × FVarId) => .fvar svar)) newsBod |>.toPExpr, sDomsVars, sDoms, tDomsEqsDoms, absArgs')

    if idx' < max then
      match (← meth.whnfPure 218 tfT.toPExpr).toExpr, (← meth.whnfPure 219 sfT.toPExpr).toExpr with
        | .forallE tName tDom tBod tBi, .forallE sName sDom sBod sBi =>
          let mut refs := default
          for (tvar, svar) in origDomVars do
            if tDom.containsFVar' tvar || sDom.containsFVar' svar then
              refs := refs.insert (tvar, svar)
              for (tvar', svar') in origDomVarsRefs.get! (tvar, svar) do
                refs := refs.insert (tvar', svar')

          let idt := ⟨← meth.mkId 207⟩

          let (true, tDomEqsDom?) ← meth.isDefEq 220 tDom.toPExpr sDom.toPExpr | unreachable!

          let cont' ids := do
            let tBod := tBod.instantiate1 (.fvar idt)
            let sBod := sBod.instantiate1 (.fvar ids)
            let origDomVarsRefs := origDomVarsRefs.insert (idt, ids) refs
            let origDomVars := origDomVars.push (idt, ids)
            withMaybeAbs tDom sDom tDomEqsDom? (fun newtsDom? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
                if let some (newtDom, newsDom) := newtsDom? then
                  let origDomVarsAbs := origDomVarsAbs.push (idt, ids)
                  let idnewt := ⟨← meth.mkId 208⟩
                  let idnews := ⟨← meth.mkId 209⟩
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
            let some tVar := (← getLCtx).find? idt | unreachable!
            if tDomEqsDom?.isSome then
              let ids := ⟨← meth.mkId 210⟩
              let idtEqs := ⟨← meth.mkId 211⟩
              let idsEqt := ⟨← meth.mkId 212⟩
              let sort ← meth.inferTypePure 221 tDom.toPExpr
              let .sort lvl := (← meth.ensureSortCorePure sort tDom).toExpr | unreachable!
              let teqsType := mkAppN (.const `HEq [lvl]) #[tDom, (.fvar idt), sDom, (.fvar ids)]
              let seqtType := mkAppN (.const `HEq [lvl]) #[sDom, (.fvar ids), tDom, (.fvar idt)]
              withLCtx ((← getLCtx).mkLocalDecl ids sName sDom sBi) do
                let some sVar := (← getLCtx).find? idt | unreachable!
                withLCtx ((← getLCtx).mkLocalDecl idtEqs default teqsType default) do
                  withLCtx ((← getLCtx).mkLocalDecl idsEqt default seqtType default) do
                    let some vtEqs := (← getLCtx).find? idtEqs | unreachable!
                    -- let some vsEqt := (← getLCtx).find? idsEqt | unreachable!
                    withEqFVar idt ids (vtEqs, (vtEqs.toExpr.toEExpr.reverse tVar.toExpr.toPExpr sVar.toExpr.toPExpr tDom.toPExpr sDom.toPExpr lvl)) do -- TODO verify that we actually need this
                      cont' ids
            else
              cont' idt
        | tBod, sBod =>
          cont tBod sBod
    else
      cont tfT sfT
  loop tfT sfT #[] #[] #[] #[] #[] default 0 #[] #[] default default

mutual
def deconstructAppHEq' (s t : PExpr) (sEqt : EExpr) (S T : PExpr) : m (Array PExpr × Array PExpr × Array (Option EExpr) × Array (FVarId × Name × PExpr) × Array (FVarId × Name × PExpr) × PExpr × PExpr) := do match sEqt with
| .app d => deconstructAppHEq d
| _ => do
  pure ()
  let sVar := (⟨← meth.mkId 215⟩, default, S) -- TODO get the names somehow?
  let tVar := (⟨← meth.mkId 216⟩, default, T)
  pure (#[s], #[t], #[.some sEqt], #[sVar], #[tVar], Expr.fvar sVar.1 |>.toPExpr, Expr.fvar tVar.1 |>.toPExpr)

def deconstructAppHEq : AppData EExpr
  → m (Array PExpr × Array PExpr × Array (Option EExpr) × Array (FVarId × Name × PExpr) × Array (FVarId × Name × PExpr) × PExpr × PExpr)
| {f, a, extra, A, U, ..} => do
  match extra with
  | .ABUV {g, fEqg, b, aEqb, B, V, ..} =>
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[V.2] V.1)
    let (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' a b aEqb A B
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .UV {g, fEqg, b, aEqb, V, ..}      =>
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[V.2] V.1)
    let (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' a b aEqb A A
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .AB {g, fEqg, b, aEqb, B, ..}      => 
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[U.2] U.1)
    let (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' a b aEqb A B
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .none {g, fEqg, b, aEqb, ..}       => 
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[U.2] U.1)
    let (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' a b aEqb A A
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .UVFun {g, fEqg, V, ..}            => 
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[V.2] V.1)
    pure (tas, sas, taEqsas?, tVars, sVars, f'.app a, g'.app a)
  | .Fun {g, fEqg, ..}                 => 
    let (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' f g fEqg (mkForall #[U.2] U.1) (mkForall #[U.2] U.1)
    pure (tas, sas, taEqsas?, tVars, sVars, f'.app a, g'.app a)
  | .Arg {b, aEqb, ..}                 =>
    let (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' a b aEqb A A
    pure (tas', sas', taEqsas?', tVars', sVars', f.app a', f.app b')
end


def isDefEqAppOpt''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, tfEqsf?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
    else meth.isDefEq 222 tf sf | return (false, none)

  let mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs _tArgsVars _sArgsVars tBodT sBodT tEtaVars sEtaVars idx := do -- FIXME why do I have to pass in the mutable variables?
    if tVars.size > 0 then
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
      -- let (tfType', sfType') ← meth.alignForAll tArgs.size tfType sfType -- TODO how to put .toPExpr directly on matched vars?
      -- let (defEq, p?) ← meth.isDefEqForall tfType.toPExpr sfType.toPExpr tVars.size fun tfTypeEqsfType? => do
      --   let ret ← mkAppEqProof meth tfType.toPExpr sfType.toPExpr tfTypeEqsfType? tArgs' sArgs' taEqsas' tf'.toPExpr sf'.toPExpr
      --   pure ret -- FIXME reduce redexes in last two values (construct partial application directly)
      -- assert! defEq

      let p? ← mkAppEqProof meth tfType.toPExpr sfType.toPExpr none tArgs' sArgs' taEqsas' tf'.toPExpr sf'.toPExpr
      pure p?
    else
      pure none

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
  let mut absArgs : Std.HashSet Nat := default
  let mut tfT ← meth.inferTypePure 223 tBodFun -- FIXME avoid when possible
  let mut sfT ← meth.inferTypePure 224 sBodFun
  let mut tBodT := tfT
  let mut sBodT := sfT
  let mut taEqsas' := #[]

  for idx in [:tArgs.size] do
    let (tBodDom, tDomName, sBodDom, sDomName) ← do
      let ok? ←
        if idx == 0 && tfEqsf?.isSome then
          pure none
        else
          let tBodT' ← meth.whnfPure 225 tBodT
          let sBodT' ← meth.whnfPure 226 sBodT
          match tBodT'.toExpr, sBodT'.toExpr with
            | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
              if tArgsVars.any fun id => tDom.containsFVar' id || sArgsVars.any fun id => sDom.containsFVar' id then
                absArgs := absArgs.insert idx
              pure $ .some (tDom, tDomName, sDom, sDomName)
            | _, _ => pure none

      if let .some (tBodDom, tDomName, sBodDom, sDomName) := ok? then
        pure (tBodDom.toPExpr, tDomName, sBodDom.toPExpr, sDomName)
      else -- the current partial application needs to be abstracted as a function
        let tfEqsf'? ←
          if idx == 0 && tfEqsf?.isSome then
            pure (tfEqsf?)
          else
            mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars idx
        let tf := (Lean.mkAppN tf (tArgs[:idx].toArray.map (·.toExpr))).toPExpr
        let sf := (Lean.mkAppN sf (sArgs[:idx].toArray.map (·.toExpr))).toPExpr

        -- TODO
        let ((tfVar : FVarId × Name × PExpr), tfTAbsDomsVars, tfTAbsDoms, (sfVar : FVarId × Name × PExpr), sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs') ← do
          let (tfType, tfTAbsDomsVars, tfTAbsDoms, sfType, sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgsOffset') ← forallAbs meth (tArgs.size - idx) tfT.toExpr sfT.toExpr
          let mut absArgs' := default
          for pos in absArgsOffset' do
            absArgs' := absArgs'.insert (pos + idx)
          pure ((⟨← meth.mkId 213⟩, `f, tfType), tfTAbsDomsVars, tfTAbsDoms, (⟨← meth.mkId 214⟩, `g, sfType), sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs')

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

        let tBodT' ← meth.whnfPure 227 tBodT
        let sBodT' ← meth.whnfPure 228 sBodT
        match tBodT'.toExpr, sBodT'.toExpr with
          | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
            pure $ (tDom.toPExpr, tDomName, sDom.toPExpr, sDomName)
          | _, _ => unreachable!
    let ta := tArgs[idx]!
    let sa := sArgs[idx]!

    let mut taEqsa? := none
    if let some _p? := targsEqsargs?.get? idx then
      taEqsa? := _p?
    else
      let (.true, _p?) ← meth.isDefEq 229 ta sa | return (false, none)
      taEqsa? := _p?
    let taEqsaData? := taEqsa?.map (ta, sa, ·)
    taEqsaDatas := taEqsaDatas.push taEqsaData?

    let (tBoda, sBoda) ← if taEqsa?.isSome || absArgs.contains idx then
      let getDefVals := do
        let tVar := (⟨← meth.mkId 215⟩, tDomName, tBodDom)
        let sVar := (⟨← meth.mkId 216⟩, sDomName, sBodDom)
        pure (#[ta], #[sa], #[taEqsa?], #[tVar], #[sVar], Expr.fvar tVar.1 |>.toPExpr, Expr.fvar sVar.1 |>.toPExpr)

      let mut dbg := false
      let (tas', sas', taEqsas'?, tVars', sVars', tBoda', sBoda') ←
          if let some taEqsa := taEqsa? then
            match taEqsa with
            | .app d =>
              dbg_trace s!"DBG[5]: App.lean:496 {tVars.map (·.2)}, {ta}, {sa}, {taEqsa}"
              dbg := true
              let ret ← deconstructAppHEq meth d
              pure ret
            | _ => getDefVals
          else
            getDefVals
      if dbg then
        dbg_trace s!"DBG[6]: App.lean:497 {tas'}, {sas'}, {tVars'.map (·.2)}, {sVars'.map (·.2)}, {tBoda'}, {sBoda'}"

      tArgs' := tArgs' ++ tas'
      sArgs' := sArgs' ++ sas'
      taEqsas' := taEqsas' ++ taEqsas'?

      tVars := tVars ++ tVars'
      sVars := sVars ++ sVars'
      tArgsVars := tArgsVars ++ (tVars'.map (·.1))
      sArgsVars := sArgsVars ++ (sVars'.map (·.1))
      tEtaVars := tEtaVars + tVars'.size
      sEtaVars := sEtaVars + tVars'.size

      pure (tBoda', sBoda')
    else 
      tEtaVars := 0
      sEtaVars := 0
      pure (ta, sa)

    tBodArgs := tBodArgs.push tBoda
    sBodArgs := sBodArgs.push sBoda

    (tfT, sfT) ← match (← meth.whnfPure 230 tfT).toExpr, (← meth.whnfPure 231 sfT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        pure $ (tBody.instantiate1 ta |>.toPExpr, sBody.instantiate1 sa |>.toPExpr)
      | _, _ => unreachable!

    (tBodT, sBodT) ← match (← meth.whnfPure 232 tBodT).toExpr, (← meth.whnfPure 233 sBodT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        pure $ (tBody.instantiate1 tBoda |>.toPExpr, sBody.instantiate1 sBoda |>.toPExpr)
      | _, _ => unreachable!

  dbg_trace s!"DBG[7]: App.lean:536 {tBodFun}, {sBodFun}"
  let tEqs? ← mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars tArgs'.size
  -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
  return (true, (tEqs?.map fun tEqs => (tEqs, taEqsaDatas)))

def isDefEqApp''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, _ret?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
    else meth.isDefEq 234 tf sf | return (false, none)

  let mut taEqsas := #[]
  let mut idx := 0
  for ta in tArgs, sa in sArgs do
    let mut p? := none
    if let some _p? := targsEqsargs?[idx]? then
      p? := _p?
    else
      let (.true, _p?) ← meth.isDefEq 235 ta sa | return (false, none)
      p? := _p?
    taEqsas := taEqsas.push (p?.map (ta, sa, ·))
    idx := idx + 1

  let mut tfT ← meth.inferTypePure 236 tf
  let mut sfT ← meth.inferTypePure 237 sf
  -- let (tfT', sfT') ← meth.alignForAll tArgs.size tfT sfT -- TODO how to put .toPExpr directly on matched vars?
  -- let (defEq, tEqs?) ← meth.isDefEqForall tfT'.toPExpr sfT'.toPExpr tArgs.size fun tfTEqsfT? =>
  --   mkAppEqProof meth tfT sfT tfTEqsfT? tArgs sArgs (taEqsas.map (·.map (·.2.2))) tf sf _ret?
  -- assert! defEq
  let tEqs? ← mkAppEqProof meth tfT sfT none tArgs sArgs (taEqsas.map (·.map (·.2.2))) tf sf _ret?

  -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
  return (true, (tEqs?.map fun tEqs => (tEqs, taEqsas)))

def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do

  if meth.opt then
    isDefEqAppOpt''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?
  else
    isDefEqApp''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?

/--
Checks if applications `t` and `s` (should be WHNF) are defeq on account of
their function heads and arguments being defeq.
-/
def isDefEqApp' (t s : PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless t.toExpr.isApp && s.toExpr.isApp do return (false, none)
  t.toExpr.withApp fun tf tArgs =>
  s.toExpr.withApp fun sf sArgs => 
    let tf := tf.toPExpr
    let sf := sf.toPExpr
    let tArgs := tArgs.map (·.toPExpr)
    let sArgs := sArgs.map (·.toPExpr)
    isDefEqApp'' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?

def isDefEqApp (t s : PExpr) (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × Option EExpr) := do
  let (isDefEq, data?) ← isDefEqApp' meth t s targsEqsargs? tfEqsf?
  pure (isDefEq, data?.map (·.1))
