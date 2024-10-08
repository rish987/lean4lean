import Lean
import Lean4Less.PExpr

open Lean

namespace Lean4Less

def mkLambda (vars : Array LocalDecl) (b : Expr) : PExpr := LocalContext.mkLambda (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr
def mkForall (vars : Array LocalDecl) (b : Expr) : PExpr := LocalContext.mkForall (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr

def getMaybeDepLemmaApp (Uas : Array PExpr) (as : Array LocalDecl) : Array PExpr × Bool :=
  let dep := Uas.zip as |>.foldl (init := false) fun acc (Ua, a) =>
    Ua.toExpr.containsFVar a.fvarId || acc
  let ret := Uas.zip as |>.map fun (Ua, a) =>
    if dep then
      mkLambda #[a] Ua
    else
      Ua
  (ret, dep)

def getMaybeDepLemmaApp1 (U : PExpr × LocalDecl) : (PExpr × Bool) :=
  let (Ua, a) := U
  match getMaybeDepLemmaApp #[Ua] #[a] with
  | (#[U], dep) => (U, dep)
  | _ => unreachable!

def getMaybeDepLemmaApp2 (U V : (PExpr × LocalDecl)) : (PExpr × PExpr × Bool) :=
  let (Ua, a) := U
  let (Vb, b) := V
  match getMaybeDepLemmaApp #[Ua, Vb] #[a, b] with
  | (#[U, V], dep) => (U, V, dep)
  | _ => unreachable!



/--
Tracks fvars for an equality in both directions (useful when reversing equalities).
-/
structure FVarData where
aEqb : LocalDecl
bEqa : LocalDecl
deriving Inhabited

structure SorryData where
u    : Level
A    : PExpr
a    : PExpr
B    : PExpr
b    : PExpr
deriving Inhabited



structure LamABData (EExpr : Type) :=
B      : PExpr
b      : LocalDecl
vaEqb  : FVarData
hAB    : EExpr

structure LamUVData :=
V   : PExpr × LocalDecl

inductive LamDataExtra (EExpr : Type) :=
| ABUV : LamABData EExpr → LamUVData → LamDataExtra EExpr
| UV   : LamUVData → LamDataExtra EExpr
| none : LamDataExtra EExpr
deriving Inhabited

structure LamData (EExpr : Type) :=
u      : Level
v      : Level
A      : PExpr
U      : PExpr × LocalDecl
f      : PExpr
a      : LocalDecl
g      : PExpr
faEqgx : EExpr
extra  : LamDataExtra EExpr := .none
deriving Inhabited



structure ForallABData (EExpr : Type) :=
B      : PExpr
b      : LocalDecl
vaEqb  : FVarData
hAB    : EExpr

structure ForallABAppData (EExpr : Type) :=
b      : LocalDecl
vaEqb  : FVarData

inductive ForallDataExtra (EExpr : Type) :=
| AB   : ForallABData EExpr → ForallDataExtra EExpr
| ABApp: ForallABAppData EExpr → ForallDataExtra EExpr
| none : ForallDataExtra EExpr
deriving Inhabited

structure ForallData (EExpr : Type) :=
u      : Level
v      : Level
A      : PExpr
a      : LocalDecl
U      : PExpr × LocalDecl
V      : PExpr × LocalDecl
UaEqVx : EExpr
extra  : ForallDataExtra EExpr := .none
deriving Inhabited



structure HUVDataExtra (EExpr : Type) where
b      : LocalDecl
vaEqb  : FVarData
deriving Inhabited

structure HUVData (EExpr : Type) where
a      : LocalDecl
UaEqVb : EExpr
extra  : Option (HUVDataExtra EExpr)
deriving Inhabited



structure AppDataNone (EExpr : Type) where
g    : PExpr
fEqg : EExpr
b    : PExpr
aEqb : EExpr
deriving Inhabited

structure AppDataArg (EExpr : Type) where
b    : PExpr
aEqb : EExpr
deriving Inhabited

structure AppDataFun (EExpr : Type) where
g    : PExpr
fEqg : EExpr
deriving Inhabited

structure AppDataAB (EExpr : Type) where
B    : PExpr
hAB  : EExpr
g    : PExpr
fEqg : EExpr
b    : PExpr
aEqb : EExpr
deriving Inhabited

structure AppDataUV (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr
b    : PExpr
aEqb : EExpr
deriving Inhabited

structure AppDataUVFun (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr
deriving Inhabited

structure AppDataABUV (EExpr : Type) where
B    : PExpr
hAB  : EExpr
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr
b    : PExpr
aEqb : EExpr
deriving Inhabited

inductive AppDataExtra (EExpr : Type) where
| none  : AppDataNone EExpr → AppDataExtra EExpr
| Fun   : AppDataFun EExpr → AppDataExtra EExpr
| Arg   : AppDataArg EExpr → AppDataExtra EExpr
| UV    : AppDataUV EExpr → AppDataExtra EExpr
| UVFun : AppDataUVFun EExpr → AppDataExtra EExpr
| AB    : AppDataAB EExpr → AppDataExtra EExpr
| ABUV  : AppDataABUV EExpr → AppDataExtra EExpr
deriving Inhabited

structure AppData (EExpr : Type) where
u     : Level
v     : Level
A     : PExpr
U     : PExpr × LocalDecl -- TODO make fvar arg optional
f     : PExpr
a     : PExpr
extra : AppDataExtra EExpr
deriving Inhabited



structure TransData (EExpr : Type) where
u     : Level
A     : PExpr
B     : PExpr
C     : PExpr
a     : PExpr
b     : PExpr
c     : PExpr
aEqb  : EExpr
bEqc  : EExpr
deriving Inhabited



structure SymmData (EExpr : Type) where
u     : Level
A     : PExpr
B     : PExpr
a     : PExpr
b     : PExpr
aEqb  : EExpr
deriving Inhabited



structure ReflData where
u     : Level
A     : PExpr
a     : PExpr
deriving Inhabited



structure PIDataHEq (EExpr : Type) where
Q    : PExpr
hPQ  : EExpr
deriving Inhabited

inductive PIDataExtra (EExpr : Type) where
| none 
| HEq   : PIDataHEq EExpr → PIDataExtra EExpr
deriving Inhabited

structure PIData (EExpr : Type) where
P     : PExpr
p     : PExpr
q     : PExpr
extra : PIDataExtra EExpr := .none
deriving Inhabited



/--
Structured data representing expressions for proofs of equality.
-/
inductive EExpr where
| other    : Expr → EExpr
| lam      : LamData EExpr → EExpr
| forallE  : ForallData EExpr → EExpr
| app      : AppData EExpr → EExpr
| trans    : TransData EExpr → EExpr
| symm     : SymmData EExpr → EExpr
| refl     : ReflData → EExpr
| prfIrrel : PIData EExpr → EExpr
| fvar     : FVarData → EExpr
| sry      : SorryData → EExpr
deriving Inhabited

def PExpr.replaceFVar (e fvar val : PExpr) : PExpr := e.toExpr.replaceFVar fvar val |>.toPExpr

def _root_.Lean.LocalDecl.replaceFVar (fvar val : PExpr) (var : LocalDecl) : LocalDecl :=
  assert! not (var.fvarId == fvar.toExpr.fvarId!)
  var.replaceFVarId fvar.toExpr.fvarId! val

def _root_.Prod.replaceFVarU (fvar val : PExpr) (Uvar : PExpr × LocalDecl) : PExpr × LocalDecl :=
  let (U, var) := Uvar
  (U.replaceFVar fvar val, var.replaceFVar fvar val)
mutual

def HUVData.replaceFVar (fvar val : PExpr) : HUVData EExpr → HUVData EExpr
| {a, UaEqVb, extra} => Id.run $ do
  let extra ← match extra with
    | .some {b, vaEqb} =>
      .some {b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val}
    | .none => .none
  {a := a.replaceFVar fvar val, UaEqVb := UaEqVb.replaceFVar fvar val, extra}

def LamData.replaceFVar (fvar val : PExpr) : LamData EExpr → LamData EExpr
| {u, v, A, U, f, a, g, faEqgx, extra} => Id.run $ do
  let extra ← match extra with
  | .ABUV {B, hAB, b, vaEqb} {V} =>
    .ABUV {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val} {V := (V.replaceFVarU fvar val)}
  | .UV {V} =>
    .UV {V := V.replaceFVarU fvar val}
  | .none =>
    .none
  {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, f := f.replaceFVar fvar val, a := a.replaceFVar fvar val, g := g.replaceFVar fvar val, faEqgx := faEqgx.replaceFVar fvar val, extra}

def ForallData.replaceFVar (fvar val : PExpr) : ForallData EExpr → ForallData EExpr
| {u, v, A, U, V, a, UaEqVx, extra} => Id.run $ do
  Id.run $ do
    let extra := match extra with
    | .AB {B, hAB, b, vaEqb} =>
      .AB {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val}
    | .ABApp {b, vaEqb} =>
      .ABApp {b := b.replaceFVar fvar val, vaEqb := vaEqb.replaceFVar fvar val}
    | .none =>
      .none
    {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, V := V.replaceFVarU fvar val, a := a.replaceFVar fvar val, UaEqVx := UaEqVx.replaceFVar fvar val, extra}

def AppData.replaceFVar (fvar val : PExpr) : AppData EExpr → AppData EExpr
| {u, v, A, U, f, a, extra} => Id.run $ do
  let extra := match extra with
  | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
    .ABUV {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
  | .UV {V, hUV, g, fEqg, b, aEqb} =>
    .UV {V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
  | .UVFun {V, hUV, g, fEqg} =>
    .UVFun {V := V.replaceFVarU fvar val, hUV := hUV.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val}
  | .AB {B, hAB, g, fEqg, b, aEqb} =>
    .AB {B := B.replaceFVar fvar val, hAB := hAB.replaceFVar fvar val, g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
  | .none {g, fEqg, b, aEqb} =>
    .none {g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
  | .Fun {g, fEqg} =>
    .Fun {g := g.replaceFVar fvar val, fEqg := fEqg.replaceFVar fvar val}
  | .Arg {b, aEqb} =>
    .Arg {b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}
  {u, v, A := A.replaceFVar fvar val, U := U.replaceFVarU fvar val, f := f.replaceFVar fvar val, a := a.replaceFVar fvar val, extra}

def TransData.replaceFVar (fvar val : PExpr) : TransData EExpr → TransData EExpr
| {u, A, B, C, a, b, c, aEqb, bEqc} =>
  {u, A := A.replaceFVar fvar val, B := B.replaceFVar fvar val, C := C.replaceFVar fvar val, a := a.replaceFVar fvar val, b := b.replaceFVar fvar val, c := c.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val, bEqc := bEqc.replaceFVar fvar val}

def SymmData.replaceFVar (fvar val : PExpr) : SymmData EExpr → SymmData EExpr
| {u, A, B, a, b, aEqb} =>
  {u, A := A.replaceFVar fvar val, B := B.replaceFVar fvar val, a := a.replaceFVar fvar val, b := b.replaceFVar fvar val, aEqb := aEqb.replaceFVar fvar val}

def ReflData.replaceFVar (fvar val : PExpr) : ReflData → ReflData
| {u, A, a} =>
  {u, A := A.replaceFVar fvar val, a := a.replaceFVar fvar val}

def PIData.replaceFVar (fvar val : PExpr) : PIData EExpr → PIData EExpr
| {P, p, q, extra} => Id.run $ do
  let extra := match extra with
  | .none =>
    .none
  | .HEq {Q, hPQ} =>
    .HEq {Q := Q.replaceFVar fvar val, hPQ := hPQ.replaceFVar fvar val}
  {P := P.replaceFVar fvar val, p := p.replaceFVar fvar val, q := q.replaceFVar fvar val, extra}

def FVarData.replaceFVar (fvar val : PExpr) : FVarData → FVarData
| {aEqb, bEqa} => {aEqb := aEqb.replaceFVar fvar val, bEqa := bEqa.replaceFVar fvar val}

def SorryData.replaceFVar (fvar val : PExpr) : SorryData → SorryData
| {u, A, a, B, b} => {u, A := A.replaceFVar fvar val, a := a.replaceFVar fvar val, B := B.replaceFVar fvar val, b := b.replaceFVar fvar val}

def EExpr.replaceFVar (fvar val : PExpr) : EExpr → EExpr
| .other e    => .other $ e.replaceFVar fvar val
| .lam d      => .lam $ d.replaceFVar fvar val
| .forallE d  => .forallE $ d.replaceFVar fvar val
| .app d      => .app $ d.replaceFVar fvar val
| .trans d    => .trans $ d.replaceFVar fvar val
| .symm d     => .symm $ d.replaceFVar fvar val
| .refl d     => .refl $ d.replaceFVar fvar val
| .prfIrrel d => .prfIrrel $ d.replaceFVar fvar val
| .fvar d     => .fvar $ d.replaceFVar fvar val
| .sry d      => .sry $ d.replaceFVar fvar val

end

-- def EExpr.reverse : EExpr → EExpr
-- | other   (e : Expr) => sorry
-- | lam     (d : LamData EExpr) => sorry
-- | forallE (d : ForallData EExpr) => sorry
-- | app     (d : AppData EExpr) => sorry

mutual
def HUVData.toExpr (dep : Bool) : HUVData EExpr → Expr
| {a, UaEqVb, extra} =>
  if dep then match extra with
    | .some {b, vaEqb} => mkLambda #[a, b, vaEqb.aEqb] UaEqVb.toExpr
    | .none => mkLambda #[a] UaEqVb.toExpr
  else
    UaEqVb.toExpr

def LamDataExtra.lemmaName (dep : Bool) (d : LamDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.lambdaHEqABUV
| .UV .. => `L4L.lambdaHEqUV
| .none => `L4L.lambdaHEq
if dep then name.toString ++ "'" |>.toName else name

def LamData.toExpr : LamData EExpr → Expr
| {u, v, A, U, f, a, g, faEqgx, extra} =>
  Id.run $ do
    let hfg := match extra with
    | .ABUV {b, vaEqb, ..} .. =>
        mkLambda #[a, b, vaEqb.aEqb] faEqgx.toExpr
    | .UV ..
    | .none => mkLambda #[a] faEqgx.toExpr

    let (args, dep) := match extra with
    | .ABUV {B, hAB, ..} {V} =>
        let (U, V, dep) := getMaybeDepLemmaApp2 U V
        (#[A, B, U, V, f, g, hAB.toExpr, hfg], dep)
    | .UV {V} => 
        let (U, V, dep) := getMaybeDepLemmaApp2 U V
        (#[A, U, V, f, g, hfg], dep)
    | .none => 
        let (U, dep) := getMaybeDepLemmaApp1 U
        (#[A, U, f, g, hfg], dep)
    let n := extra.lemmaName dep
    Lean.mkAppN (.const n [u, v]) args

def ForallDataExtra.lemmaName (dep : Bool) (d : ForallDataExtra EExpr) : Name :=
let name := match d with
| .AB .. => `L4L.forallHEqAB
| .ABApp .. => `L4L.forallHEq
| .none => `L4L.forallHEq
if dep then name.toString ++ "'" |>.toName else name

def ForallData.toExpr : ForallData EExpr → Expr
| {u, v, A, U, V, a, UaEqVx, extra} =>
  Id.run $ do
    let hUV dep :=
      if dep then match extra with
        | .AB {b, vaEqb, ..} => mkLambda #[a, b, vaEqb.aEqb] UaEqVx.toExpr
        | .ABApp {b, vaEqb} =>
          let fvars := #[b.toExpr, vaEqb.toExpr]
          let vals := #[a.toExpr, Lean.mkAppN (.const `HEq.refl [u]) #[A, a.toExpr]]
          -- TODO optimize resultant term -- will need to call replaceFVars directly on UaEqVx, call a simplify routine and prove termination
          mkLambda #[a] (UaEqVx.toExpr.replaceFVars fvars vals)
        | .none => mkLambda #[a] UaEqVx.toExpr
      else
        UaEqVx.toExpr

    let (U, V, dep) := getMaybeDepLemmaApp2 U V
    let (args, dep) := match extra with
    | .AB {B, hAB, ..} =>
        (#[A, B, U, V, hAB.toExpr, hUV dep], dep)
    | .ABApp _ =>
        (#[A, U, V, hUV dep], dep)
    | .none =>
        (#[A, U, V, hUV dep], dep)

    let n := extra.lemmaName dep
    Lean.mkAppN (.const n [u, v]) args

def AppDataExtra.lemmaName (dep : Bool) (d : AppDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.appHEqABUV
| .UV .. => `L4L.appHEqUV
| .UVFun .. => `L4L.appFunHEqUV
| .AB .. => `L4L.appHEqAB
| .none .. => `L4L.appHEq
| .Arg .. => `L4L.appArgHEq
| .Fun .. => `L4L.appFunHEq
if dep then name.toString ++ "'" |>.toName else name

def AppData.toExpr : AppData EExpr → Expr
| {u, v, A, U, f, a, extra} =>
  let (args, dep) := match extra with
  | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
    let (U, V, dep) := getMaybeDepLemmaApp2 U V
    (#[A, B, U, V, hAB.toExpr, hUV.toExpr dep, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .UV {V, hUV, g, fEqg, b, aEqb} => 
    let (U, V, dep) := getMaybeDepLemmaApp2 U V
    (#[A, U, V, hUV.toExpr dep, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .UVFun {V, hUV, g, fEqg} => 
    let (U, V, dep) := getMaybeDepLemmaApp2 U V
    (#[A, U, V, hUV.toExpr dep, f, g, a, fEqg.toExpr], dep)
  | .AB {B, hAB, g, fEqg, b, aEqb} => 
    let U := U.1
    (#[A, B, U, hAB.toExpr, f, g, a, b, fEqg.toExpr, aEqb.toExpr], false)
  | .none {g, fEqg, b, aEqb} => -- FIXME fails to show termination if doing nested match?
    let (U, dep) := getMaybeDepLemmaApp1 U
    (#[A, U, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .Fun {g, fEqg} =>
    let (U, dep) := getMaybeDepLemmaApp1 U
    (#[A, U, f, g, a, fEqg.toExpr], dep)
  | .Arg {b, aEqb} =>
    let (U, dep) := getMaybeDepLemmaApp1 U
    (#[A, U, f, a, b, aEqb.toExpr], dep)
  let n := extra.lemmaName dep
  Lean.mkAppN (.const n [u, v]) args

def TransData.toExpr : TransData EExpr → Expr
| {u, A, B, C, a, b, c, aEqb, bEqc} =>
  Lean.mkAppN (.const `HEq.trans [u]) #[A, B, C, a, b, c, aEqb.toExpr, bEqc.toExpr]

def SymmData.toExpr : SymmData EExpr → Expr
| {u, A, B, a, b, aEqb} => Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, aEqb.toExpr]

def ReflData.toExpr : ReflData → Expr
| {u, A, a} => Lean.mkAppN (.const `HEq.refl [u]) #[A, a]

def PIData.toExpr : PIData EExpr → Expr
| {P, p, q, extra} =>
  match extra with
  | .none =>
    Lean.mkAppN (.const `L4L.prfIrrel []) #[P, p, q]
  | .HEq {Q, hPQ} =>
    Lean.mkAppN (.const `L4L.prfIrrelHEq []) #[P, Q, hPQ.toExpr, p, q]

def FVarData.toExpr : FVarData → Expr
| {aEqb, ..} => aEqb.toExpr

def SorryData.toExpr : SorryData → Expr
| {u, A, a, B, b} => Lean.mkAppN (.const `sorryAx [0]) #[Lean.mkAppN (.const ``HEq [u]) #[A, a, B, b], .const `Bool.false []]

def EExpr.toExpr : EExpr → Expr
| .other e => e
| .lam d
| .forallE d
| .app d
| .trans d
| .symm d
| .refl d
| .prfIrrel d
| .fvar d
| .sry d  => d.toExpr

end

mutual

abbrev revaEqb aEqb (a b A B : PExpr) u := EExpr.reverse a b A B u aEqb

def FVarData.reverse : FVarData → FVarData
| {aEqb, bEqa} => {aEqb := bEqa, bEqa := aEqb} 

def LamData.reverse : LamData EExpr → EExpr
| {u, v, A, U, f, a, g, faEqgx, extra} =>
  Id.run $ do 
    let (extra, newA, newU, newa) := match extra with
    | .ABUV {b, B, vaEqb, hAB} {V} =>
        (.ABUV {b := a, B := A, vaEqb := vaEqb.reverse, hAB := EExpr.reverse A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB} {V := U}, B, V, b)
    | .UV {V} => (.UV {V := U}, A, V, a)
    | .none => (.none, A, U, a)

    let newfaEqgx := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) faEqgx
    .lam {u, v, A := newA, U := newU, f := g, a := newa, g := f, faEqgx := newfaEqgx, extra}


def HUVData.reverse (Ua Vb : PExpr) (v : Level) : HUVData EExpr → HUVData EExpr
| {a, UaEqVb, extra} =>
  let newUaEqVb := UaEqVb.reverse Ua Vb (Expr.sort v).toPExpr (Expr.sort v).toPExpr v.succ
  match extra with
  | .some {b, vaEqb} => {a := b, UaEqVb := newUaEqVb, extra := .some {b := a, vaEqb := vaEqb.reverse}}
  | .none => {a, UaEqVb := newUaEqVb, extra := .none}

def ForallData.reverse : ForallData EExpr → EExpr
| {u, v, A, U, V, a, UaEqVx, extra} =>
  Id.run $ do 
    let (extra, newA, newa) := match extra with
    | .AB {b, B, hAB, vaEqb} => 
      (.AB {b := a, B := A, hAB := hAB.reverse A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ, vaEqb := vaEqb.reverse}, B, b)
    | .ABApp {b, vaEqb} => 
      (.ABApp {b := a, vaEqb := vaEqb.reverse}, A, b)
    | .none =>
      (.none, A, a)

    let newUaEqVx := UaEqVx.reverse U.1 V.1 (Expr.sort v).toPExpr (Expr.sort v).toPExpr v.succ
    pure $ .forallE {u, v, A := newA, U := V, V := U, a := newa, UaEqVx := newUaEqVx, extra}

def AppData.reverse : AppData EExpr → EExpr
| {u, v, A, U, f, a, extra} =>
  let (extra, newA, newU, newf, newa) := match extra with
  | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
    (.ABUV {B := A, hAB := EExpr.reverse A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB, V := U, hUV := HUVData.reverse (Prod.fst U) (Prod.fst V) v hUV, g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg, b := a, aEqb := EExpr.reverse a b A B u aEqb}, B, V, g, b)
  | .UV {V, hUV, g, fEqg, b, aEqb} => 
    (.UV {V := U, hUV := HUVData.reverse (Prod.fst U) (Prod.fst V) v hUV, g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg, b := a, aEqb := EExpr.reverse a b A A u aEqb}, A, V, g, b)
  | .UVFun {V, hUV, g, fEqg} => 
    (.UVFun {V := U, hUV := HUVData.reverse (Prod.fst U) (Prod.fst V) v hUV, g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[V.2] V.1) (Level.imax u v) fEqg}, A, V, g, a)
  | .AB {B, hAB, g, fEqg, b, aEqb} => 
    (.AB {B := A, hAB := EExpr.reverse A B (Expr.sort u).toPExpr (Expr.sort u).toPExpr u.succ hAB, g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg, b := a, aEqb := EExpr.reverse a b A B u aEqb}, B, U, g, b)
  | .none {g, fEqg, b, aEqb} =>
    (.none {g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg, b := a, aEqb := EExpr.reverse a b A A u aEqb}, A, U, g, b)
  | .Fun {g, fEqg} =>
    (.Fun {g := f, fEqg := EExpr.reverse f g (mkForall #[U.2] U.1) (mkForall #[U.2] U.1) (Level.imax u v) fEqg}, A, U, g, a)
  | .Arg {b, aEqb} =>
    (.Arg {b := a, aEqb := EExpr.reverse a b A A u aEqb}, A, U, f, b)
  .app {u, v, A := newA, U := newU, f := newf, a := newa, extra}

def TransData.reverse : TransData EExpr → EExpr
| {u, A, B, C, a, b, c, aEqb, bEqc} =>
  .trans {u, A := C, B, C := A, a := c, b, c := a, aEqb := bEqc.reverse b c B C u, bEqc := aEqb.reverse a b A B u}

def SymmData.reverse : SymmData EExpr → EExpr
| {aEqb, ..} => aEqb

def ReflData.reverse : ReflData → EExpr := .refl

def PIData.reverse : PIData EExpr → EExpr
| {P, p, q, extra} =>
  let (extra, newP) := match extra with
  | .none => (.none, P)
  | .HEq {Q, hPQ} =>
    (.HEq {Q := P, hPQ := hPQ.reverse P Q (Expr.sort 0).toPExpr (Expr.sort 0).toPExpr 1}, Q)
  .prfIrrel {P := newP, p := q, q := p, extra := extra}

def SorryData.reverse : SorryData → EExpr
| {u, a, A, b, B} =>
  .sry {u, A := B, a := b, B := A, b := a}

def EExpr.reverse (t s tType sType : PExpr) (lvl : Level) : EExpr → EExpr
| .other e => .symm {u := lvl, A := tType, B := sType, a := t, b := s, aEqb := .other e}
| .lam d
| .forallE d
| .app d
| .trans d
| .symm d
| .refl d
| .prfIrrel d
| .sry d  =>
  d.reverse
| .fvar d  => .fvar d.reverse

end

namespace EExpr

def toPExpr (e : EExpr) : PExpr := .mk e.toExpr

instance : BEq EExpr where
beq x y := x.toExpr == y.toExpr

end EExpr

namespace Expr

def _root_.Lean.Expr.toEExpr (e : Expr) : EExpr := EExpr.other e

end Expr

instance : ToString EExpr where
toString e := toString $ e.toExpr

def EExpr.instantiateRev (e : EExpr) (subst : Array EExpr) : EExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExpr

instance : ToString (Option EExpr) where
toString e? := toString $ e?.map (·.toExpr)

instance : Coe EExpr Expr := ⟨(EExpr.toExpr)⟩
instance : Coe EExpr PExpr := ⟨(EExpr.toPExpr)⟩

end Lean4Less
