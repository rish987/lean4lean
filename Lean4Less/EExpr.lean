import Lean
import Lean4Less.PExpr

open Lean

namespace Lean4Less

def getMaybeDepLemmaApp (Uas as : Array PExpr) (lctx : LocalContext) : Array PExpr × Bool :=
  let dep := Uas.zip as |>.foldl (init := false) fun acc (Ua, a) =>
    Ua.toExpr.containsFVar a.toExpr.fvarId! || acc
  let ret := Uas.zip as |>.map fun (Ua, a) =>
    if dep then
      lctx.mkLambda #[a] Ua |>.toPExpr
    else
      Ua
  (ret, dep)

def getMaybeDepLemmaApp1 (U : PExpr × PExpr) (lctx : LocalContext) : (PExpr × Bool) :=
  let (Ua, a) := U
  match getMaybeDepLemmaApp #[Ua] #[a] lctx with
  | (#[U], dep) => (U, dep)
  | _ => unreachable!

def getMaybeDepLemmaApp2 (U V : (PExpr × PExpr)) (lctx : LocalContext) : (PExpr × PExpr × Bool) :=
  let (Ua, a) := U
  let (Vb, b) := V
  match getMaybeDepLemmaApp #[Ua, Vb] #[a, b] lctx with
  | (#[U, V], dep) => (U, V, dep)
  | _ => unreachable!

structure LamABData (EExpr : Type) :=
B      : PExpr
b      : PExpr
idaEqb : FVarId
hAB : EExpr

structure LamUVData :=
V   : PExpr × PExpr

inductive LamDataExtra (EExpr : Type) :=
| ABUV : LamABData EExpr → LamUVData → LamDataExtra EExpr
| UV   : LamUVData → LamDataExtra EExpr
| none : LamDataExtra EExpr
deriving Inhabited

structure LamData (EExpr : Type) :=
u      : Level
v      : Level
A      : PExpr
U      : PExpr × PExpr
f      : PExpr
a      : PExpr
g      : PExpr
faEqgx : EExpr
extra  : LamDataExtra EExpr
lctx   : LocalContext
deriving Inhabited



structure ForallABData (EExpr : Type) :=
B      : PExpr
b      : PExpr
idaEqb : FVarId
hAB    : EExpr

inductive ForallDataExtra (EExpr : Type) :=
| AB   : ForallABData EExpr → ForallDataExtra EExpr
| none : ForallDataExtra EExpr
deriving Inhabited

structure ForallData (EExpr : Type) :=
u      : Level
v      : Level
A      : PExpr
a      : PExpr
U      : PExpr × PExpr
V      : PExpr × PExpr
UaEqVx : EExpr
extra  : ForallDataExtra EExpr
lctx   : LocalContext
deriving Inhabited


-- FIXME many of the PExprs below should be EExprs
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
V     : PExpr × PExpr
hUV   : PExpr
g    : PExpr
fEqg : EExpr
b    : PExpr
aEqb : EExpr
deriving Inhabited

structure AppDataUVFun (EExpr : Type) where
V     : PExpr × PExpr
hUV   : PExpr
g    : PExpr
fEqg : EExpr
deriving Inhabited

structure AppDataABUV (EExpr : Type) where
B    : PExpr
hAB  : EExpr
V    : PExpr × PExpr
hUV  : PExpr
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
U     : PExpr × PExpr
f     : PExpr
a     : PExpr
extra : AppDataExtra EExpr
lctx  : LocalContext
deriving Inhabited



/--
The type of expressions for proofs of equality.
-/
inductive EExpr where
| other   : Expr → EExpr
| lam     : LamData EExpr → EExpr
| forallE : ForallData EExpr → EExpr
| app     : AppData EExpr → EExpr
deriving Inhabited

mutual
def LamDataExtra.lemmaName (dep : Bool) (d : LamDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.lambdaHEqABUV
| .UV .. => `L4L.lambdaHEqUV
| .none => `L4L.lambdaHEq
if dep then name.toString ++ "'" |>.toName else name

def LamData.toExpr : LamData EExpr → Expr
| {u, v, A, U, f, a, g, faEqgx, extra, lctx} =>
  let hfg := match extra with
  | .ABUV {b, idaEqb, ..} .. =>
      lctx.mkLambda #[a, b, .fvar idaEqb] faEqgx.toExpr |>.toPExpr
  | .UV ..
  | .none => lctx.mkLambda #[a] faEqgx.toExpr |>.toPExpr

  let (args, dep) := match extra with
  | .ABUV {B, hAB, ..} {V} =>
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, B, U, V, f, g, hAB.toExpr, hfg], dep)
  | .UV {V} => 
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, U, V, f, g, hfg], dep)
  | .none => 
      let (U, dep) := getMaybeDepLemmaApp1 U lctx
      (#[A, U, f, g, hfg], dep)
  let n := extra.lemmaName dep
  Lean.mkAppN (.const n [u, v]) args

def ForallDataExtra.lemmaName (dep : Bool) (d : ForallDataExtra EExpr) : Name :=
let name := match d with
| .AB .. => `L4L.forallHEqAB
| .none => `L4L.forallHEq
if dep then name.toString ++ "'" |>.toName else name

def ForallData.toExpr : ForallData EExpr → Expr
| {u, v, A, U, V, a, UaEqVx, extra, lctx} =>

  let hUV dep :=
    if dep then match extra with
      | .AB {b, idaEqb, ..} => lctx.mkLambda #[a, b, .fvar idaEqb] UaEqVx.toExpr |>.toPExpr
      | .none => lctx.mkLambda #[a] UaEqVx.toExpr |>.toPExpr
    else
      UaEqVx.toExpr

  let (args, dep) := match extra with
  | .AB {B, hAB, ..} => 
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, B, U, V, hAB.toExpr, hUV dep], dep)
  | .none =>
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
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
| {u, v, A, U, f, a, extra, lctx} =>
  let (args, dep) := match extra with
  | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb} =>
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, B, U, V, hAB.toExpr, hUV.toExpr, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .UV {V, hUV, g, fEqg, b, aEqb} => 
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, U, V, hUV, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .UVFun {V, hUV, g, fEqg} => 
      let (U, V, dep) := getMaybeDepLemmaApp2 U V lctx
      (#[A, U, V, hUV.toExpr, f, g, a, fEqg.toExpr], dep)
  | .AB {B, hAB, g, fEqg, b, aEqb} => 
      let U := U.1
      (#[A, B, U, hAB.toExpr, f, g, a, b, fEqg.toExpr, aEqb.toExpr], false)
  | .none {g, fEqg, b, aEqb} => -- FIXME fails to show termination if doing nested match?
    let (U, dep) := getMaybeDepLemmaApp1 U lctx
    (#[A, U, f, g, a, b, fEqg.toExpr, aEqb.toExpr], dep)
  | .Fun {g, fEqg} =>
    let (U, dep) := getMaybeDepLemmaApp1 U lctx
    (#[A, U, f, g, a, fEqg.toExpr], dep)
  | .Arg {b, aEqb} =>
    let (U, dep) := getMaybeDepLemmaApp1 U lctx
    (#[A, U, f, a, b, aEqb.toExpr], dep)
let n := extra.lemmaName dep
Lean.mkAppN (.const n [u, v]) args

def EExpr.toExpr : EExpr → Expr
| .other e => e
| .lam d
| .forallE d
| .app d  => d.toExpr
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
