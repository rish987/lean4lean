import Lean
import Lean4Less.PExpr

open Lean

namespace Lean4Less

structure LamABData (EExpr : Type) :=
B   : PExpr
b   : PExpr
hAB : EExpr

structure LamUVData :=
V   : PExpr

inductive LamDataExtra (EExpr : Type) :=
| ABUV : LamABData EExpr → LamUVData → LamDataExtra EExpr
| UV   : LamUVData → LamDataExtra EExpr
| none : LamDataExtra EExpr
deriving Inhabited

structure LamData (EExpr : Type) :=
u      : Level
v      : Level
A      : PExpr
U      : PExpr
f      : PExpr
a      : PExpr
g      : PExpr
faEqgx : EExpr
extra  : LamDataExtra EExpr
dep    : Bool
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
U      : PExpr
V      : PExpr
UaEqVx : EExpr
extra  : ForallDataExtra EExpr
dep    : Bool
lctx   : LocalContext
deriving Inhabited



structure AppDataFun (EExpr : Type) where
g      : PExpr
faEqgx : EExpr

structure AppDataArg (EExpr : Type) where
b    : PExpr
aEqb : EExpr

structure AppDataNone (EExpr : Type) where
fund? : (Option (AppDataFun EExpr))
argd? : (Option (AppDataArg EExpr))
deriving Inhabited

structure AppDataAB (EExpr : Type) where
B   : PExpr
hAB : EExpr
deriving Inhabited

structure AppDataUV (EExpr : Type) where
b : PExpr
Vb : PExpr
hUV : PExpr
argd? : (Option (AppDataArg EExpr))
deriving Inhabited

inductive AppDataExtra (EExpr : Type) where
| none : AppDataExtra EExpr
| UV : AppDataUV EExpr → AppDataExtra EExpr
| AB : AppDataAB EExpr → AppDataExtra EExpr
| ABUV : AppDataAB EExpr → AppDataUV EExpr → AppDataExtra EExpr
deriving Inhabited

structure AppData (EExpr : Type) where
u  : Level
v  : Level
A  : PExpr
U  : PExpr
f : PExpr
a : PExpr
g : PExpr
b : PExpr
extra : AppDataExtra EExpr
dep   : Bool
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

namespace EExpr

def toExpr : EExpr → Expr := sorry
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
