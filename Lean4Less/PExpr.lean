import Lean

namespace Lean

/--
The type of "patched" expressions.
-/
structure PExpr where
expr : Expr
deriving Inhabited, BEq

namespace PExpr

def toExpr : PExpr → Expr := PExpr.expr

end PExpr

def Expr.toPExpr (e : Expr) : PExpr := PExpr.mk e

/--
The type of expressions for proofs of equality.
-/
structure EExpr where
expr : Expr
deriving Inhabited

instance : BEq EExpr where
beq x y := x.expr == y.expr

namespace EExpr

def toExpr : EExpr → Expr := EExpr.expr
def toPExpr (e : EExpr) : PExpr := .mk e.expr

end EExpr

namespace Expr

def toEExpr (e : Expr) : EExpr := EExpr.mk e

end Expr

instance : ToString PExpr where
toString e := toString $ e.toExpr

instance : ToString EExpr where
toString e := toString $ e.toExpr

instance : ToString (Option PExpr) where
toString e? := toString $ e?.map (·.toExpr)

instance : ToString (Option EExpr) where
toString e? := toString $ e?.map (·.toExpr)


def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExpr

def EExpr.instantiateRev (e : EExpr) (subst : Array EExpr) : EExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExpr

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩
instance : Coe EExpr Expr := ⟨(EExpr.toExpr)⟩

end Lean
