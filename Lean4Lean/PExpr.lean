import Lean

namespace Lean
/--
The type of "patched" expressions.
-/
structure PExpr where
expr : Expr
deriving BEq, Inhabited, Repr

def PExpr.toExpr : PExpr → Expr := PExpr.expr
def Expr.toPExpr : Expr → PExpr := PExpr.mk

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
    e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExpr
end Lean
