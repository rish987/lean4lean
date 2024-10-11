import Lean

open Lean

namespace Lean4Less

/--
The type of "patched" expressions.
-/
structure PExpr where
expr : Expr
deriving Inhabited, BEq

namespace PExpr

def toExpr : PExpr → Expr := PExpr.expr

end PExpr

def _root_.Lean.Expr.toPExpr (e : Expr) : PExpr := PExpr.mk e

instance : ToString PExpr where
toString e := toString $ e.toExpr

instance : ToString (Option PExpr) where
toString e? := toString $ e?.map (·.toExpr)

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExpr

def PExpr.app (t s : PExpr) := Lean.mkApp t.toExpr s.toExpr |>.toPExpr

end Lean4Less
