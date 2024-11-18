import Lean

open Lean

namespace Lean4Less

/--
The type of "patched" expressions.
-/
structure PExpr where
expr : Expr
deriving Inhabited, BEq

/--
The type of "patched" expressions with delta variables.
-/
structure DPExpr where
expr : Expr
deriving Inhabited, BEq

def PExpr.toExpr : PExpr → Expr := PExpr.expr
def DPExpr.toExpr : DPExpr → Expr := DPExpr.expr

def _root_.Lean.Expr.toPExpr (e : Expr) : PExpr := PExpr.mk e
def _root_.Lean.Expr.toDPExpr (e : Expr) : DPExpr := DPExpr.mk e

instance : ToString PExpr where
toString e := toString $ e.toExpr

instance : ToString DPExpr where
toString e := toString $ e.toExpr

instance : ToString (Option PExpr) where
toString e? := toString $ e?.map (·.toExpr)

instance : ToString (Option DPExpr) where
toString e? := toString $ e?.map (·.toExpr)

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩

instance : Hashable DPExpr := ⟨(·.toExpr.hash)⟩
instance : Coe DPExpr Expr := ⟨(DPExpr.toExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExpr

def DPExpr.instantiateRev (e : DPExpr) (subst : Array DPExpr) : DPExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toDPExpr

def PExpr.app (t s : PExpr) := Lean.mkApp t.toExpr s.toExpr |>.toPExpr

def DPExpr.app (t s : DPExpr) := Lean.mkApp t.toExpr s.toExpr |>.toPExpr

end Lean4Less
