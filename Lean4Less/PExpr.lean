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
Tracks which equality proofs were used to construct an `EExpr`.
-/
structure EExprData where
usedFVarEqs : NameSet := default
usedProofIrrel : Bool := false
deriving Inhabited

def EExprData.merge (p1 p2 : EExprData) : EExprData := 
  {p1 with
    usedFVarEqs := p1.usedFVarEqs.union p2.usedFVarEqs,
    usedProofIrrel := p1.usedProofIrrel || p2.usedProofIrrel}

def EExprData.mergeN (ps : Array EExprData) : EExprData := ps.foldl (init := default) fun acc p => acc.merge p

def EExprData.isEmpty (data : EExprData) : Bool := data.usedProofIrrel == false && data.usedFVarEqs.isEmpty

/--
The type of expressions for proofs of equality.
-/
structure EExpr where
expr : Expr
data : EExprData
deriving Inhabited

instance : BEq EExpr where
beq x y := x.expr == y.expr

namespace EExpr

def mergeData (p1 p2 : EExpr) : EExprData := 
  p1.data.merge p2.data

def mergeDataN (p : EExpr) (ps : Array EExpr) : EExprData := p.data.merge $ EExprData.mergeN (ps.map (·.data))

def toExpr : EExpr → Expr := EExpr.expr
def toPExpr (e : EExpr) : PExpr := -- assert! e.data.usedFVarEqs.isEmpty -- FIXME put back
  .mk e.expr

end EExpr

namespace Expr

def toEExpr (data : EExprData) (e : Expr) : EExpr := EExpr.mk e data 

def toEExprMerge (e : Expr) (p : EExpr) (p' : EExpr) : EExpr := e.toEExpr (p.mergeData p')
def toEExprMergeN (e : Expr) (p : EExpr) (ps : Array EExpr) : EExpr := e.toEExpr (p.mergeDataN ps)
def toEExprD (e : Expr) : EExpr := EExpr.mk e default

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
  -- FIXME only merge data from the substitutions that actually occurred
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExprMergeN e subst

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩
instance : Coe EExpr Expr := ⟨(EExpr.toExpr)⟩

end Lean
