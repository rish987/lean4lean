import Lean

namespace Lean
structure PExprData where
usedFVarEqs : NameSet := default
usedProofIrrel : Bool := false
deriving Inhabited

def PExprData.merge (p1 p2 : PExprData) : PExprData := 
  {p1 with
    usedFVarEqs := p1.usedFVarEqs.mergeBy (fun _ b _ => b) p2.usedFVarEqs,
    usedProofIrrel := p1.usedProofIrrel || p2.usedProofIrrel}

def PExprData.mergeN (ps : Array PExprData) : PExprData := ps.foldl (init := default) fun acc p => acc.merge p

/--
The type of "patched" expressions.
-/
structure PExpr where
expr : Expr
data : PExprData
deriving Inhabited

instance : BEq PExpr where
beq x y := x.expr == y.expr

def PExpr.mergeData (p1 p2 : PExpr) : PExprData := 
  p1.data.merge p2.data

def PExpr.mergeDataN (p : PExpr) (ps : Array PExpr) : PExprData := p.data.merge $ PExprData.mergeN (ps.map (·.data))

def PExpr.toExpr : PExpr → Expr := PExpr.expr
def Expr.toPExpr (data : PExprData) (e : Expr) : PExpr := PExpr.mk e data 

def Expr.toPExprMerge (e : Expr) (p : PExpr) (p' : PExpr) : PExpr := e.toPExpr (p.mergeData p')
def Expr.toPExprMergeN (e : Expr) (p : PExpr) (ps : Array PExpr) : PExpr := e.toPExpr (p.mergeDataN ps)
def Expr.toPExprD (e : Expr) : PExpr := PExpr.mk e default

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
  -- FIXME only merge data from the substitutions that actually occurred
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExprMergeN e subst

inductive PLocalDecl where
  | cdecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : PExpr) (bi : BinderInfo) (kind : LocalDeclKind)
  | ldecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : PExpr) (value : PExpr) (nonDep : Bool) (kind : LocalDeclKind)
  deriving Inhabited

def PLocalDecl.type : PLocalDecl → PExpr
  | cdecl (type := t) .. => t
  | ldecl (type := t) .. => t

structure PLocalContext where
  fvarIdToDecl : PersistentHashMap FVarId PLocalDecl := {}
  decls        : PersistentArray (Option PLocalDecl) := {}
  deriving Inhabited

def PLocalContext.find? (lctx : PLocalContext) (fvarId : FVarId) : Option PLocalDecl :=
  lctx.fvarIdToDecl.find? fvarId

def PLocalContext.mkLocalDecl (lctx : PLocalContext) (fvarId : FVarId) (userName : Name) (type : PExpr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : PLocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := PLocalDecl.cdecl idx fvarId userName type bi kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

/-- Class used to denote that `m` has a local context. -/
class MonadPLCtx (m : Type → Type) where
  getLCtx : m PLocalContext

export MonadPLCtx (getLCtx)

instance [MonadLift m n] [MonadPLCtx m] : MonadPLCtx n where
  getLCtx := liftM (getLCtx : m _)

end Lean
