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
    usedFVarEqs := p1.usedFVarEqs.mergeBy (fun _ b _ => b) p2.usedFVarEqs,
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
def toPExpr (e : EExpr) : PExpr := assert! e.data.isEmpty
  .mk e.expr

end EExpr

namespace Expr

def toEExpr (data : EExprData) (e : Expr) : EExpr := EExpr.mk e data 

def toEExprMerge (e : Expr) (p : EExpr) (p' : EExpr) : EExpr := e.toEExpr (p.mergeData p')
def toEExprMergeN (e : Expr) (p : EExpr) (ps : Array EExpr) : EExpr := e.toEExpr (p.mergeDataN ps)
def toEExprD (e : Expr) : EExpr := EExpr.mk e default

end Expr

def PExpr.instantiateRev (e : PExpr) (subst : Array PExpr) : PExpr :=
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toPExpr

def EExpr.instantiateRev (e : EExpr) (subst : Array EExpr) : EExpr :=
  -- FIXME only merge data from the substitutions that actually occurred
  e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExprMergeN e subst

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩
instance : Coe EExpr Expr := ⟨(EExpr.toExpr)⟩

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

def PLocalDecl.toLocalDecl : PLocalDecl → LocalDecl
  | cdecl i f u t b k => .cdecl i f u (t) b k
  | ldecl i f u t v n k => .ldecl i f u t v n k

def PLocalContext.toLocalContext : PLocalContext → LocalContext
  | mk ftd d => .mk (ftd.map fun decl => decl.toLocalDecl) (d.map (·.map (·.toLocalDecl)))

def PLocalContext.find? (lctx : PLocalContext) (fvarId : FVarId) : Option PLocalDecl :=
  lctx.fvarIdToDecl.find? fvarId

def PLocalContext.mkLocalDecl (lctx : PLocalContext) (fvarId : FVarId) (userName : Name) (type : PExpr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : PLocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := PLocalDecl.cdecl idx fvarId userName type bi kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

/-- Low level API for let declarations. Do not use directly.-/
def PLocalContext.mkLetDecl (lctx : PLocalContext) (fvarId : FVarId) (userName : Name) (type : PExpr) (value : PExpr) (nonDep := false) (kind : LocalDeclKind := default) : PLocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := PLocalDecl.ldecl idx fvarId userName type value nonDep kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

/-- Class used to denote that `m` has a local context. -/
class MonadPLCtx (m : Type → Type) where
  getLCtx : m PLocalContext

export MonadPLCtx (getLCtx)

instance [MonadLift m n] [MonadPLCtx m] : MonadPLCtx n where
  getLCtx := liftM (getLCtx : m _)

end Lean
