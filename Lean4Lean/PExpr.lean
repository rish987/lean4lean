import Lean

namespace Lean

/--
TODO update docs, I'm now using this for patched expressions
The type of "patchable" expressions, i.e. "original expressions" coming from
from the input constants' types/values that can be patched by the typechecker.

A patchable expression should never be a return type of any typechecking routine.

NOTE: while a coercion allows expressions to be used in place of patchable expressions,
the opposite is not true, enforcing that functions that throw away the patched results
of patching calls (e.g. to `inferType` and friends) are not called with expressions
that we expect to be patched.

Calling such functions within the course of normal typechecking should throw an error,
which suggests one of two things:
1. This usage of the function should be considered auxilliary to normal typechecking
(e.g. when printing a debug message), which should be made explicit by
converting `e : PExpr` with `e.toExpr` or by using a `NoPatch`-suffixed variant
of the original function taking `PExpr` instead of `Expr` (preferred).
2. If this call is part of typechecking, the function should be modified to expect
`PExpr` and return `T × Option Expr` (this is less likely to be the case).
-/
inductive PExpr where
  | bvar (deBruijnIndex : Nat)
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | sort (u : Level)
  | const (declName : Name) (us : List Level)
  | app (fn : PExpr) (arg : PExpr)
  | lam (binderName : Name) (binderType : PExpr) (body : PExpr) (binderInfo : BinderInfo)
  | forallE (binderName : Name) (binderType : PExpr) (body : PExpr) (binderInfo : BinderInfo)
  | letE (declName : Name) (type : PExpr) (value : PExpr) (body : PExpr) (nonDep : Bool)
  | lit : Literal → PExpr
  | mdata (data : MData) (expr : PExpr)
  | proj (typeName : Name) (idx : Nat) (struct : PExpr)
deriving BEq, Inhabited, Repr

def PExpr.toExpr : PExpr → Expr
| .bvar i => .bvar i
| .fvar id => .fvar id
| .mvar id => .mvar id
| .sort u => .sort u
| .const n us => .const n us
| .app fn arg => .app fn.toExpr arg.toExpr
| .lam n typ bod bin => .lam n typ.toExpr bod.toExpr bin
| .forallE n typ bod bin => .forallE n typ.toExpr bod.toExpr bin
| .letE n typ val bod bin => .letE n typ.toExpr val.toExpr bod.toExpr bin
| .lit l => .lit l
| .mdata dat e => .mdata dat e.toExpr
| .proj typ idx str => .proj typ idx str.toExpr

def Expr.toPExpr : Expr → PExpr
| .bvar i => .bvar i
| .fvar id => .fvar id
| .mvar id => .mvar id
| .sort u => .sort u
| .const n us => .const n us
| .app fn arg => .app fn.toPExpr arg.toPExpr
| .lam n typ bod bin => .lam n typ.toPExpr bod.toPExpr bin
| .forallE n typ bod bin => .forallE n typ.toPExpr bod.toPExpr bin
| .letE n typ val bod bin => .letE n typ.toPExpr val.toPExpr bod.toPExpr bin
| .lit l => .lit l
| .mdata dat e => .mdata dat e.toPExpr
| .proj typ idx str => .proj typ idx str.toPExpr

instance : Hashable PExpr := ⟨(·.toExpr.hash)⟩
instance : Coe PExpr Expr := ⟨(PExpr.toExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array Expr) : PExpr :=
    e.toExpr.instantiateRev subst |>.toPExpr

inductive LocalDecl' (T : Type) (F : T → Expr) where
  | cdecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : T) (bi : BinderInfo) (kind : LocalDeclKind)
  | ldecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : T) (value : T) (nonDep : Bool) (kind : LocalDeclKind)
  deriving Inhabited

def LocalDecl'.toLocalDecl : LocalDecl' T F → LocalDecl
  | cdecl i f u t b k => .cdecl i f u (F t) b k
  | ldecl i f u t v n k => .ldecl i f u (F t) (F v) n k

def LocalDecl.toLocalDecl' (G : Expr → T) : LocalDecl → LocalDecl' T F
  | cdecl i f u t b k => .cdecl i f u (G t) b k
  | ldecl i f u t v n k => .ldecl i f u (G t) (G v) n k

abbrev PLocalDecl := LocalDecl' PExpr (PExpr.toExpr)

instance : Coe PLocalDecl LocalDecl := ⟨(LocalDecl'.toLocalDecl)⟩
instance : Coe LocalDecl PLocalDecl := ⟨(LocalDecl.toLocalDecl' (Expr.toPExpr))⟩

structure LocalContext' (T : Type) (F : T → Expr) where
  fvarIdToDecl : PersistentHashMap FVarId (LocalDecl' T F) := {}
  decls        : PersistentArray (Option (LocalDecl' T F)) := {}
  deriving Inhabited

def LocalContext'.toLocalContext : LocalContext' T F → LocalContext
  | mk ftd d => .mk (ftd.map fun decl => decl.toLocalDecl) (d.map (·.map (·.toLocalDecl)))

def LocalContext.toLocalContext' (G : Expr → T) : LocalContext → LocalContext' T F
  | mk ftd d => .mk (ftd.map fun decl => decl.toLocalDecl' G) (d.map (·.map (·.toLocalDecl' G)))

abbrev PLocalContext := LocalContext' PExpr (PExpr.toExpr)

instance : Coe (PLocalContext) LocalContext := ⟨(LocalContext'.toLocalContext)⟩
instance : Coe (LocalContext) PLocalContext := ⟨(LocalContext.toLocalContext' (Expr.toPExpr))⟩

/-- Class used to denote that `m` has a local context. -/
class MonadPLCtx (m : Type → Type) where
  getLCtx : m PLocalContext

export MonadPLCtx (getLCtx)

instance [MonadLift m n] [MonadPLCtx m] : MonadPLCtx n where
  getLCtx := liftM (getLCtx : m _)

end Lean
