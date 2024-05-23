import Lean

namespace Lean

/--
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
instance : Coe Expr PExpr := ⟨(Expr.toPExpr)⟩

def PExpr.instantiateRev (e : PExpr) (subst : Array Expr) : PExpr :=
    e.toExpr.instantiateRev subst |>.toPExpr

end Lean
