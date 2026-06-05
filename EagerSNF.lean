/-
Reproducer: Lean kernel reduction is **not strongly normalizing**.

`Nat.modCore` is defined by well-founded recursion. On *symbolic* arguments the
kernel's lazy `whnf` halts (it stops at the stuck `Decidable.rec`/`dite` that
decides the recursion's guard). But if you reduce *eagerly* — forcing `whnf` at
every subterm position, under binders and into both branches — reduction
diverges: the well-foundedness / accessibility proof, which Lean builds with
`Nat.rec` + the `Nat.below` course-of-values tower (`PProd`/`PUnit`), expands
without bound for a symbolic argument.

This is the well-known `Acc`/`WellFounded.fix` non-termination of the kernel's
reduction. The kernel is safe in practice only because `whnf`/`isDefEq` are lazy
and never force that proof. (Discovered while debugging the lean2dk Lean→Dedukti
translator, whose untyped conversion *does* get forced into that region and so
loops where Lean does not.)

Run with:   lake env lean EagerSNF.lean

Expected:
  - `Nat.modCore 100 7`            terminates (it is `2`), no Nat.rec/PProd blowup.
  - `Nat.modCore (Nat.succ n) m`   DIVERGES: hits the step budget; the visited
                                   nodes are dominated by Nat.rec / PProd / PUnit
                                   (the `Nat.below` well-foundedness proof tower),
                                   with ~0 `Acc.rec` firings.
-/
import Lean4Lean.Methods
import Lean

open Lean Lean.Meta Lean.TypeChecker

def budget : Nat := 1500000

/-- Force `whnf` at every subterm position (head, args, under binders, into all
    branches) — the eager/strong-reduction strategy. No term rebuild, so no
    ill-typed intermediates. Counters live in the kernel `State`:
      numCalls               : total whnf steps (budget-capped by *returning*,
                               so the final State survives for inspection)
      data.maxRecursionDepth : whnf'd nodes headed by `Nat.rec`
      data.numSorries        : whnf'd nodes headed by `PProd` -/
partial def force (e : Expr) : M Unit := do
  modify fun s => { s with numCalls := s.numCalls + 1 }
  if (← get).numCalls > budget then return ()
  let e ← Lean.TypeChecker.whnf e
  match e.getAppFn.constName? with
  | some ``Nat.rec => modify fun s => { s with data := { s.data with maxRecursionDepth := s.data.maxRecursionDepth + 1 } }
  | some ``PProd   => modify fun s => { s with data := { s.data with numSorries := s.data.numSorries + 1 } }
  | _ => pure ()
  match e with
  | .app .. =>
    force e.getAppFn
    e.getAppArgs.forM force
  | .lam nm d bd bi =>
    force d
    let id : FVarId := ⟨← mkNewId⟩
    withReader (fun (c : Lean.TypeChecker.Context) => { c with lctx := c.lctx.mkLocalDecl id nm d bi }) do
      force (bd.instantiate1 (.fvar id))
  | .forallE nm d bd bi =>
    force d
    let id : FVarId := ⟨← mkNewId⟩
    withReader (fun (c : Lean.TypeChecker.Context) => { c with lctx := c.lctx.mkLocalDecl id nm d bi }) do
      force (bd.instantiate1 (.fvar id))
  | .letE _ t v b _ => force t; force v; force b
  | .proj _ _ s => force s
  | .mdata _ e => force e
  | _ => pure ()

def runForce (env : Environment) (lctx : LocalContext) (e : Expr) (label : String) : IO Unit := do
  IO.println s!">>> eager-reduce {label} ..."
  match TypeChecker.M.run env.toKernelEnv (lctx := lctx) (safety := .safe) (force e) with
  | .ok (_, st) =>
    let status := if st.numCalls > budget then "DIVERGES (budget hit)" else "terminated"
    IO.println s!"    {status}: {st.numCalls} whnf steps  (Nat.rec={st.data.maxRecursionDepth}, PProd={st.data.numSorries})"
  | .error _ => IO.println s!"    halted with a kernel exception (did NOT loop)"

def natTy : Expr := .const ``Nat []
def succ (e : Expr) : Expr := .app (.const ``Nat.succ []) e

#eval show MetaM Unit from do
  let env ← getEnv
  runForce env {} (mkApp2 (.const ``Nat.modCore []) (mkNatLit 100) (mkNatLit 7)) "Nat.modCore 100 7  [literal]"
  withLocalDeclD `n natTy fun n => withLocalDeclD `m natTy fun m => do
    let lctx ← getLCtx
    runForce env lctx (mkApp2 (.const ``Nat.modCore []) (succ n) m) "Nat.modCore (Nat.succ n) m  [symbolic]"
