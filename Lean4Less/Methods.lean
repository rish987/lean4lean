import Lean4Less.TypeChecker

namespace Lean4Less.TypeChecker

open Inner
open Lean

def defFuel := 1300

mutual
def fuelWrap (idx : Nat) (fuel : Nat) (d : CallData) : M (CallDataT d) := do
let ctx := (← readThe Context)
match fuel with

  | 0 =>
    dbg_trace s!"deep recursion callstack: {ctx.callStack.map (·.1)}"
    throw .deepRecursion
  | fuel' + 1 =>
    -- let recDepth := (defFuel - fuel)
    let m : RecM (CallDataT d):=
      match d with
      | .isDefEqCore t s => isDefEqCore' t s
      | .isDefEqCorePure t s => isDefEqCorePure' t s
      | .quickIsDefEq t s b => quickIsDefEq' t s b
      | .whnfCore e k p => whnfCore' e k p
      | .whnf e k => whnf' e k
      | .whnfPure e => whnfPure' e
      | .inferType e d => inferType' e d
      | .inferTypePure e => inferTypePure' e
    -- if recDepth > 500 then
    --   dbg_trace s!"DBG[3]: {d.name}, {fuel}, {idx}"
    modify fun s => {s with numCalls := s.numCalls + 1} 
    let s ← get
    -- let newFuel := 
    --   match d with
    --   | .quickIsDefEq t s b => fuel'
    --   | _ => fuel'
    --   

    let mut printedTrace := false
    let methPrint := false
    -- let methPrint := true
    if methPrint && ctx.callId == 532 /- && not s.printedDbg -/ then -- TODO static variables?
      if s.numCalls % 1 == 0 then
        printedTrace := true
        dbg_trace s!"calltrace {s.numCalls}: {ctx.callStack.map (·.1)}, {idx}, {ctx.callId}"

    -- if s.numCalls == 39363 then
    --   dbg_trace s!"DBG[21]: Methods.lean:46 (after if s.numCalls == 39363 then)"

    -- let meth := Methods.withFuel fuel'
    -- if s.isDefEqCache.size > 300 then
    --   modify fun s => {s with isDefEqCache := Std.HashMap.empty (capacity := 1000)} 

    --
    --   -- pure ()
    --
    --   match x with
    --     | .isDefEqCore t s .. =>
    --       -- dbg_trace s!"{t}\n\n{s}"
    --       let whnfCorePure x := runLeanRecM (Lean.TypeChecker.Inner.whnfCore x) meth
    --       let isDefEqCorePure x y := runLeanRecM (Lean.TypeChecker.Inner.isDefEqCore x y) meth
    --       -- dbg_trace s!"DBG[2]: Methods.lean:54 {t}, {s}"
    --       dbg_trace s!"DBG[3]: Methods.lean:55 (after dbg_trace s!DBG[2]: Methods.lean:54 t, s)"
    --       _ ← isDefEq 0 t s meth
    --       dbg_trace s!"DBG[1]: Methods.lean:55: res"
    --       -- let res ← runLeanRecM (Lean.TypeChecker.Inner.isDefEqCore t s) meth
    --       -- match res with
    --       -- | .unknown tn' sn' =>
    --       --   -- let w ← whnfCorePure tn'
    --       --   let x ← match tn' with
    --       --   | .proj _ i s => 
    --       --     let s ← runLeanRecM (Lean.TypeChecker.Inner.reduceProj i s false false) meth
    --       --     -- let s ← runLeanMinusRecM (Lean.TypeChecker.Inner.inferType s.getAppArgs[5]! true) meth
    --       --     -- let s ← runLeanMinusRecM (Lean.TypeChecker.Inner.whnfCore s.get!) meth
    --       --     pure s
    --       --   | _ => unreachable!
    --       --   dbg_trace s!"DBG[1]: {← isDefEqCorePure (← whnfCorePure tn').toPExpr sn'.toPExpr} {sn'}"
    --       -- | _ => unreachable! 
    --     | _ => unreachable!
    --
      -- let t ← match stack[10]!.2 with
      --   | .whnf t k =>
      --     -- dbg_trace s!"DBG[1]: TypeChecker.lean:1708 (after | .whnf t .. =>)"
      --     -- let t1 ← whnfPure 0 t (Methods.withFuel fuel')
      --     -- let t2 ← reduceRecursor t1 false (Methods.withFuel fuel')
      --     -- let t3 ← whnfPure 0 t2.get!.1 (Methods.withFuel fuel')
      --     -- dbg_trace s!"HERE: {k}, {t3}"
      --     -- let t' ← whnf 0 t1 false (Methods.withFuel fuel')
      --     -- dbg_trace s!"DBG[2]: TypeChecker.lean:1710 (after dbg_trace s!HERE: ← reduceRecursor ("
      --     pure t
      --   | _ => unreachable!
      -- dbg_trace s!"{s.numCalls}: {stack[9]!.2}, {stack.map (·.1)}"

    let traceId : Option Nat := none
    -- let traceId := Option.some 532
    try
      let ret ← withCallId s.numCalls traceId do
        withCallData idx s.numCalls d do 
          -- if let some id := traceId then
          --   if s.numCalls == id then
          --     let stack := (← readThe Context).callStack
          --     if idx == 110 then
          --       dbg_trace s!"\n{stack[stack.size - 4]!}"
          --       dbg_trace s!"{s.numCalls}: {stack.map (·.1)}"

          m (Methods.withFuel fuel')
      if printedTrace then
        dbg_trace s!"end of    {s.numCalls}: {(← readThe Context).callStack.map (·.1)}, {idx}, {(← readThe Context).callId}"
      -- if s.numCalls == 39363 then
      --   dbg_trace s!"DBG[22]: Methods.lean:110 (after dbg_trace s!DBG[21]: Methods.lean:46 (af…)"
      pure ret
    catch e =>
      -- if s.numCalls == 7229 then
      --   let stack := (← readThe Context).callStack--.map (·.2.2)
      --   let d := stack[stack.size - 2]!
      --   match d.2.2 with
      --   | .isDefEqCore t s .. => 
      --     let ret ← isDefEqLean t s 1000 (Methods.withFuel fuel')
      --     dbg_trace s!"DBG[11]: Methods.lean:119: ret={ret}"
      --     pure ()
      --   | _ => unreachable!
        -- isDefEqLean 
      dbg_trace s!"err calltrace {s.numCalls}: {(← readThe Context).callStack.map (·.1)}, {idx}"
      throw e

def Methods.withFuel (n : Nat) : Methods := 
  { isDefEqCore := fun i t s => do
      fuelWrap i n $ .isDefEqCore t s
    isDefEqCorePure := fun i t s => do
      fuelWrap i n $ .isDefEqCorePure t s
    quickIsDefEq := fun i t s b => do
      fuelWrap i n $ .quickIsDefEq t s b
    whnfCore := fun i e k p => do
      fuelWrap i n $ .whnfCore e k p
    whnf := fun i e k => do
      fuelWrap i n $ .whnf e k
    whnfPure := fun i e => do
      fuelWrap i n $ .whnfPure e
    inferType := fun i e d => do
      fuelWrap i n $ .inferType e d
    inferTypePure := fun i e => do
      fuelWrap i n $ .inferTypePure e
  }
end

/--
Runs `x` with a limit on the recursion depth.
-/
def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

/--
With the level context `lps`, infers the type of expression `e` and checks that
`e` is well-typed according to Lean's typing judgment.

Use `inferType` to infer type alone.
-/
def check (e : Expr) (lps : List Name) : MPE := do
  let ret ← withReader ({ · with lparams := lps }) (inferType 82 e).run
  -- let (_, e'?) := ret

  -- if let some e' := e'? then
  --   for c in e'.toExpr.getUsedConstants do
  --     if not ((← getEnv).find? c).isSome then
  --       throw $ .other s!"possible patching loop detected ({c})"

  pure ret

def checkPure (e : Expr) (lps : List Name) : M PExpr :=
  withReader ({ · with lparams := lps }) (inferTypePure 83 e.toPExpr).run

@[inherit_doc whnf']
def whnf (e : PExpr) (lps : List Name) : M PExpr := withReader ({ · with lparams := lps }) $ (Inner.whnfPure 84 e).run

/--
Infers the type of expression `e`. Note that this uses the optimization
`inferOnly := false`, and so should only be used for the purpose of type
inference on terms that are known to be well-typed. To typecheck terms for the
first time, use `check`.
-/
def inferType (e : PExpr) (lps : List Name) : M PExpr := do
  let ret ← withReader ({ · with lparams := lps }) $ (Inner.inferTypePure 85 e).run
  pure ret

@[inherit_doc isDefEqCore]
def isDefEq (t s : PExpr) (lps : List Name) : MB :=
  withReader ({ · with lparams := lps }) (Inner.isDefEq 86 t s).run

def isDefEqPure (t s : PExpr) (lps : List Name) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqPure 87 t s).run

@[inherit_doc ensureSortCore]
def ensureSort (t : PExpr) (lps : List Name) (s := t) : MEE := 
  withReader ({ · with lparams := lps }) $ RecM.run do 
    ensureSortCore t s

@[inherit_doc ensureSortCore]
def ensureSortPure (t : PExpr) (lps : List Name) (s := t) : M PExpr := withReader ({ · with lparams := lps }) $ RecM.run do 
  try
    let res ← runLeanMinus $ Lean.TypeChecker.ensureSort t.toExpr s.toExpr
    pure res.toPExpr
  catch e =>
    throw e

@[inherit_doc ensureForallCore]
def ensureForall (t : PExpr) (lps : List Name) (s := t) : MEE := withReader ({ · with lparams := lps }) $ (ensureForallCore t s).run

def maybeCast (p? : Option EExpr) (typLhs typRhs e : PExpr) (lps : List Name) : M PExpr := 
  withReader ({ · with lparams := lps }) (Inner.maybeCast 24 p? typLhs typRhs e).run

def smartCast (typLhs typRhs e : PExpr) (lps : List Name) : M (Bool × PExpr) := 
  withReader ({ · with lparams := lps }) (Inner.smartCast 25 typLhs typRhs e).run

-- def test' : MetaM String := do
--   dbg_trace s!"test"
--   unreachable!
--   pure "HERE"
--
-- def test : MetaM Unit := do
--   let x ← test'
--   dbg_trace s!"{x}"
--
-- -- #eval test

/--
Ensures that `e` is defeq to some `e' := .sort (_ + 1)`, returning `e'`. If not,
throws an error with `s` (the expression required be a type).
-/
def ensureType (e : PExpr) (lps : List Name) : MEE := withReader ({ · with lparams := lps }) $ RecM.run $
  do ensureSortCore (← inferType e lps) e -- FIXME transport e using proof from ensureSort?

def ensureTypePure (e : PExpr) (lps : List Name) : M PExpr := do ensureSortPure (← inferType e lps) lps e -- FIXME transport e using proof from ensureSort?
