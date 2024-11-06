import Lean4Lean.TypeChecker

namespace Lean.TypeChecker

open Inner
open Lean

def defFuel := 1000

mutual
def fuelWrap (idx : Nat) (fuel : Nat) (d : CallData) : M (CallDataT d) := do
-- let trace := (← readThe Context).trace
let trace := false
match fuel with
  | 0 =>
    -- dbg_trace s!">deep recursion callstack: {(← readThe Context).callStack.map (·.1)}"
    throw .deepRecursion
  | fuel' + 1 =>
    let m : RecM (CallDataT d):=
      match d with
      | .isDefEqCore t s => isDefEqCore' t s
      | .whnfCore e r p => whnfCore' e r p
      | .whnf e => whnf' e
      | .inferType e o => inferType' e o
    modify fun s => {s with numCalls := s.numCalls + 1} 
    let s ← get
    let mut printedTrace := false
    let print := false
    -- let print := true
    if print && trace then
      if s.numCalls % 1 == 0 then
        printedTrace := true
        -- let l := (← readThe Context).callStack.map fun d => s!"{d.1}/{d.2.1}"
        let mut l := (← readThe Context).callStack.map fun d => s!"{d.1}"
        if l.size > 20 then
          l := l[l.size - 20:]
        dbg_trace s!">calltrace {s.numCalls}: {l}, {idx}, {(← readThe Context).callId}"
    try
      let ret ← withCallId s.numCalls (.some 22160) do
        if trace then
          withCallData idx s.numCalls d $ m (Methods.withFuel fuel')
        else
          m (Methods.withFuel fuel')
      -- if printedTrace then
      --   dbg_trace s!">end of    {s.numCalls}: {(← readThe Context).callStack.map (·.1)}, {idx}, {(← readThe Context).callId}"
      pure ret
    catch e =>
      if trace then
        dbg_trace s!">calltrace {s.numCalls}: {(← readThe Context).callStack.map (·.1)}, {idx}"
      throw e

def Methods.withFuel (n : Nat) : Methods := 
  { isDefEqCore := fun i t s => do
      fuelWrap i n $ .isDefEqCore t s
    whnfCore := fun i e k p => do
      fuelWrap i n $ .whnfCore e k p
    whnf := fun i e => do
      fuelWrap i n $ .whnf e
    inferType := fun i e d => do
      fuelWrap i n $ .inferType e d
  }
end

def RecM.run (x : RecM α) (fuel := defFuel) : M α := x (Methods.withFuel fuel)

def check (e : Expr) (lps : List Name) : M Expr :=
  withReader ({ · with lparams := lps }) (inferType 48 e (inferOnly := false)).run

def whnf (e : Expr) : M Expr := (Inner.whnf 49 e).run

def inferType (e : Expr) : M Expr := (Inner.inferType 50 e).run

def inferTypeCheck (e : Expr) : M Expr := (Inner.inferType 51 e (inferOnly := false)).run

def isDefEq (t s : Expr) (fuel := defFuel) : M Bool := (Inner.isDefEq 69 t s).run fuel

def isDefEqCore (t s : Expr) : M Bool := (Inner.isDefEqCore 52 t s).run

def isProp (t : Expr) : M Bool := (Inner.isProp t).run

def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e
