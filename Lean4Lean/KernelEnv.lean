import Lean
import Lean.Declaration
import Batteries.Tactic.OpenPrivate

open Lean

open private Lean.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment
open private Lean.Kernel.Environment.extraConstNames from Lean.Environment
open private Lean.Environment.asyncConstsMap from Lean.Environment
open private Lean.Environment.asyncCtx? from Lean.Environment
open private Lean.Environment.realizedImportedConsts? from Lean.Environment
open private Lean.Environment.realizedLocalConsts from Lean.Environment
open private Lean.Environment.serverBaseExts from Lean.Environment
open private Lean.Environment.allRealizations from Lean.Environment
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Environment.updateBaseAfterKernelAdd from Lean.Environment

def _root_.Lean.Kernel.Environment.toStage₁ (kernel : Kernel.Environment) : Kernel.Environment :=
  Lean.Kernel.Environment.mk {kernel.constants with stage₁ := true} kernel.quotInit kernel.diagnostics (kernel.const2ModIdx) (Lean.Kernel.Environment.extensions kernel) (Lean.Kernel.Environment.extraConstNames kernel) (kernel.header)

namespace Lean4Lean

def updateConst2ModIdx (env : Kernel.Environment) (const2ModIdx : Std.HashMap Name ModuleIdx) : Kernel.Environment := Id.run $ do
  let mut newConst2ModIdx := env.const2ModIdx.union const2ModIdx
  let newKernel := Lean.Kernel.Environment.mk env.constants env.quotInit env.diagnostics newConst2ModIdx (Lean.Kernel.Environment.extensions env) (Lean.Kernel.Environment.extraConstNames env) (env.header)
  pure newKernel

def updateBaseAfterKernelAdd (env : Environment) (kernel : Kernel.Environment) : Environment :=
  let newKernel := Lean.Kernel.Environment.mk kernel.constants kernel.quotInit kernel.diagnostics (env.toKernelEnv.const2ModIdx) (Lean.Kernel.Environment.extensions env.toKernelEnv) (Lean.Kernel.Environment.extraConstNames kernel) (env.toKernelEnv.header)
  Lean.Environment.mk (.mk newKernel newKernel) (Lean.Environment.serverBaseExts env) (.pure newKernel) (Lean.Environment.asyncConstsMap env) (Lean.Environment.asyncCtx? env) (Lean.Environment.realizedImportedConsts? env) (Lean.Environment.realizedLocalConsts env) (Lean.Environment.allRealizations env) (env.isExporting)
