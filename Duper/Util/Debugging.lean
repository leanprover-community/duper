import Lean
open Lean

namespace Duper

-- Check heartbeat with given maxheartbeat number

def checkGivenHeartbeats (moduleName : String) (max : Nat) : CoreM Unit := do
  Core.checkMaxHeartbeatsCore moduleName `maxHeartbeats (max * 1000)


-- Options that can be used in debugging

register_option duperDebugOpt1 : Nat := {
  defValue := 0
  descr := "Duper debugging option 1"
}

def getDuperDebugOpt1 : CoreM Nat := do
  let opts ← getOptions
  return duperDebugOpt1.get opts

register_option duperDebugOpt2 : Nat := {
  defValue := 0
  descr := "Duper debugging option 2"
}

def getDuperDebugOpt2 : CoreM Nat := do
  let opts ← getOptions
  return duperDebugOpt2.get opts