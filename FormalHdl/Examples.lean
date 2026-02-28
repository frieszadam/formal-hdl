-- Adam Friesz, Winter 2026

import FormalHdl.Defs

namespace hdl.examples
open hdl

set_option linter.style.longLine false
/-
  Examples
-/

-- A typeclass defining the formal specification of a 1-bit enabled counter.
class OneBitCounter (C : Circuit) (en_idx : Fin C.gates.length) (out_idx : Fin C.gates.length) where

  -- 1. Structural Verification
  -- Proves the gate assigned as the enable signal is truly an input port.
  en_is_input : (C.gates.get en_idx).ni = 0
  out_is_output : (C.gates.get out_idx).is_output

-- Toggles if the internal enable wire is currently high
  toggle_on_high : ∀ (s : State C) (env : List Bool),
    s en_idx = true →
    (runCycle C s env) out_idx = !(s out_idx)

  -- Holds if the internal enable wire is currently low
  hold_on_low : ∀ (s : State C) (env : List Bool),
    s en_idx = false →
    (runCycle C s env) out_idx = s out_idx

  -- 4. The Initialization Property
  -- Proves the circuit powers on to a 'False' state at the output.
  starts_low : (initState C) out_idx = false

def ex_gates : List Gate := [
  igate True,           -- Enable signal
  dff False True,       -- Q (Flip-Flop) - Flagged as Output!
  hdl.not False,        -- Q_bar (NOT gate)
  hdl.and False         -- Next D (AND gate)
]

-- Notice how much cleaner the wiring is without the `× Nat` pin index!
def ex_connections : List (List Nat) := [
  [],                  -- Gate 0 (igate): 0 inputs
  [3],                 -- Gate 1 (dff)  : Input 0 connects to Gate 3
  [1],                 -- Gate 2 (not)  : Input 0 connects to Gate 1
  [0, 2]               -- Gate 3 (and)  : Input 0 -> Gate 0, Input 1 -> Gate 2
]

def my_counter : Circuit := {
  gates := ex_gates,
  wiring := mkWiring ex_gates ex_connections (by decide),
  is_dag := by decide
}

def en_idx : Fin my_counter.gates.length := ⟨0, by decide⟩
def out_idx : Fin my_counter.gates.length := ⟨1, by decide⟩

def counter_c0 : State my_counter := initState my_counter

def counter_c1 : State my_counter :=
  runCycle my_counter counter_c0 [true]

def counter_c2 : State my_counter :=
  runCycle my_counter counter_c1 [true]

def counter_c3 : State my_counter :=
  runCycle my_counter counter_c2 [true]

#eval gatherOutputs my_counter counter_c0
#eval gatherOutputs my_counter counter_c1
#eval gatherOutputs my_counter counter_c2
#eval gatherOutputs my_counter counter_c3

-- Teach Lean Gates of my_counter
@[simp] lemma my_counter_gate_0 :
  my_counter.gates.get ⟨0, by decide⟩ = igate true := by rfl

@[simp] lemma my_counter_gate_1 :
  my_counter.gates.get ⟨1, by decide⟩ = dff false true := by rfl

@[simp] lemma my_counter_gate_2 :
  my_counter.gates.get ⟨2, by decide⟩ = not false := by rfl

@[simp] lemma my_counter_gate_3 :
  my_counter.gates.get ⟨3, by decide⟩ = and false := by rfl

instance counter_proof : OneBitCounter my_counter en_idx out_idx where
  en_is_input := by rfl
  out_is_output := by rfl
  starts_low := by rfl
  toggle_on_high := by
    sorry
  hold_on_low := by
    sorry

end hdl.examples
