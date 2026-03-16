-- Adam Friesz, Winter 2026

import FormalHdl.Defs

namespace hdl.examples
open hdl

set_option linter.style.longLine false

-- A typeclass defining the formal specification of a 1-bit enabled counter.
class OneBitCounter (C : Circuit) (en_idx : Fin C.gates.length) (out_idx : Fin C.gates.length) where

  -- 1. Structural Verification
  -- Proves the gate assigned as the enable signal is truly an input port.
  en_is_input : (C.gates.get en_idx).kind.ni = 0
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
  igate True,           -- Gate 0: en_i
  hdl.not False,        -- Gate 1: ~en_i
  dff False True,       -- Gate 2: cntr_o
  hdl.not False,        -- Gate 3: ~cntr_o
  hdl.and False,        -- Gate 4: en_i & ~cntr_o
  hdl.and False,        -- Gate 5: ~en_i & cntr_o
  hdl.or False          -- Gate 6: m0 | m1
]

def ex_connections : List (List Nat) := [
  [],
  [0],
  [6],
  [2],
  [0, 3],
  [1, 2],
  [4, 5]
]

def my_counter : Circuit := {
  gates := ex_gates,
  wiring := mkWiring ex_gates ex_connections (by decide),
  is_dag := by decide
}

def en_idx : Fin my_counter.gates.length := ⟨0, by decide⟩
def out_idx : Fin my_counter.gates.length := ⟨2, by decide⟩

/-
  Demonstrate step-through simulation logic
-/
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

/-
  Define AST equivalence to prove more complicated theorems.
-/

def my_counter_ast : AstCircuit 7 := to_ast my_counter

-- The Bridge: Proves the physical circuit and the AST compute the exact same boolean logic
lemma my_counter_equiv (s : State my_counter) (env : List Bool) (i : Fin 7) :
  runCycle my_counter s env i = stepAst my_counter_ast s env i := by
  -- Because both engines are fuel-based and completely concrete for `my_counter`,
  -- Lean's kernel unrolls them both and matches them perfectly.
  fin_cases i <;> rfl

-- The AST Evaluation Lemma
-- Evaluates the complex unrolled AST into clean boolean logic automatically.
@[simp]
lemma stepAst_counter_out (s : State my_counter) (env : List Bool) :
  stepAst my_counter_ast s env out_idx =
  ((s en_idx && !s out_idx) || (!s en_idx && s out_idx)) := by
  rfl

instance counter_proof : OneBitCounter my_counter en_idx out_idx where
  en_is_input := by rfl
  out_is_output := by rfl
  starts_low := by rfl

  toggle_on_high := by
    intro s env h_en
    rw [my_counter_equiv] -- teleport to the AST domain
    simp [h_en]

  hold_on_low := by
    intro s env h_en
    rw [my_counter_equiv] -- teleport to the AST domain
    simp [h_en]

end hdl.examples
