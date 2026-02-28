-- Adam Friesz, Winter 2026

import mathlib

-- Logical Framework
-- There exists a time t and input such that Circuit.eval(t, input) = output
-- However this requires a sequence of inputs to determine the Circuit state at time t
--
-- One idea is to model the structure similar to the Dyadics where circuits are made
-- from a chain of gates that operate on eachother. Two interesting things here are
-- how to have gates be dual-purpose feeding into another circuit or potentially
-- feeding to the output. The other issue are regs which could potentially just be
-- handled inside of the evaluation function ...
--

namespace hdl
open hdl

set_option linter.style.emptyLine false

-- all gates have 1 output and a parameterized number of inputs
structure Gate where
  ni : Nat
  f : Vector Bool ni → Bool
  is_seq : Bool
  init_val : Bool -- ignored when is_seq is False
  is_output : Bool

def not (is_output : Bool) : Gate := {
  ni := 1,
  f i := !i[0],
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def or (is_output : Bool) : Gate := {
  ni := 2,
  f i := i[0] || i[1],
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def and (is_output : Bool) : Gate := {
  ni := 2,
  f i := i[0] && i[1],
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def xor (is_output : Bool) : Gate := {
  ni := 2,
  f i := i[0] ^^ i[1],
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def nor (is_output : Bool) : Gate := {
  ni := 2,
  f i := !(i[0] || i[1]),
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def nand (is_output : Bool) : Gate := {
  ni := 2,
  f i := !(i[0] && i[1]),
  is_seq := False,
  init_val := False,
  is_output := is_output
}

def xnor (is_output : Bool) : Gate := {
  ni := 2,
  f i := !(i[0] ^^ i[1]),
  is_seq := False,
  init_val := False,
  is_output := is_output
}

-- DFFs are a circuit primitive evaluated as sequential logic
def dff (reset_val is_output : Bool) : Gate := {
  ni := 1,
  f i := i[0],
  is_seq := True,
  init_val := reset_val,
  is_output := is_output
}

def igate (start_val : Bool) : Gate := {
  ni := 0,
  f _ := False,
  is_seq := True,
  init_val := start_val,
  is_output := False
}

structure Circuit where
  gates : List Gate

  -- (Gate Index, Input Pin) -> Source Gate Index
  wiring : (i : Fin gates.length) → Fin (gates.get i).ni → Fin gates.length

  -- Ensure combinatorial paths are acyclic
  is_dag : ∀ (i : Fin gates.length) (p : Fin (gates.get i).ni),
    let source := wiring i p
    (gates.get i).is_seq = false → source < i

-- Helper to map raw adjacency lists to dependent Fin types
-- Connections are now just a List of source gate indices
def mkWiring (gates : List Gate) (connections : List (List Nat))
  (h_gates : 0 < gates.length)
  (i : Fin gates.length) (p : Fin (gates.get i).ni) :
  Fin gates.length :=

  -- Safely extract the source gate index from the raw list
  let conn := (connections.getD i.val []).getD p.val 0

  -- Validate the source gate index
  if h1 : conn < gates.length then
    ⟨conn, h1⟩
  else
    ⟨0, h_gates⟩ -- Fallback to Gate 0 using non-empty constraint

-- State only needs to map a Gate Index to a single Bool
def State (C : Circuit) :=
  (i : Fin C.gates.length) → Bool

def initState (C : Circuit) : State C :=
  fun i => (C.gates.get i).init_val

-- Helper: Gathers the input vector for a specific gate based on the current wire states
def gatherInputs (C : Circuit) (s : State C) (i : Fin C.gates.length) :
  Vector Bool (C.gates.get i).ni :=
  ⟨ Array.ofFn (fun p =>
      let src := C.wiring i p
      s src
    ),
    Array.size_ofFn
  ⟩

-- Helper: Dynamically searches the circuit for any gate flagged as an output.
def gatherOutputs (C : Circuit) (s : State C) : List Bool :=
  let all_gates := List.finRange C.gates.length
  all_gates.filterMap (fun i =>
    if (C.gates.get i).is_output then
      some (s i)
    else
      none
  )

-- Evaluates the stable state of the circuit during the current clock cycle.
-- Proven to terminate because combinatorial dependencies strictly decrease in index.
def evalCombinatorial (C : Circuit) (curr_state : State C) (i : Fin C.gates.length) : Bool :=
  let gate := C.gates.get i

  if h : gate.is_seq = false then -- combinational branch
    let inputs := ⟨ Array.ofFn (fun p =>
      let src := C.wiring i p
      have _h_wf : src < i := C.is_dag i p h
      evalCombinatorial C curr_state src
    ), Array.size_ofFn ⟩

    gate.f inputs

  else -- sequential branch
    curr_state i

-- prove termination by observing that the index strictly decreases.
termination_by i.val

-- The step function models the clock edge.
def step (C : Circuit) (stable_state : State C) (env_inputs : List Bool) : State C :=
  fun i =>
    let gate := C.gates.get i

    if gate.ni = 0 then
      env_inputs.getD i.val false

    else if gate.is_seq then
      let next_d := gatherInputs C stable_state i
      gate.f next_d

    else
      false

-- Run a complete cycle
def runCycle (C : Circuit) (s : State C) (env_inputs : List Bool) : State C :=
  let stable_current := evalCombinatorial C s
  step C stable_current env_inputs

/-
  Simp Lemmas
-/

-- Tell simp to always unfold runCycle
@[simp] lemma runCycle_def (C : Circuit) (s : State C) (env : List Bool) :
  runCycle C s env = step C (evalCombinatorial C s) env := by rfl

-- Tell simp to unfold gatherInputs
@[simp] lemma gatherInputs_def (C : Circuit) (s : State C) (i : Fin C.gates.length) :
  gatherInputs C s i = ⟨ Array.ofFn (fun p => s (C.wiring i p)), Array.size_ofFn ⟩ := by rfl

-- Lemmas to tell Lean how to evaluate each Gate
@[simp] lemma eval_not (is_out : Bool) (inputs : Vector Bool 1) :
  (hdl.not is_out).f inputs = !(inputs.get 0) := by rfl

@[simp] lemma eval_and (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.and is_out).f inputs = (inputs.get 0 && inputs.get 1) := by rfl

@[simp] lemma eval_nand (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.nand is_out).f inputs = !(inputs.get 0 && inputs.get 1) := by rfl

@[simp] lemma eval_or (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.or is_out).f inputs = (inputs.get 0 || inputs.get 1) := by rfl

@[simp] lemma eval_nor (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.nor is_out).f inputs = !(inputs.get 0 || inputs.get 1) := by rfl

@[simp] lemma eval_xor (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.xor is_out).f inputs = (inputs.get 0 ^^ inputs.get 1) := by rfl

@[simp] lemma eval_xnor (is_out : Bool) (inputs : Vector Bool 2) :
  (hdl.xnor is_out).f inputs = !(inputs.get 0 ^^ inputs.get 1) := by rfl

end hdl
