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
set_option linter.style.longLine false

-- 1. The Single Source of Truth for Logic
inductive GateKind
  | igate  -- Input port (0 inputs)
  | dff    -- Register (1 input)
  | not_   -- Inverter (1 input)
  | and_   -- AND gate (2 inputs)
  | or_    -- OR gate (2 inputs)
  | xor_   -- XOR gate (2 inputs)

-- 2. Intrinsic Arity (Replaces `ni` in the Gate structure)
def GateKind.ni : GateKind → Nat
  | .igate => 0
  | .dff   => 1
  | .not_  => 1
  | .and_  => 2
  | .or_   => 2
  | .xor_  => 2

-- 3. Intrinsic Sequentiality (Replaces `is_seq` in the Gate structure)
def GateKind.is_seq : GateKind → Bool
  | .igate => true  -- Inputs hold state between clock edges
  | .dff   => true  -- Registers hold state
  | _      => false -- Combinatorial logic is transient

-- 4. The Minimalist Gate Structure
structure Gate where
  kind : GateKind
  init_val : Bool   -- Ignored for combinatorial gates
  is_output : Bool  -- Probe flag for gatherOutputs

-- 5. Helper Functions for instantiation (to keep your user API clean)
def igate (start_val : Bool) : Gate :=
  { kind := .igate, init_val := start_val, is_output := false }

def dff (reset_val is_output : Bool) : Gate :=
  { kind := .dff, init_val := reset_val, is_output := is_output }

def and (is_output : Bool) : Gate :=
  { kind := .and_, init_val := false, is_output := is_output }

def or (is_output : Bool) : Gate :=
  { kind := .or_, init_val := false, is_output := is_output }

def xor (is_output : Bool) : Gate :=
  { kind := .xor_, init_val := false, is_output := is_output }

def not (is_output : Bool) : Gate :=
  { kind := .not_, init_val := false, is_output := is_output }

structure Circuit where
  gates : List Gate

  -- The wiring depends on the intrinsic arity of the gate's kind!
  wiring : (i : Fin gates.length) → Fin (gates.get i).kind.ni → Fin gates.length

  -- The DAG proof uses the intrinsic sequentiality
  is_dag : ∀ (i : Fin gates.length) (p : Fin (gates.get i).kind.ni),
    let source := wiring i p
    (gates.get i).kind.is_seq = false → source < i


structure Module where
  -- The isolated, formally verified internal circuit
  C : Circuit

  -- The indices of the input ports.
  -- (These should map to `.igate` components inside `C`)
  in_ports : List (Fin C.gates.length)

  -- The indices of the output ports.
  out_ports : List (Fin C.gates.length)

-- Helper to map raw adjacency lists to dependent Fin types
-- Connections are now just a List of source gate indices
def mkWiring (gates : List Gate) (connections : List (List Nat))
  (h_gates : 0 < gates.length)
  (i : Fin gates.length) (p : Fin (gates.get i).kind.ni) :
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
-- Fuel-based structural evaluator. Lean's kernel evaluates this instantly.
def evalCombinatorial (C : Circuit) (fuel : Nat) (curr_state : State C) (i : Fin C.gates.length) : Bool :=
  match fuel with
  | 0 => false -- Out of fuel
  | f + 1 =>
    let gate := C.gates.get i
    if gate.kind.is_seq then
      curr_state i
    else
      match h_kind : gate.kind with
      | .not_ => !(evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩))
      | .and_ => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) &&
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)
      | .or_  => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) ||
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)
      | .xor_ => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) ^^
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)
      | _     => false

-- The step function models the clock edge.
def step (C : Circuit) (stable_state : State C) (env_inputs : List Bool) : State C :=
  fun i =>
    let gate := C.gates.get i
    match h_kind : gate.kind with
    | .igate => -- External inputs latch the new values from the environment
      env_inputs.getD i.val false
    | .dff => -- Registers latch their current input value
      let src := C.wiring i ⟨0, by rw [h_kind]; decide⟩
      stable_state src
    | _ => -- Combinatorial gates do not hold state across clock edges.
      false

-- Step remains unchanged, but runCycle injects the maximum fuel (C.gates.length)
def runCycle (C : Circuit) (s : State C) (env_inputs : List Bool) : State C :=
  let stable_current := evalCombinatorial C C.gates.length s
  step C stable_current env_inputs

/-
  AST
-/

inductive CombExpr (Idx : Type)
  | stateRef (i : Idx)
  | false_const
  | true_const
  | not      (e : CombExpr Idx)
  | and      (a b : CombExpr Idx)
  | or       (a b : CombExpr Idx)
  | xor      (a b : CombExpr Idx)

structure AstCircuit (N : Nat) where
  is_input : (i : Fin N) → Bool
  is_seq   : (i : Fin N) → Bool
  next_state : (i : Fin N) → CombExpr (Fin N)

def evalExpr {Idx : Type} (state : Idx → Bool) : CombExpr Idx → Bool
  | .stateRef i   => state i
  | .false_const  => false
  | .true_const   => true
  | .not e        => !(evalExpr state e)
  | .and a b      => (evalExpr state a) && (evalExpr state b)
  | .or a b       => (evalExpr state a) || (evalExpr state b)
  | .xor a b      => (evalExpr state a) ^^ (evalExpr state b)

-- Aligned signature with structural `step`
def stepAst {N : Nat} (C : AstCircuit N) (curr_state : Fin N → Bool) (env_inputs : List Bool) : Fin N → Bool :=
  fun i =>
    if C.is_input i then
      env_inputs.getD i.val false
    else
      evalExpr curr_state (C.next_state i)

def unrollDAG (C : Circuit) (fuel : Nat) (i : Fin C.gates.length) : CombExpr (Fin C.gates.length) :=
  match fuel with
  | 0 => .false_const -- Out of fuel (Mathematically impossible if C.is_dag is true)
  | f + 1 =>
    let gate := C.gates.get i

    if gate.kind.is_seq then
      .stateRef i
    else
      match h_kind : gate.kind with
      | .not_ =>
          let p : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
          .not (unrollDAG C f (C.wiring i p))

      | .and_ =>
          let p0 : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
          let p1 : Fin gate.kind.ni := ⟨1, by rw [h_kind]; decide⟩
          .and (unrollDAG C f (C.wiring i p0)) (unrollDAG C f (C.wiring i p1))

      | .or_ =>
          let p0 : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
          let p1 : Fin gate.kind.ni := ⟨1, by rw [h_kind]; decide⟩
          .or (unrollDAG C f (C.wiring i p0)) (unrollDAG C f (C.wiring i p1))

      | .xor_ =>
          let p0 : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
          let p1 : Fin gate.kind.ni := ⟨1, by rw [h_kind]; decide⟩
          .xor (unrollDAG C f (C.wiring i p0)) (unrollDAG C f (C.wiring i p1))

      | _ => .false_const

def to_ast (C : Circuit) : AstCircuit C.gates.length := {
  is_input := fun i =>
    match (C.gates.get i).kind with
    | .igate => true
    | _ => false,

  is_seq := fun i => (C.gates.get i).kind.is_seq,

  next_state := fun i =>
    let gate := C.gates.get i
    match h_kind : gate.kind with
    | .dff =>
        let p : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
        let src := C.wiring i p

        -- We jumpstart the recursion with maximum possible fuel
        unrollDAG C C.gates.length src

    | _ => .false_const
}

end hdl
