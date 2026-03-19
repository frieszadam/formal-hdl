-- Adam Friesz, Winter 2026

import mathlib

namespace hdl
open hdl

set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- ==========================================
-- 1. Pure Mathematical Helpers
-- ==========================================

-- Helper to convert bus state to integer representation (LSB first)
-- Rewritten to use structural recursion instead of foldl for easier proof automation
def bitsToNat {N : Nat} (s : Fin N → Bool) : List (Fin N) → Nat
  | [] => 0
  | (b :: bs) => (if s b then 1 else 0) + 2 * bitsToNat s bs

def compute_adder_1 (cin a b : Bool) : Nat :=
  (if cin then 1 else 0) + a.toNat + b.toNat

-- The 2-bit math core (built sequentially from two 1-bit cores!)
def compute_adder_2 (cin a0 a1 b0 b1 : Bool) : Nat :=
  let sum0 := compute_adder_1 cin a0 b0
  let c1   := sum0.testBit 1
  let sum1 := compute_adder_1 c1 a1 b1
  (sum0 % 2) + (sum1 * 2)

def compute_adder_4 (cin a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : Nat :=
  let lo_sum := compute_adder_2 cin a0 a1 b0 b1
  let c_mid  := lo_sum.testBit 2
  let hi_sum := compute_adder_2 c_mid a2 a3 b2 b3
  (lo_sum % 4) + (hi_sum * 4)

-- ==========================================
-- 2. Core Structural Types (No Proofs Here)
-- ==========================================

inductive GateKind
  | igate | dff
  | not_ | and_ | or_ | xor_
  -- Adders
  | adder_1 (bit : Fin 2)
  | adder_2 (bit : Fin 3)
  | adder_4 (bit : Fin 5)
  -- Comparators (A < B)
  | comp_1 | comp_2 | comp_4
  -- Up/Down Counters (outputs the Next State bit)
  | up_down_count_1 (bit : Fin 1)
  | up_down_count_2 (bit : Fin 2)
  | up_down_count_4 (bit : Fin 4)
  -- Decoder
  | decoder_3 (bit : Fin 8)

def GateKind.ni : GateKind → Nat
  | .igate => 0
  | .dff | .not_ => 1
  | .and_ | .or_ | .xor_ | .comp_1 => 2
  | .adder_1 _ | .up_down_count_1 _ | .decoder_3 _ => 3
  | .comp_2 | .up_down_count_2 _ => 4
  | .adder_2 _ => 5
  | .up_down_count_4 _ => 6
  | .comp_4 => 8
  | .adder_4 _ => 9

def GateKind.is_seq : GateKind → Bool
  | .dff => true
  | _    => false

structure Gate where
  kind : GateKind
  init_val : Bool

structure Circuit where
  gates : List Gate
  wiring : (i : Fin gates.length) → Fin (gates.get i).kind.ni → Fin gates.length
  is_dag : ∀ (i : Fin gates.length) (p : Fin (gates.get i).kind.ni),
    let source := wiring i p
    (gates.get i).kind.is_seq = false → source < i

-- ==========================================
-- 3. The Evaluator
-- ==========================================

def mkWiring (gates : List Gate) (connections : List (List Nat))
  (h_gates : 0 < gates.length)
  (i : Fin gates.length) (p : Fin (gates.get i).kind.ni) : Fin gates.length :=
  let conn := (connections.getD i.val []).getD p.val 0
  if h1 : conn < gates.length then
    ⟨conn, h1⟩
  else
    ⟨0, h_gates⟩

def State (C : Circuit) :=
  (i : Fin C.gates.length) → Bool

def initState (C : Circuit) : State C :=
  fun i => (C.gates.get i).init_val

def evalCombinatorial (C : Circuit) (fuel : Nat) (curr_state : Fin C.gates.length → Bool) (i : Fin C.gates.length) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    let gate := C.gates.get i
    if gate.kind.is_seq then
      curr_state i
    else
      match h_kind : gate.kind with
      | .igate => curr_state i
      | .not_ => !(evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩))
      | .and_ => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) &&
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)
      | .or_  => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) ||
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)
      | .xor_ => evalCombinatorial C f curr_state (C.wiring i ⟨0, by rw [h_kind]; decide⟩) ^^
                 evalCombinatorial C f curr_state (C.wiring i ⟨1, by rw [h_kind]; decide⟩)

      -- Fast Standard Cell Evaluation
-- Comparators
      | .comp_1 =>
          let w (idx : Fin 2) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          (w 0).toNat < (w 1).toNat
      | .comp_2 =>
          let w (idx : Fin 4) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let a_val := (w 0).toNat + 2*(w 1).toNat
          let b_val := (w 2).toNat + 2*(w 3).toNat
          a_val < b_val
      | .comp_4 =>
          let w (idx : Fin 8) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let a_val := (w 0).toNat + 2*(w 1).toNat + 4*(w 2).toNat + 8*(w 3).toNat
          let b_val := (w 4).toNat + 2*(w 5).toNat + 4*(w 6).toNat + 8*(w 7).toNat
          a_val < b_val
      -- Up/Down Counters
      | .up_down_count_1 bit =>
          let w (idx : Fin 3) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let next_val := if w 0 && !(w 1) then ((w 2).toNat + 1) % 2 else if w 1 && !(w 0) then ((w 2).toNat + 1) % 2 else (w 2).toNat
          next_val.testBit bit.val
      | .up_down_count_2 bit =>
          let w (idx : Fin 4) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let q_val := (w 2).toNat + 2*(w 3).toNat
          let next_val := if w 0 && !(w 1) then (q_val + 1) % 4 else if w 1 && !(w 0) then (q_val + 3) % 4 else q_val
          next_val.testBit bit.val
      | .up_down_count_4 bit =>
          let w (idx : Fin 6) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let q_val := (w 2).toNat + 2*(w 3).toNat + 4*(w 4).toNat + 8*(w 5).toNat
          let next_val := if w 0 && !(w 1) then (q_val + 1) % 16 else if w 1 && !(w 0) then (q_val + 15) % 16 else q_val
          next_val.testBit bit.val
      | .adder_1 bit =>
          let w (idx : Fin 3) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let res := compute_adder_1 (w 0) (w 1) (w 2)
          res.testBit bit.val
      | .adder_2 bit =>
          let w (idx : Fin 5) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let res := compute_adder_2 (w 0) (w 1) (w 2) (w 3) (w 4)
          res.testBit bit.val
      | .adder_4 bit =>
          let w (idx : Fin 9) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let res := compute_adder_4 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8)
          res.testBit bit.val
      | .decoder_3 bit =>
          let w (idx : Fin 3) := evalCombinatorial C f curr_state (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩)
          let val := (w 0).toNat + 2*(w 1).toNat + 4*(w 2).toNat
          val == bit.val
      | _ => false

def step (C : Circuit) (stable_state : State C) (env_inputs : List Bool) : State C :=
  fun i =>
    let gate := C.gates.get i
    match h_kind : gate.kind with
    | .igate => env_inputs.getD i.val false
    | .dff =>
      let src := C.wiring i ⟨0, by rw [h_kind]; decide⟩
      stable_state src
    | _ => false

def runCycle (C : Circuit) (s : State C) (env_inputs : List Bool) : State C :=
  let stable_current := evalCombinatorial C C.gates.length s
  step C stable_current env_inputs

-- Takes an input trace which will be passed through the circuit in consecutive cycle
def runCycles (C : Circuit) (s : State C) : List (List Bool) → List (State C)
  | [] => [s]
  | (inps :: rest) => s :: runCycles C (runCycle C s inps) rest

-- ==========================================
-- 4. The Formal Contracts & Proof-Carrying Typeclasses
-- ==========================================

-- Generic Mathematical Contracts
class IsAdder (C : Circuit) (n : Nat)
  (a_bus b_bus : List (Fin C.gates.length))
  (sum_bus : List (Fin C.gates.length))
  (cin : Fin C.gates.length)
  (cout : Fin C.gates.length) : Prop where
  widths_match : a_bus.length = n ∧ b_bus.length = n ∧ sum_bus.length = n
  inputs_are_valid : ∀ i ∈ cin :: (a_bus ++ b_bus), (C.gates.get i).kind.ni = 0
  adder_correct : ∀ (s : Fin C.gates.length → Bool),
    let stable_s := evalCombinatorial C C.gates.length s
    let A_val := bitsToNat stable_s a_bus
    let B_val := bitsToNat stable_s b_bus
    let Sum_val := bitsToNat stable_s sum_bus
    let Cin_val := if stable_s cin then 1 else 0
    let Cout_val := if stable_s cout then (2 ^ n) else 0
    Sum_val + Cout_val = A_val + B_val + Cin_val

class IsSubtractor (C : Circuit) (n : Nat)
  (a_bus b_bus : List (Fin C.gates.length))
  (diff_bus : List (Fin C.gates.length))
  (bin : Fin C.gates.length)
  (bout : Fin C.gates.length) : Prop where
  widths_match : a_bus.length = n ∧ b_bus.length = n ∧ diff_bus.length = n
  inputs_are_valid : ∀ i ∈ bin :: (a_bus ++ b_bus), (C.gates.get i).kind.ni = 0
  sub_correct : ∀ (s : Fin C.gates.length → Bool),
    let stable_s := evalCombinatorial C C.gates.length s
    let A_val := bitsToNat stable_s a_bus
    let B_val := bitsToNat stable_s b_bus
    let Diff_val := bitsToNat stable_s diff_bus
    let Bin_val := if stable_s bin then 1 else 0
    let Bout_val := if stable_s bout then (2 ^ n) else 0
    -- Arranged as A + Bout*2^n = B + Diff + Bin to avoid negative integer math!
    A_val + Bout_val = B_val + Diff_val + Bin_val

class IsComparator (C : Circuit) (n : Nat)
  (a_bus b_bus : List (Fin C.gates.length))
  (out : Fin C.gates.length) : Prop where
  widths_match : a_bus.length = n ∧ b_bus.length = n
  inputs_are_valid : ∀ i ∈ (a_bus ++ b_bus), (C.gates.get i).kind.ni = 0
  comp_correct : ∀ (s : Fin C.gates.length → Bool),
    let stable_s := evalCombinatorial C C.gates.length s
    let A_val := bitsToNat stable_s a_bus
    let B_val := bitsToNat stable_s b_bus
    let Out_val := stable_s out
    Out_val = (A_val < B_val)

class IsUpCounter (C : Circuit) (n : Nat) (q_bus : List (Fin C.gates.length)) (inc : Fin C.gates.length) : Prop where
  widths_match : q_bus.length = n
  inputs_are_valid : (C.gates.get inc).kind.ni = 0 ∧ ∀ i ∈ q_bus, (C.gates.get i).kind.is_seq = true
  incr_on_high : ∀ (s : State C) (env : List Bool),
    s inc = true →
    bitsToNat (runCycle C s env) q_bus = (bitsToNat s q_bus + 1) % (2 ^ n)
  hold_on_low : ∀ (s : State C) (env : List Bool),
    s inc = false →
    bitsToNat (runCycle C s env) q_bus = bitsToNat s q_bus

class IsUpDownCounter (C : Circuit) (n : Nat)
  (q_bus : List (Fin C.gates.length))
  (incr decr : Fin C.gates.length) : Prop where
  widths_match : q_bus.length = n
  inputs_are_valid : (C.gates.get incr).kind.ni = 0 ∧
                     (C.gates.get decr).kind.ni = 0 ∧
                     ∀ i ∈ q_bus, (C.gates.get i).kind.is_seq = true
  -- 1. Increment when ONLY Incr is high
  count_up : ∀ (s : State C) (env : List Bool),
    s incr = true → s decr = false →
    bitsToNat (runCycle C s env) q_bus = (bitsToNat s q_bus + 1) % (2 ^ n)
  -- 2. Decrement when ONLY Decr is high (Uses Two's Complement math to avoid Nat flooring)
  count_down : ∀ (s : State C) (env : List Bool),
    s incr = false → s decr = true →
    bitsToNat (runCycle C s env) q_bus = (bitsToNat s q_bus + (2 ^ n - 1)) % (2 ^ n)
  -- 3. Hold when neither is asserted (00) OR both are asserted simultaneously (11)
  hold_on_invalid : ∀ (s : State C) (env : List Bool),
    s incr = s decr →
    bitsToNat (runCycle C s env) q_bus = bitsToNat s q_bus

class IsDecoder (C : Circuit) (n : Nat)
  (sel_bus : List (Fin C.gates.length))
  (out_bus : List (Fin C.gates.length)) : Prop where
  widths_match : sel_bus.length = n ∧ out_bus.length = 2 ^ n
  inputs_are_valid : ∀ i ∈ sel_bus, (C.gates.get i).kind.ni = 0
  decode_correct : ∀ (s : Fin C.gates.length → Bool),
    let stable_s := evalCombinatorial C C.gates.length s
    let sel_val := bitsToNat stable_s sel_bus
    let out_val := bitsToNat stable_s out_bus
    out_val = 2 ^ sel_val

-- Specific Parameterized Verified Implementations
class VerifiedAdder1 (C : Circuit) (a b sum : List (Fin C.gates.length)) (cin cout : Fin C.gates.length) : Prop where
  proof : IsAdder C 1 a b sum cin cout

class VerifiedAdder2 (C : Circuit) (a b sum : List (Fin C.gates.length)) (cin cout : Fin C.gates.length) : Prop where
  proof : IsAdder C 2 a b sum cin cout

class VerifiedAdder4 (C : Circuit) (a b sum : List (Fin C.gates.length)) (cin cout : Fin C.gates.length) : Prop where
  proof : IsAdder C 4 a b sum cin cout

class VerifiedSubtractor1 (C : Circuit) (a b diff : List (Fin C.gates.length)) (bin bout : Fin C.gates.length) : Prop where
  proof : IsSubtractor C 1 a b diff bin bout

class VerifiedSubtractor2 (C : Circuit) (a b diff : List (Fin C.gates.length)) (bin bout : Fin C.gates.length) : Prop where
  proof : IsSubtractor C 2 a b diff bin bout

class VerifiedSubtractor4 (C : Circuit) (a b diff : List (Fin C.gates.length)) (bin bout : Fin C.gates.length) : Prop where
  proof : IsSubtractor C 4 a b diff bin bout

class VerifiedComp4 (C : Circuit) (a b : List (Fin C.gates.length)) (out : Fin C.gates.length) : Prop where
  proof : IsComparator C 4 a b out

class VerifiedUpCounter1 (C : Circuit) (q_bus : List (Fin C.gates.length)) (inc : Fin C.gates.length) : Prop where
  proof : IsUpCounter C 1 q_bus inc

class VerifiedUpCounter2 (C : Circuit) (q_bus : List (Fin C.gates.length)) (inc : Fin C.gates.length) : Prop where
  proof : IsUpCounter C 2 q_bus inc

class VerifiedUpCounter4 (C : Circuit) (q_bus : List (Fin C.gates.length)) (inc : Fin C.gates.length) : Prop where
  proof : IsUpCounter C 4 q_bus inc

class VerifiedUpDownCounter4 (C : Circuit) (q_bus : List (Fin C.gates.length)) (incr decr : Fin C.gates.length) : Prop where
  proof : IsUpDownCounter C 4 q_bus incr decr

class VerifiedUpDownCounter5 (C : Circuit) (q_bus : List (Fin C.gates.length)) (incr decr : Fin C.gates.length) : Prop where
  proof : IsUpDownCounter C 5 q_bus incr decr

class VerifiedDecoder3 (C : Circuit) (sel_bus out_bus : List (Fin C.gates.length)) : Prop where
  proof : IsDecoder C 3 sel_bus out_bus

-- ==========================================
-- 5. AST Evaluator
-- ==========================================

inductive CombExpr (Idx : Type)
  | stateRef (i : Idx)
  | false_const | true_const
  | not (e : CombExpr Idx)
  | and (a b : CombExpr Idx)
  | or  (a b : CombExpr Idx)
  | xor (a b : CombExpr Idx)
  -- Comparators
  | comp_1 (args : List (CombExpr Idx))
  | comp_2 (args : List (CombExpr Idx))
  | comp_4 (args : List (CombExpr Idx))
  -- Adders
  | adder_1 (bit : Fin 2) (args : List (CombExpr Idx))
  | adder_2 (bit : Fin 3) (args : List (CombExpr Idx))
  | adder_4 (bit : Fin 5) (args : List (CombExpr Idx))
  -- Up/Down Counters
  | up_down_count_1 (bit : Fin 1) (args : List (CombExpr Idx))
  | up_down_count_2 (bit : Fin 2) (args : List (CombExpr Idx))
  | up_down_count_4 (bit : Fin 4) (args : List (CombExpr Idx))
  -- Decoder
  | decoder_3 (bit : Fin 8) (args : List (CombExpr Idx))

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
  -- Comparators
  | .comp_1 args =>
      match args with
      | [a0, b0] =>
          (evalExpr state a0).toNat < (evalExpr state b0).toNat
      | _ => false
  | .comp_2 args =>
      match args with
      | [a0, a1, b0, b1] =>
          let a_val := (evalExpr state a0).toNat + 2*(evalExpr state a1).toNat
          let b_val := (evalExpr state b0).toNat + 2*(evalExpr state b1).toNat
          a_val < b_val
      | _ => false
  | .comp_4 args =>
      match args with
      | [a0, a1, a2, a3, b0, b1, b2, b3] =>
          let a_val := (evalExpr state a0).toNat + 2*(evalExpr state a1).toNat + 4*(evalExpr state a2).toNat + 8*(evalExpr state a3).toNat
          let b_val := (evalExpr state b0).toNat + 2*(evalExpr state b1).toNat + 4*(evalExpr state b2).toNat + 8*(evalExpr state b3).toNat
          a_val < b_val
      | _ => false
  -- Up/Down Counters
  | .up_down_count_1 bit args =>
      match args with
      | [incr, decr, q0] =>
          let w0 := evalExpr state incr
          let w1 := evalExpr state decr
          let w2 := evalExpr state q0
          let next_val := if w0 && !w1 then (w2.toNat + 1) % 2 else if w1 && !w0 then (w2.toNat + 1) % 2 else w2.toNat
          next_val.testBit bit.val
      | _ => false
  | .up_down_count_2 bit args =>
      match args with
      | [incr, decr, q0, q1] =>
          let w0 := evalExpr state incr
          let w1 := evalExpr state decr
          let q_val := (evalExpr state q0).toNat + 2*(evalExpr state q1).toNat
          let next_val := if w0 && !w1 then (q_val + 1) % 4 else if w1 && !w0 then (q_val + 3) % 4 else q_val
          next_val.testBit bit.val
      | _ => false
  | .up_down_count_4 bit args =>
      match args with
      | [incr, decr, q0, q1, q2, q3] =>
          let w0 := evalExpr state incr
          let w1 := evalExpr state decr
          let q_val := (evalExpr state q0).toNat + 2*(evalExpr state q1).toNat + 4*(evalExpr state q2).toNat + 8*(evalExpr state q3).toNat
          let next_val := if w0 && !w1 then (q_val + 1) % 16 else if w1 && !w0 then (q_val + 15) % 16 else q_val
          next_val.testBit bit.val
      | _ => false
  | .adder_1 bit args =>
      match args with
      | [cin, a, b] =>
          let res := compute_adder_1 (evalExpr state cin) (evalExpr state a) (evalExpr state b)
          res.testBit bit.val
      | _ => false
  | .adder_2 bit args =>
      match args with
      | [cin, a0, a1, b0, b1] =>
          let res := compute_adder_2
            (evalExpr state cin)
            (evalExpr state a0) (evalExpr state a1)
            (evalExpr state b0) (evalExpr state b1)
          res.testBit bit.val
      | _ => false
  | .adder_4 bit args =>
      match args with
      | [cin, a0, a1, a2, a3, b0, b1, b2, b3] =>
          let res := compute_adder_4
            (evalExpr state cin)
            (evalExpr state a0) (evalExpr state a1) (evalExpr state a2) (evalExpr state a3)
            (evalExpr state b0) (evalExpr state b1) (evalExpr state b2) (evalExpr state b3)
          res.testBit bit.val
      | _ => false
  | .decoder_3 bit args =>
      match args with
      | [s0, s1, s2] =>
          let val := (evalExpr state s0).toNat + 2*(evalExpr state s1).toNat + 4*(evalExpr state s2).toNat
          val == bit.val
      | _ => false

def stepAst {N : Nat} (C : AstCircuit N) (curr_state : Fin N → Bool) (env_inputs : List Bool) : Fin N → Bool :=
  fun i =>
    if C.is_input i then env_inputs.getD i.val false
    else evalExpr curr_state (C.next_state i)

def unrollDAG (C : Circuit) (fuel : Nat) (i : Fin C.gates.length) : CombExpr (Fin C.gates.length) :=
  match fuel with
  | 0 => .false_const
  | f + 1 =>
    let gate := C.gates.get i
    if gate.kind.is_seq then .stateRef i
    else
      match h_kind : gate.kind with
      | .igate => .stateRef i
      | .not_ => .not (unrollDAG C f (C.wiring i ⟨0, by rw [h_kind]; decide⟩))
      | .and_ => .and (unrollDAG C f (C.wiring i ⟨0, by rw [h_kind]; decide⟩)) (unrollDAG C f (C.wiring i ⟨1, by rw [h_kind]; decide⟩))
      | .or_  => .or  (unrollDAG C f (C.wiring i ⟨0, by rw [h_kind]; decide⟩)) (unrollDAG C f (C.wiring i ⟨1, by rw [h_kind]; decide⟩))
      | .xor_ => .xor (unrollDAG C f (C.wiring i ⟨0, by rw [h_kind]; decide⟩)) (unrollDAG C f (C.wiring i ⟨1, by rw [h_kind]; decide⟩))
      | .comp_1 =>
          let args := List.ofFn (fun (idx : Fin 2) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .comp_1 args
      | .comp_2 =>
          let args := List.ofFn (fun (idx : Fin 4) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .comp_2 args
      | .comp_4 =>
          let args := List.ofFn (fun (idx : Fin 8) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .comp_4 args

      | .up_down_count_1 bit =>
          let args := List.ofFn (fun (idx : Fin 3) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .up_down_count_1 bit args
      | .up_down_count_2 bit =>
          let args := List.ofFn (fun (idx : Fin 4) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .up_down_count_2 bit args
      | .up_down_count_4 bit =>
          let args := List.ofFn (fun (idx : Fin 6) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .up_down_count_4 bit args
      | .adder_1 bit =>
          let args := List.ofFn (fun (idx : Fin 3) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .adder_1 bit args
      | .adder_2 bit =>
          let args := List.ofFn (fun (idx : Fin 5) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .adder_2 bit args
      | .adder_4 bit =>
          let args := List.ofFn (fun (idx : Fin 9) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .adder_4 bit args
      | .decoder_3 bit =>
          let args := List.ofFn (fun (idx : Fin 3) => unrollDAG C f (C.wiring i ⟨idx.val, by rw [h_kind]; exact idx.isLt⟩))
          .decoder_3 bit args
      | _ => .false_const

def to_ast (C : Circuit) : AstCircuit C.gates.length := {
  is_input := fun i => match (C.gates.get i).kind with | .igate => true | _ => false,
  is_seq := fun i => (C.gates.get i).kind.is_seq,
  next_state := fun i =>
    let gate := C.gates.get i
    match h_kind : gate.kind with
    | .dff =>
        let p : Fin gate.kind.ni := ⟨0, by rw [h_kind]; decide⟩
        unrollDAG C C.gates.length (C.wiring i p)
    | _ => .false_const
}

end hdl
