-- Adam Friesz, Winter 2026

import FormalHdl.Defs

namespace hdl.examples
open hdl

set_option linter.style.longLine false
set_option linter.style.whitespace false

-- A typeclass defining the formal specification of a 1-bit enabled counter.
class IsOneBitCounter (C : Circuit) (en_idx : Fin C.gates.length) (out_idx : Fin C.gates.length) where

  -- 1. Structural Verification
  -- Proves the gate assigned as the enable signal is truly an input port.
  en_is_input : (C.gates.get en_idx).kind.ni = 0

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
  igate false, -- Gate 0: en_i
  not,        -- Gate 1: ~en_i
  dff False,  -- Gate 2: cntr_o
  not,        -- Gate 3: ~cntr_o
  and,        -- Gate 4: en_i & ~cntr_o
  and,        -- Gate 5: ~en_i & cntr_o
  or          -- Gate 6: m0 | m1
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

instance counter_proof : IsOneBitCounter my_counter en_idx out_idx where
  en_is_input := by rfl
  starts_low := by rfl

  toggle_on_high := by
    intro s env h_en
    rw [my_counter_equiv] -- teleport to the AST domain
    simp [h_en]

  hold_on_low := by
    intro s env h_en
    rw [my_counter_equiv] -- teleport to the AST domain
    simp [h_en]


/-
  Full Adder
-/

class IsFullAdder (C : Circuit) (a b cin sum cout : Fin C.gates.length) where
  a_is_input   : (C.gates.get a).kind.ni = 0
  b_is_input   : (C.gates.get b).kind.ni = 0
  cin_is_input : (C.gates.get cin).kind.ni = 0

  -- The stable output of the Sum pin must match the XOR cascade
  sum_logic : ∀ (s : State C),
    evalCombinatorial C C.gates.length s sum =
    ((s a ^^ s b) ^^ s cin)

  -- The stable output of the Cout pin must match the carry logic
  cout_logic : ∀ (s : State C),
    evalCombinatorial C C.gates.length s cout =
    ((s a && s b) || ((s a ^^ s b) && s cin))

def fa_gates : List Gate := [
  igate false, -- Gate 0: A
  igate false, -- Gate 1: B
  igate false, -- Gate 2: Cin
  xor,   -- Gate 3: A ^ B
  and,   -- Gate 4: A & B
  xor,   -- Gate 5: Sum = (A ^ B) ^ Cin
  and,   -- Gate 6: (A ^ B) & Cin
  or     -- Gate 7: Cout = (A & B) | ((A ^ B) & Cin)
]

def fa_connections : List (List Nat) := [
  [],      -- 0: A
  [],      -- 1: B
  [],      -- 2: Cin
  [0, 1],  -- 3: A ^ B
  [0, 1],  -- 4: A & B
  [3, 2],  -- 5: Sum
  [3, 2],  -- 6: (A ^ B) & Cin
  [4, 6]   -- 7: Cout
]

def full_adder : Circuit := {
  gates := fa_gates,
  wiring := mkWiring fa_gates fa_connections (by decide),
  is_dag := by decide
}

-- 1. Update the indices to use the dynamic length instead of hardcoded 8
def a_idx   : Fin full_adder.gates.length := ⟨0, by decide⟩
def b_idx   : Fin full_adder.gates.length := ⟨1, by decide⟩
def cin_idx : Fin full_adder.gates.length := ⟨2, by decide⟩
def sum_idx : Fin full_adder.gates.length := ⟨5, by decide⟩
def cout_idx: Fin full_adder.gates.length := ⟨7, by decide⟩

-- 2. Update the Equivalence Bridge
lemma fa_comb_equiv (s : State full_adder) (i : Fin full_adder.gates.length) :
  evalCombinatorial full_adder full_adder.gates.length s i =
  evalExpr s (unrollDAG full_adder full_adder.gates.length i) := by
  fin_cases i <;> rfl

-- 3. Update the Simp Lemmas
@[simp] lemma ast_fa_sum (s : State full_adder) :
  evalExpr s (unrollDAG full_adder full_adder.gates.length sum_idx) =
  ((s a_idx ^^ s b_idx) ^^ s cin_idx) := by rfl

@[simp] lemma ast_fa_cout (s : State full_adder) :
  evalExpr s (unrollDAG full_adder full_adder.gates.length cout_idx) =
  ((s a_idx && s b_idx) || ((s a_idx ^^ s b_idx) && s cin_idx)) := by rfl

instance fa_proof : IsFullAdder full_adder a_idx b_idx cin_idx sum_idx cout_idx where
  a_is_input   := by rfl
  b_is_input   := by rfl
  cin_is_input := by rfl

  sum_logic := by
    intro s
    rw [fa_comb_equiv]
    simp

  cout_logic := by
    intro s
    rw [fa_comb_equiv]
    simp

/-
  N-bit adder
-/

-- Converts a list of wire indices (LSB first) into a Nat based on the current state.
@[simp]
def bitsToNat {C : Circuit} (s : State C) : List (Fin C.gates.length) → Nat
  | []      => 0
  | i :: is => (s i).toNat + 2 * bitsToNat s is

class IsAdder (C : Circuit) (n : Nat)
  (a_bus b_bus : List (Fin C.gates.length))
  (sum_bus : List (Fin C.gates.length))
  (cin : Fin C.gates.length)
  (cout : Fin C.gates.length) where
  widths_match : a_bus.length = n ∧ b_bus.length = n ∧ sum_bus.length = n
  inputs_are_valid : ∀ i ∈ cin :: (a_bus ++ b_bus), (C.gates.get i).kind.ni = 0
  adder_correct : ∀ (s : State C),
    let stable_s := evalCombinatorial C C.gates.length s
    let A_val := bitsToNat stable_s a_bus
    let B_val := bitsToNat stable_s b_bus
    let Sum_val := bitsToNat stable_s sum_bus
    let Cin_val := if stable_s cin then 1 else 0
    let Cout_val := if stable_s cout then (2 ^ n) else 0
    Sum_val + Cout_val = A_val + B_val + Cin_val -- expression of what an adder is

-- PURE FUNCTION: adder_rca_2
def adder_rca_2_pure_fn (cin : Bool) (a b : Nat) : Nat := a + b + (if cin then 1 else 0)

-- COMPONENT: adder_rca_2
def adder_rca_2_gates : List Gate := [
  igate false,
  igate false,
  igate false,
  igate false,
  igate false,
  xor,
  and,
  xor,
  and,
  or,
  xor,
  and,
  xor,
  and,
  or
]
def adder_rca_2_conns : List (List Nat) := [
  [],
  [],
  [],
  [],
  [],
  [1, 2],
  [1, 2],
  [5, 0],
  [5, 0],
  [6, 8],
  [3, 4],
  [3, 4],
  [10, 9],
  [10, 9],
  [11, 13]
]
def adder_rca_2 : Circuit := { gates := adder_rca_2_gates, wiring := mkWiring adder_rca_2_gates adder_rca_2_conns (by decide), is_dag := by decide }
def a_bus_adder_rca_2 : List (Fin 15) := [⟨1, by decide⟩, ⟨3, by decide⟩]
def b_bus_adder_rca_2 : List (Fin 15) := [⟨2, by decide⟩, ⟨4, by decide⟩]
def sum_bus_adder_rca_2 : List (Fin 15) := [⟨7, by decide⟩, ⟨12, by decide⟩]
def cin_adder_rca_2 : Fin 15 := ⟨0, by decide⟩
def cout_adder_rca_2 : Fin 15 := ⟨14, by decide⟩

-- EQUIVALENCE PROOF: adder_rca_2
@[simp] lemma ast_adder_rca_2_cin (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_a_0 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_b_0 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_a_1 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_b_1 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_sum_0 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) ^^ s ⟨0, by decide⟩) := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_sum_1 (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 12 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) ^^ ((s ⟨1, by decide⟩ && s ⟨2, by decide⟩) || ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) && s ⟨0, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_2_cout (s : State adder_rca_2) (i : Fin 15) (hi : i.val = 14 := by decide) : evalExpr s (unrollDAG adder_rca_2 15 i) = ((s ⟨3, by decide⟩ && s ⟨4, by decide⟩) || ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) && ((s ⟨1, by decide⟩ && s ⟨2, by decide⟩) || ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) && s ⟨0, by decide⟩)))) := by cases i; subst hi; rfl

instance : IsAdder adder_rca_2 2 a_bus_adder_rca_2 b_bus_adder_rca_2 sum_bus_adder_rca_2 cin_adder_rca_2 cout_adder_rca_2 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 15) : evalCombinatorial adder_rca_2 15 s i = evalExpr s (unrollDAG adder_rca_2 15 i) := by fin_cases i <;> rfl
    simp only [a_bus_adder_rca_2, b_bus_adder_rca_2, sum_bus_adder_rca_2, cout_adder_rca_2, cin_adder_rca_2, bitsToNat, Bool.toNat]
    simp only [equiv]
    simp only [ast_adder_rca_2_cin, ast_adder_rca_2_a_0, ast_adder_rca_2_b_0, ast_adder_rca_2_a_1, ast_adder_rca_2_b_1, ast_adder_rca_2_sum_0, ast_adder_rca_2_sum_1, ast_adder_rca_2_cout]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨3, by decide⟩ = a_1
    generalize h_b_1 : s ⟨4, by decide⟩ = b_1
    cases cin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> decide

-- CLA 2-Bit Adder Implementation
def adder_cla_2_gates : List Gate := [
  igate false,
  igate false,
  igate false,
  igate false,
  igate false,
  xor,
  and,
  xor,
  and,
  and,
  or,
  and,
  and,
  and,
  or,
  or,
  xor,
  xor
]
def adder_cla_2_conns : List (List Nat) := [
  [],
  [],
  [],
  [],
  [],
  [1, 2],
  [1, 2],
  [3, 4],
  [3, 4],
  [5, 0],
  [6, 9],
  [7, 6],
  [7, 5],
  [12, 0],
  [8, 11],
  [14, 13],
  [5, 0],
  [7, 10]
]
def adder_cla_2 : Circuit := { gates := adder_cla_2_gates, wiring := mkWiring adder_cla_2_gates adder_cla_2_conns (by decide), is_dag := by decide }
def a_bus_cla_2 : List (Fin 18) := [⟨1, by decide⟩, ⟨3, by decide⟩]
def b_bus_cla_2 : List (Fin 18) := [⟨2, by decide⟩, ⟨4, by decide⟩]
def sum_bus_cla_2 : List (Fin 18) := [⟨16, by decide⟩, ⟨17, by decide⟩]
def cin_cla_2 : Fin 18 := ⟨0, by decide⟩
def cout_cla_2 : Fin 18 := ⟨15, by decide⟩

@[simp] lemma ast_cla_cin (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_cla_a_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_cla_b_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_cla_a_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_cla_b_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_cla_sum_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 16 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) ^^ s ⟨0, by decide⟩) := by cases i; subst hi; rfl
@[simp] lemma ast_cla_sum_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) ^^ ((s ⟨1, by decide⟩ && s ⟨2, by decide⟩) || ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) && s ⟨0, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_cla_cout_2 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 15 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = (((s ⟨3, by decide⟩ && s ⟨4, by decide⟩) || ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) && (s ⟨1, by decide⟩ && s ⟨2, by decide⟩))) || (((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) && (s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩)) && s ⟨0, by decide⟩)) := by cases i; subst hi; rfl

instance : IsAdder adder_cla_2 2 a_bus_cla_2 b_bus_cla_2 sum_bus_cla_2 cin_cla_2 cout_cla_2 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 18) : evalCombinatorial adder_cla_2 adder_cla_2.gates.length s i = evalExpr s (unrollDAG adder_cla_2 18 i) := by fin_cases i <;> rfl
    simp only [a_bus_cla_2, b_bus_cla_2, sum_bus_cla_2, cout_cla_2, cin_cla_2, bitsToNat, Bool.toNat]
    simp only [equiv]
    simp only [ast_cla_cin, ast_cla_a_0, ast_cla_b_0, ast_cla_a_1, ast_cla_b_1, ast_cla_sum_0, ast_cla_sum_1, ast_cla_cout_2]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨3, by decide⟩ = a_1
    generalize h_b_1 : s ⟨4, by decide⟩ = b_1
    cases cin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> decide


/-
  Multi-Bit Counter Example
-/

-- COMPONENT: counter_4
def counter_4_gates : List Gate := [
  igate false,
  dff false,
  dff false,
  dff false,
  dff false,
  add4 0,
  add4 1,
  add4 2,
  add4 3
]

def counter_4_conns : List (List Nat) := [
  [],
  [5],
  [6],
  [7],
  [8],
  [0, 1, 2, 3, 4],
  [0, 1, 2, 3, 4],
  [0, 1, 2, 3, 4],
  [0, 1, 2, 3, 4]
]
def counter_4 : Circuit := { gates := counter_4_gates, wiring := mkWiring counter_4_gates counter_4_conns (by decide), is_dag := by decide }
def q_bus_counter_4 : List (Fin 9) := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
def inc_counter_4 : Fin 9 := ⟨0, by decide⟩

-- AST LEMMAS: counter_4
@[simp] lemma ast_counter_4_inc (s : State counter_4) (i : Fin 9) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG counter_4 counter_4.gates.length i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_0 (s : State counter_4) (i : Fin 9) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG counter_4 counter_4.gates.length i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_1 (s : State counter_4) (i : Fin 9) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG counter_4 counter_4.gates.length i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_2 (s : State counter_4) (i : Fin 9) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG counter_4 counter_4.gates.length i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_3 (s : State counter_4) (i : Fin 9) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG counter_4 counter_4.gates.length i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl

end hdl.examples
