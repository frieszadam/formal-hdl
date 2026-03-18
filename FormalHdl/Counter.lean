-- Adam Friesz, Winter 2026
import FormalHdl.Defs
namespace hdl.examples.counter
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- COMPONENT: counter_1
def counter_1_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .dff false,
  Gate.mk (.adder_1 ⟨0, by decide⟩) false
]
def counter_1_conns : List (List Nat) := [
  [],
  [0],
  [0, 1],
  [4],
  [0, 3, 2]
]
def counter_1 : Circuit := { gates := counter_1_gates, wiring := mkWiring counter_1_gates counter_1_conns (by decide), is_dag := by decide }
def q_bus_counter_1 : List (Fin counter_1.gates.length) := [⟨3, by decide⟩]
def inc_counter_1 : Fin counter_1.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: counter_1
@[simp] lemma ast_counter_1_inc (s : State counter_1) (i : Fin 5) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG counter_1 5 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_1_q_0 (s : State counter_1) (i : Fin 5) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG counter_1 5 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_1_zero (s : State counter_1) (i : Fin 5) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG counter_1 5 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_counter_1_next_q_0 (s : State counter_1) (i : Fin 5) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG counter_1 5 i) = (compute_adder_1 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma runCycle_counter_1_q_0 (s : State counter_1) (env : List Bool) : (runCycle counter_1 s env) ⟨3, by decide⟩ = evalCombinatorial counter_1 5 s ⟨4, by decide⟩ := by rfl

instance instIsCounter_counter_1 : IsCounter counter_1 1 q_bus_counter_1 inc_counter_1 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 5) : evalCombinatorial counter_1 5 s i = evalExpr s (unrollDAG counter_1 5 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_1, bitsToNat]
    simp only [runCycle_counter_1_q_0]
    simp only [equiv]
    simp only [ast_counter_1_next_q_0]
    simp only [inc_counter_1] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    cases val_q_0 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 5) : evalCombinatorial counter_1 5 s i = evalExpr s (unrollDAG counter_1 5 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_1, bitsToNat]
    simp only [runCycle_counter_1_q_0]
    simp only [equiv]
    simp only [ast_counter_1_next_q_0]
    simp only [inc_counter_1] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    cases val_q_0 <;> decide

instance instVerifiedCounter1_counter_1 : VerifiedCounter1 counter_1 q_bus_counter_1 inc_counter_1 where
  proof := instIsCounter_counter_1

-- COMPONENT: counter_2
def counter_2_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk (.adder_2 ⟨0, by decide⟩) false,
  Gate.mk (.adder_2 ⟨1, by decide⟩) false
]
def counter_2_conns : List (List Nat) := [
  [],
  [0],
  [0, 1],
  [5],
  [6],
  [0, 3, 4, 2, 2],
  [0, 3, 4, 2, 2]
]
def counter_2 : Circuit := { gates := counter_2_gates, wiring := mkWiring counter_2_gates counter_2_conns (by decide), is_dag := by decide }
def q_bus_counter_2 : List (Fin counter_2.gates.length) := [⟨3, by decide⟩, ⟨4, by decide⟩]
def inc_counter_2 : Fin counter_2.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: counter_2
@[simp] lemma ast_counter_2_inc (s : State counter_2) (i : Fin 7) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_2_q_0 (s : State counter_2) (i : Fin 7) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_2_q_1 (s : State counter_2) (i : Fin 7) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_2_zero (s : State counter_2) (i : Fin 7) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_counter_2_next_q_0 (s : State counter_2) (i : Fin 7) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_counter_2_next_q_1 (s : State counter_2) (i : Fin 7) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG counter_2 7 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma runCycle_counter_2_q_0 (s : State counter_2) (env : List Bool) : (runCycle counter_2 s env) ⟨3, by decide⟩ = evalCombinatorial counter_2 7 s ⟨5, by decide⟩ := by rfl
@[simp] lemma runCycle_counter_2_q_1 (s : State counter_2) (env : List Bool) : (runCycle counter_2 s env) ⟨4, by decide⟩ = evalCombinatorial counter_2 7 s ⟨6, by decide⟩ := by rfl

instance instIsCounter_counter_2 : IsCounter counter_2 2 q_bus_counter_2 inc_counter_2 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 7) : evalCombinatorial counter_2 7 s i = evalExpr s (unrollDAG counter_2 7 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_2, bitsToNat]
    simp only [runCycle_counter_2_q_0, runCycle_counter_2_q_1]
    simp only [equiv]
    simp only [ast_counter_2_next_q_0, ast_counter_2_next_q_1]
    simp only [inc_counter_2] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    cases val_q_0 <;> cases val_q_1 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 7) : evalCombinatorial counter_2 7 s i = evalExpr s (unrollDAG counter_2 7 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_2, bitsToNat]
    simp only [runCycle_counter_2_q_0, runCycle_counter_2_q_1]
    simp only [equiv]
    simp only [ast_counter_2_next_q_0, ast_counter_2_next_q_1]
    simp only [inc_counter_2] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    cases val_q_0 <;> cases val_q_1 <;> decide

instance instVerifiedCounter2_counter_2 : VerifiedCounter2 counter_2 q_bus_counter_2 inc_counter_2 where
  proof := instIsCounter_counter_2

-- COMPONENT: counter_4
def counter_4_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk (.adder_4 ⟨0, by decide⟩) false,
  Gate.mk (.adder_4 ⟨1, by decide⟩) false,
  Gate.mk (.adder_4 ⟨2, by decide⟩) false,
  Gate.mk (.adder_4 ⟨3, by decide⟩) false
]
def counter_4_conns : List (List Nat) := [
  [],
  [0],
  [0, 1],
  [7],
  [8],
  [9],
  [10],
  [0, 3, 4, 5, 6, 2, 2, 2, 2],
  [0, 3, 4, 5, 6, 2, 2, 2, 2],
  [0, 3, 4, 5, 6, 2, 2, 2, 2],
  [0, 3, 4, 5, 6, 2, 2, 2, 2]
]
def counter_4 : Circuit := { gates := counter_4_gates, wiring := mkWiring counter_4_gates counter_4_conns (by decide), is_dag := by decide }
def q_bus_counter_4 : List (Fin counter_4.gates.length) := [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]
def inc_counter_4 : Fin counter_4.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: counter_4
@[simp] lemma ast_counter_4_inc (s : State counter_4) (i : Fin 11) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_0 (s : State counter_4) (i : Fin 11) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_1 (s : State counter_4) (i : Fin 11) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_2 (s : State counter_4) (i : Fin 11) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_q_3 (s : State counter_4) (i : Fin 11) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_zero (s : State counter_4) (i : Fin 11) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_next_q_0 (s : State counter_4) (i : Fin 11) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_next_q_1 (s : State counter_4) (i : Fin 11) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_next_q_2 (s : State counter_4) (i : Fin 11) (hi : i.val = 9 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_counter_4_next_q_3 (s : State counter_4) (i : Fin 11) (hi : i.val = 10 := by decide) : evalExpr s (unrollDAG counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 3 := by cases i; subst hi; rfl
@[simp] lemma runCycle_counter_4_q_0 (s : State counter_4) (env : List Bool) : (runCycle counter_4 s env) ⟨3, by decide⟩ = evalCombinatorial counter_4 11 s ⟨7, by decide⟩ := by rfl
@[simp] lemma runCycle_counter_4_q_1 (s : State counter_4) (env : List Bool) : (runCycle counter_4 s env) ⟨4, by decide⟩ = evalCombinatorial counter_4 11 s ⟨8, by decide⟩ := by rfl
@[simp] lemma runCycle_counter_4_q_2 (s : State counter_4) (env : List Bool) : (runCycle counter_4 s env) ⟨5, by decide⟩ = evalCombinatorial counter_4 11 s ⟨9, by decide⟩ := by rfl
@[simp] lemma runCycle_counter_4_q_3 (s : State counter_4) (env : List Bool) : (runCycle counter_4 s env) ⟨6, by decide⟩ = evalCombinatorial counter_4 11 s ⟨10, by decide⟩ := by rfl

instance instIsCounter_counter_4 : IsCounter counter_4 4 q_bus_counter_4 inc_counter_4 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 11) : evalCombinatorial counter_4 11 s i = evalExpr s (unrollDAG counter_4 11 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_4, bitsToNat]
    simp only [runCycle_counter_4_q_0, runCycle_counter_4_q_1, runCycle_counter_4_q_2, runCycle_counter_4_q_3]
    simp only [equiv]
    simp only [ast_counter_4_next_q_0, ast_counter_4_next_q_1, ast_counter_4_next_q_2, ast_counter_4_next_q_3]
    simp only [inc_counter_4] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨5, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨6, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 11) : evalCombinatorial counter_4 11 s i = evalExpr s (unrollDAG counter_4 11 i) := by fin_cases i <;> rfl
    simp only [q_bus_counter_4, bitsToNat]
    simp only [runCycle_counter_4_q_0, runCycle_counter_4_q_1, runCycle_counter_4_q_2, runCycle_counter_4_q_3]
    simp only [equiv]
    simp only [ast_counter_4_next_q_0, ast_counter_4_next_q_1, ast_counter_4_next_q_2, ast_counter_4_next_q_3]
    simp only [inc_counter_4] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨5, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨6, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide

instance instVerifiedCounter4_counter_4 : VerifiedCounter4 counter_4 q_bus_counter_4 inc_counter_4 where
  proof := instIsCounter_counter_4

/-
  Cycle by Cycle Simulation Example
-/

-- Sequence of inputs (e.g., 4 cycles of incrementing)
def input_stimulus : List (List Bool) := [[true], [true], [true], [true], [false], [false]]

-- Generate the trace and extract the numeric values of the q_bus
-- expected value 0, 0, 1, 2, 3, 4
-- note that t0 corresponds to reset, so the input is not consumed until t1
#eval (runCycles counter_4 (initState counter_4) input_stimulus).map (fun s =>
  bitsToNat (evalCombinatorial counter_4 counter_4.gates.length s) q_bus_counter_4
)

end hdl.examples.counter
