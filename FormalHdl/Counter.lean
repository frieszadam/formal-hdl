-- FormalHDL — Verified Counter Components
-- Adam Friesz, Winter 2026
--
-- Five counter designs proved correct:
--
--   up_counter_1        — 1-bit synchronous up-counter with enable (IsUpCounter n=1)
--   up_counter_2        — 2-bit synchronous up-counter with enable (IsUpCounter n=2)
--   up_counter_4        — 4-bit synchronous up-counter with enable (IsUpCounter n=4)
--   up_down_counter_4   — 4-bit up/down-counter (IsUpDownCounter n=4)
--   up_down_counter_5   — 5-bit up/down-counter (IsUpDownCounter n=5)
--
-- All up-counters use adder cells to compute Q+1 each cycle (when enabled).
-- The up/down-counters use an adder whose B-input is driven by a mux:
--   incr=1,decr=0 → add XOR(incr,decr) = 1            (increment)
--   incr=0,decr=1 → add 1111...1 (all-ones = -1 mod 2^n) (decrement)
--   incr=decr     → add 0                              (hold)
--
-- The 5-bit counter (up_down_counter_5) extends the 4-bit slice by chaining
-- a 1-bit adder_1 cell to propagate the carry into the 5th flip-flop.
--
-- Proof structure: same four-step recipe as all other components.
-- Sequential components additionally require `runCycle_*` lemmas that unfold
-- (runCycle C s env) ⟨dff_index, _⟩ = evalCombinatorial C n s ⟨next_state_gate, _⟩.

import FormalHdl.Defs
namespace hdl.examples.counter
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- ============================================================
-- COMPONENT: up_counter_1
--
-- 1-bit synchronous up-counter with active-high enable.
-- Gate layout (5 gates):
--   0 : igate       inc (enable)
--   1 : not_        ~inc   (used to build constant-0 for carry-in)
--   2 : and_        inc & ~inc = 0  (hardwired false: B input to adder)
--   3 : dff         Q[0]  (state register)
--   4 : adder_1 b=0 next_Q[0] = inc + Q[0] + 0
-- The adder is connected as: cin=inc, a=Q[0], b=0.
-- When inc=1: next = Q+1 mod 2.  When inc=0: next = Q.
-- ============================================================
def up_counter_1_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .dff false,
  Gate.mk (.adder_1 ⟨0, by decide⟩) false
]
def up_counter_1_conns : List (List Nat) := [
  [],
  [0],
  [0, 1],
  [4],
  [0, 3, 2]
]
def up_counter_1 : Circuit := { gates := up_counter_1_gates, wiring := mkWiring up_counter_1_gates up_counter_1_conns (by decide), is_dag := by decide }
def q_bus_up_counter_1 : List (Fin up_counter_1.gates.length) := [⟨3, by decide⟩]
def inc_up_counter_1 : Fin up_counter_1.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: up_counter_1
@[simp] lemma ast_up_counter_1_inc (s : State up_counter_1) (i : Fin 5) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG up_counter_1 5 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_1_q_0 (s : State up_counter_1) (i : Fin 5) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG up_counter_1 5 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_1_zero (s : State up_counter_1) (i : Fin 5) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG up_counter_1 5 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_1_next_q_0 (s : State up_counter_1) (i : Fin 5) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG up_counter_1 5 i) = (compute_adder_1 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma runCycle_up_counter_1_q_0 (s : State up_counter_1) (env : List Bool) : (runCycle up_counter_1 s env) ⟨3, by decide⟩ = evalCombinatorial up_counter_1 5 s ⟨4, by decide⟩ := by rfl

instance instIsUpCounter_up_counter_1 : IsUpCounter up_counter_1 1 q_bus_up_counter_1 inc_up_counter_1 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 5) : evalCombinatorial up_counter_1 5 s i = evalExpr s (unrollDAG up_counter_1 5 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_1, bitsToNat]
    simp only [runCycle_up_counter_1_q_0]
    simp only [equiv]
    simp only [ast_up_counter_1_next_q_0]
    simp only [inc_up_counter_1] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    cases val_q_0 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 5) : evalCombinatorial up_counter_1 5 s i = evalExpr s (unrollDAG up_counter_1 5 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_1, bitsToNat]
    simp only [runCycle_up_counter_1_q_0]
    simp only [equiv]
    simp only [ast_up_counter_1_next_q_0]
    simp only [inc_up_counter_1] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    cases val_q_0 <;> decide

instance instVerifiedUpCounter1_up_counter_1 : VerifiedUpCounter1 up_counter_1 q_bus_up_counter_1 inc_up_counter_1 where
  proof := instIsUpCounter_up_counter_1

-- ============================================================
-- COMPONENT: up_counter_2
--
-- 2-bit synchronous up-counter with active-high enable.
-- Gate layout (7 gates):
--   0   : igate         inc
--   1   : not_          ~inc
--   2   : and_          0 (constant false, B inputs to adder)
--   3,4 : dff           Q[0], Q[1]
--   5,6 : adder_2 b=0,1 next_Q[0], next_Q[1]
-- Adder inputs: cin=inc, A={Q[0],Q[1]}, B={0,0}.
-- ============================================================
def up_counter_2_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk (.adder_2 ⟨0, by decide⟩) false,
  Gate.mk (.adder_2 ⟨1, by decide⟩) false
]
def up_counter_2_conns : List (List Nat) := [
  [],
  [0],
  [0, 1],
  [5],
  [6],
  [0, 3, 4, 2, 2],
  [0, 3, 4, 2, 2]
]
def up_counter_2 : Circuit := { gates := up_counter_2_gates, wiring := mkWiring up_counter_2_gates up_counter_2_conns (by decide), is_dag := by decide }
def q_bus_up_counter_2 : List (Fin up_counter_2.gates.length) := [⟨3, by decide⟩, ⟨4, by decide⟩]
def inc_up_counter_2 : Fin up_counter_2.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: up_counter_2
@[simp] lemma ast_up_counter_2_inc (s : State up_counter_2) (i : Fin 7) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_2_q_0 (s : State up_counter_2) (i : Fin 7) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_2_q_1 (s : State up_counter_2) (i : Fin 7) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_2_zero (s : State up_counter_2) (i : Fin 7) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_2_next_q_0 (s : State up_counter_2) (i : Fin 7) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_2_next_q_1 (s : State up_counter_2) (i : Fin 7) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG up_counter_2 7 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma runCycle_up_counter_2_q_0 (s : State up_counter_2) (env : List Bool) : (runCycle up_counter_2 s env) ⟨3, by decide⟩ = evalCombinatorial up_counter_2 7 s ⟨5, by decide⟩ := by rfl
@[simp] lemma runCycle_up_counter_2_q_1 (s : State up_counter_2) (env : List Bool) : (runCycle up_counter_2 s env) ⟨4, by decide⟩ = evalCombinatorial up_counter_2 7 s ⟨6, by decide⟩ := by rfl

instance instIsUpCounter_up_counter_2 : IsUpCounter up_counter_2 2 q_bus_up_counter_2 inc_up_counter_2 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 7) : evalCombinatorial up_counter_2 7 s i = evalExpr s (unrollDAG up_counter_2 7 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_2, bitsToNat]
    simp only [runCycle_up_counter_2_q_0, runCycle_up_counter_2_q_1]
    simp only [equiv]
    simp only [ast_up_counter_2_next_q_0, ast_up_counter_2_next_q_1]
    simp only [inc_up_counter_2] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    cases val_q_0 <;> cases val_q_1 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 7) : evalCombinatorial up_counter_2 7 s i = evalExpr s (unrollDAG up_counter_2 7 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_2, bitsToNat]
    simp only [runCycle_up_counter_2_q_0, runCycle_up_counter_2_q_1]
    simp only [equiv]
    simp only [ast_up_counter_2_next_q_0, ast_up_counter_2_next_q_1]
    simp only [inc_up_counter_2] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    cases val_q_0 <;> cases val_q_1 <;> decide

instance instVerifiedUpCounter2_up_counter_2 : VerifiedUpCounter2 up_counter_2 q_bus_up_counter_2 inc_up_counter_2 where
  proof := instIsUpCounter_up_counter_2

-- ============================================================
-- COMPONENT: up_counter_4
--
-- 4-bit synchronous up-counter with active-high enable.
-- Same structure as up_counter_2 but scaled to 4 bits:
--   0      : igate           inc
--   1      : not_            ~inc
--   2      : and_            0 (constant false)
--   3–6    : dff             Q[0..3]
--   7–10   : adder_4 b=0..3 next_Q[0..3]
-- ============================================================
def up_counter_4_gates : List Gate := [
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
def up_counter_4_conns : List (List Nat) := [
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
def up_counter_4 : Circuit := { gates := up_counter_4_gates, wiring := mkWiring up_counter_4_gates up_counter_4_conns (by decide), is_dag := by decide }
def q_bus_up_counter_4 : List (Fin up_counter_4.gates.length) := [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]
def inc_up_counter_4 : Fin up_counter_4.gates.length := ⟨0, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: up_counter_4
@[simp] lemma ast_up_counter_4_inc (s : State up_counter_4) (i : Fin 11) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_q_0 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_q_1 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_q_2 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_q_3 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_zero (s : State up_counter_4) (i : Fin 11) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = (s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_next_q_0 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_next_q_1 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_next_q_2 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 9 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_up_counter_4_next_q_3 (s : State up_counter_4) (i : Fin 11) (hi : i.val = 10 := by decide) : evalExpr s (unrollDAG up_counter_4 11 i) = (compute_adder_4 (s ⟨0, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (s ⟨6, by decide⟩) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))).testBit 3 := by cases i; subst hi; rfl
@[simp] lemma runCycle_up_counter_4_q_0 (s : State up_counter_4) (env : List Bool) : (runCycle up_counter_4 s env) ⟨3, by decide⟩ = evalCombinatorial up_counter_4 11 s ⟨7, by decide⟩ := by rfl
@[simp] lemma runCycle_up_counter_4_q_1 (s : State up_counter_4) (env : List Bool) : (runCycle up_counter_4 s env) ⟨4, by decide⟩ = evalCombinatorial up_counter_4 11 s ⟨8, by decide⟩ := by rfl
@[simp] lemma runCycle_up_counter_4_q_2 (s : State up_counter_4) (env : List Bool) : (runCycle up_counter_4 s env) ⟨5, by decide⟩ = evalCombinatorial up_counter_4 11 s ⟨9, by decide⟩ := by rfl
@[simp] lemma runCycle_up_counter_4_q_3 (s : State up_counter_4) (env : List Bool) : (runCycle up_counter_4 s env) ⟨6, by decide⟩ = evalCombinatorial up_counter_4 11 s ⟨10, by decide⟩ := by rfl

instance instIsUpCounter_up_counter_4 : IsUpCounter up_counter_4 4 q_bus_up_counter_4 inc_up_counter_4 where
  widths_match := by decide
  inputs_are_valid := by decide
  incr_on_high := by
    intro s env h_inc
    have equiv (i : Fin 11) : evalCombinatorial up_counter_4 11 s i = evalExpr s (unrollDAG up_counter_4 11 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_4, bitsToNat]
    simp only [runCycle_up_counter_4_q_0, runCycle_up_counter_4_q_1, runCycle_up_counter_4_q_2, runCycle_up_counter_4_q_3]
    simp only [equiv]
    simp only [ast_up_counter_4_next_q_0, ast_up_counter_4_next_q_1, ast_up_counter_4_next_q_2, ast_up_counter_4_next_q_3]
    simp only [inc_up_counter_4] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨5, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨6, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  hold_on_low := by
    intro s env h_inc
    have equiv (i : Fin 11) : evalCombinatorial up_counter_4 11 s i = evalExpr s (unrollDAG up_counter_4 11 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_counter_4, bitsToNat]
    simp only [runCycle_up_counter_4_q_0, runCycle_up_counter_4_q_1, runCycle_up_counter_4_q_2, runCycle_up_counter_4_q_3]
    simp only [equiv]
    simp only [ast_up_counter_4_next_q_0, ast_up_counter_4_next_q_1, ast_up_counter_4_next_q_2, ast_up_counter_4_next_q_3]
    simp only [inc_up_counter_4] at h_inc
    simp only [h_inc]
    generalize h_val_q_0 : s ⟨3, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨4, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨5, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨6, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide

instance instVerifiedUpCounter4_up_counter_4 : VerifiedUpCounter4 up_counter_4 q_bus_up_counter_4 inc_up_counter_4 where
  proof := instIsUpCounter_up_counter_4

-- ============================================================
-- COMPONENT: up_down_counter_4
--
-- 4-bit synchronous up/down-counter.
-- Inputs: incr (gate 0), decr (gate 1).
-- State:  Q[0..3] held in DFFs at gates 2–5.
--
-- The combinatorial logic computes the adder B-inputs:
--   b_xor   = incr XOR decr  (gate 10 via OR of gates 8 and 9)
--   b_decr  = decr & ~incr   (gate 11, replicated for bits 1–3 at gates 12–14)
--   cin     = incr & ~incr = 0  (gate 14: hardwired false)
-- This yields:
--   incr=1, decr=0 → B = {0001}  → Q+1
--   incr=0, decr=1 → B = {1111}  → Q+15 = Q−1  (mod 16)
--   incr=decr      → B = {0000}  → Q unchanged
-- ============================================================
def up_down_counter_4_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk (.adder_4 ⟨0, by decide⟩) false,
  Gate.mk (.adder_4 ⟨1, by decide⟩) false,
  Gate.mk (.adder_4 ⟨2, by decide⟩) false,
  Gate.mk (.adder_4 ⟨3, by decide⟩) false
]
def up_down_counter_4_conns : List (List Nat) := [
  [],
  [],
  [15],
  [16],
  [17],
  [18],
  [0],
  [1],
  [0, 7],
  [1, 6],
  [8, 9],
  [9, 9],
  [9, 9],
  [9, 9],
  [0, 6],
  [14, 2, 3, 4, 5, 10, 11, 12, 13],
  [14, 2, 3, 4, 5, 10, 11, 12, 13],
  [14, 2, 3, 4, 5, 10, 11, 12, 13],
  [14, 2, 3, 4, 5, 10, 11, 12, 13]
]
def up_down_counter_4 : Circuit := { gates := up_down_counter_4_gates, wiring := mkWiring up_down_counter_4_gates up_down_counter_4_conns (by decide), is_dag := by decide }
def q_bus_up_down_counter_4 : List (Fin up_down_counter_4.gates.length) := [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
def incr_up_down_counter_4 : Fin up_down_counter_4.gates.length := ⟨0, by decide⟩
def decr_up_down_counter_4 : Fin up_down_counter_4.gates.length := ⟨1, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: up_down_counter_4
@[simp] lemma ast_up_down_counter_4_incr (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_decr (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_q_0 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_q_1 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_q_2 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_q_3 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_next_q_0 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 15 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_next_q_1 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 16 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_next_q_2 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_4_next_q_3 (s : State up_down_counter_4) (i : Fin 19) (hi : i.val = 18 := by decide) : evalExpr s (unrollDAG up_down_counter_4 19 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 3 := by cases i; subst hi; rfl
@[simp] lemma runCycle_up_down_counter_4_q_0 (s : State up_down_counter_4) (env : List Bool) (idx : Fin 19) (h : idx.val = 2 := by decide) : (runCycle up_down_counter_4 s env) idx = evalCombinatorial up_down_counter_4 19 s ⟨15, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_4_q_1 (s : State up_down_counter_4) (env : List Bool) (idx : Fin 19) (h : idx.val = 3 := by decide) : (runCycle up_down_counter_4 s env) idx = evalCombinatorial up_down_counter_4 19 s ⟨16, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_4_q_2 (s : State up_down_counter_4) (env : List Bool) (idx : Fin 19) (h : idx.val = 4 := by decide) : (runCycle up_down_counter_4 s env) idx = evalCombinatorial up_down_counter_4 19 s ⟨17, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_4_q_3 (s : State up_down_counter_4) (env : List Bool) (idx : Fin 19) (h : idx.val = 5 := by decide) : (runCycle up_down_counter_4 s env) idx = evalCombinatorial up_down_counter_4 19 s ⟨18, by decide⟩ := by cases idx; subst h; rfl

instance instIsUpDownCounter_up_down_counter_4 : IsUpDownCounter up_down_counter_4 4 q_bus_up_down_counter_4 incr_up_down_counter_4 decr_up_down_counter_4 where
  widths_match := by decide
  inputs_are_valid := by decide
  count_up := by
    intro s env h_incr h_decr
    have equiv (i : Fin 19) : evalCombinatorial up_down_counter_4 19 s i = evalExpr s (unrollDAG up_down_counter_4 19 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_4, bitsToNat]
    simp only [runCycle_up_down_counter_4_q_0, runCycle_up_down_counter_4_q_1, runCycle_up_down_counter_4_q_2, runCycle_up_down_counter_4_q_3]
    simp only [equiv]
    simp only [ast_up_down_counter_4_next_q_0, ast_up_down_counter_4_next_q_1, ast_up_down_counter_4_next_q_2, ast_up_down_counter_4_next_q_3]
    change s ⟨0, by decide⟩ = true at h_incr
    change s ⟨1, by decide⟩ = false at h_decr
    simp only [h_incr, h_decr]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  count_down := by
    intro s env h_incr h_decr
    have equiv (i : Fin 19) : evalCombinatorial up_down_counter_4 19 s i = evalExpr s (unrollDAG up_down_counter_4 19 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_4, bitsToNat]
    simp only [runCycle_up_down_counter_4_q_0, runCycle_up_down_counter_4_q_1, runCycle_up_down_counter_4_q_2, runCycle_up_down_counter_4_q_3]
    simp only [equiv]
    simp only [ast_up_down_counter_4_next_q_0, ast_up_down_counter_4_next_q_1, ast_up_down_counter_4_next_q_2, ast_up_down_counter_4_next_q_3]
    change s ⟨0, by decide⟩ = false at h_incr
    change s ⟨1, by decide⟩ = true at h_decr
    simp only [h_incr, h_decr]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  hold_on_invalid := by
    intro s env h_eq
    have equiv (i : Fin 19) : evalCombinatorial up_down_counter_4 19 s i = evalExpr s (unrollDAG up_down_counter_4 19 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_4, bitsToNat]
    simp only [runCycle_up_down_counter_4_q_0, runCycle_up_down_counter_4_q_1, runCycle_up_down_counter_4_q_2, runCycle_up_down_counter_4_q_3]
    simp only [equiv]
    simp only [ast_up_down_counter_4_next_q_0, ast_up_down_counter_4_next_q_1, ast_up_down_counter_4_next_q_2, ast_up_down_counter_4_next_q_3]
    change s ⟨0, by decide⟩ = s ⟨1, by decide⟩ at h_eq
    generalize h_in : s ⟨1, by decide⟩ = val_in
    rw [h_in] at h_eq
    simp only [h_eq]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    cases val_in <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide

instance instVerifiedUpDownCounter4_up_down_counter_4 : VerifiedUpDownCounter4 up_down_counter_4 q_bus_up_down_counter_4 incr_up_down_counter_4 decr_up_down_counter_4 where
  proof := instIsUpDownCounter_up_down_counter_4

-- ============================================================
-- COMPONENT: up_down_counter_5
--
-- 5-bit synchronous up/down-counter, extending up_down_counter_4.
-- The lower 4 bits are handled identically to up_down_counter_4
-- (gates 0–20, same B-input generation logic).
-- The 5th bit Q[4] is stored in a DFF at gate 6 and is driven by
-- an adder_1 cell (gate 22) that adds the carry-out from the
-- 4-bit slice (gate 21 bit=4) to Q[4] with B=decr_and_notincr.
--
-- Gate layout additions over the 4-bit version:
--   6   : dff            Q[4]
--   16  : and_           (same as gate 14, extra b-input copy for 5th bit)
--   21  : adder_4 bit=4  carry-out from lower 4 bits
--   22  : adder_1 bit=0  next_Q[4] = carry_out + Q[4] + b_decr
-- ============================================================
def up_down_counter_5_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk (.adder_4 ⟨0, by decide⟩) false,
  Gate.mk (.adder_4 ⟨1, by decide⟩) false,
  Gate.mk (.adder_4 ⟨2, by decide⟩) false,
  Gate.mk (.adder_4 ⟨3, by decide⟩) false,
  Gate.mk (.adder_4 ⟨4, by decide⟩) false,
  Gate.mk (.adder_1 ⟨0, by decide⟩) false
]
def up_down_counter_5_conns : List (List Nat) := [
  [],
  [],
  [17],
  [18],
  [19],
  [20],
  [22],
  [0],
  [1],
  [0, 8],
  [1, 7],
  [9, 10],
  [10, 10],
  [10, 10],
  [10, 10],
  [10, 10],
  [0, 7],
  [16, 2, 3, 4, 5, 11, 12, 13, 14],
  [16, 2, 3, 4, 5, 11, 12, 13, 14],
  [16, 2, 3, 4, 5, 11, 12, 13, 14],
  [16, 2, 3, 4, 5, 11, 12, 13, 14],
  [16, 2, 3, 4, 5, 11, 12, 13, 14],
  [21, 6, 15]
]
def up_down_counter_5 : Circuit := { gates := up_down_counter_5_gates, wiring := mkWiring up_down_counter_5_gates up_down_counter_5_conns (by decide), is_dag := by decide }
def q_bus_up_down_counter_5 : List (Fin up_down_counter_5.gates.length) := [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]
def incr_up_down_counter_5 : Fin up_down_counter_5.gates.length := ⟨0, by decide⟩
def decr_up_down_counter_5 : Fin up_down_counter_5.gates.length := ⟨1, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: up_down_counter_5
@[simp] lemma ast_up_down_counter_5_incr (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_decr (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_q_0 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_q_1 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_q_2 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_q_3 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_q_4 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_next_q_0 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_next_q_1 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 18 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_next_q_2 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 19 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_up_down_counter_5_next_q_3 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 20 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = (compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 3 := by cases i; subst hi; rfl
set_option maxHeartbeats 1000000 in -- takes a while to run
  @[simp] lemma ast_up_down_counter_5_next_q_4 (s : State up_down_counter_5) (i : Fin 23) (hi : i.val = 22 := by decide) : evalExpr s (unrollDAG up_down_counter_5 23 i) = (compute_adder_1 ((compute_adder_4 ((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩))) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩) (s ⟨5, by decide⟩) (((s ⟨0, by decide⟩ && !(s ⟨1, by decide⟩)) || (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)))) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 4) (s ⟨6, by decide⟩) (((s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩ && !(s ⟨0, by decide⟩))))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma runCycle_up_down_counter_5_q_0 (s : State up_down_counter_5) (env : List Bool) (idx : Fin 23) (h : idx.val = 2 := by decide) : (runCycle up_down_counter_5 s env) idx = evalCombinatorial up_down_counter_5 23 s ⟨17, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_5_q_1 (s : State up_down_counter_5) (env : List Bool) (idx : Fin 23) (h : idx.val = 3 := by decide) : (runCycle up_down_counter_5 s env) idx = evalCombinatorial up_down_counter_5 23 s ⟨18, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_5_q_2 (s : State up_down_counter_5) (env : List Bool) (idx : Fin 23) (h : idx.val = 4 := by decide) : (runCycle up_down_counter_5 s env) idx = evalCombinatorial up_down_counter_5 23 s ⟨19, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_5_q_3 (s : State up_down_counter_5) (env : List Bool) (idx : Fin 23) (h : idx.val = 5 := by decide) : (runCycle up_down_counter_5 s env) idx = evalCombinatorial up_down_counter_5 23 s ⟨20, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_up_down_counter_5_q_4 (s : State up_down_counter_5) (env : List Bool) (idx : Fin 23) (h : idx.val = 6 := by decide) : (runCycle up_down_counter_5 s env) idx = evalCombinatorial up_down_counter_5 23 s ⟨22, by decide⟩ := by cases idx; subst h; rfl

instance instIsUpDownCounter_up_down_counter_5 : IsUpDownCounter up_down_counter_5 5 q_bus_up_down_counter_5 incr_up_down_counter_5 decr_up_down_counter_5 where
  widths_match := by decide
  inputs_are_valid := by decide
  count_up := by
    intro s env h_incr h_decr
    have equiv (i : Fin 23) : evalCombinatorial up_down_counter_5 23 s i = evalExpr s (unrollDAG up_down_counter_5 23 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_5, bitsToNat]
    simp only [runCycle_up_down_counter_5_q_0, runCycle_up_down_counter_5_q_1, runCycle_up_down_counter_5_q_2, runCycle_up_down_counter_5_q_3, runCycle_up_down_counter_5_q_4]
    simp only [equiv]
    simp only [ast_up_down_counter_5_next_q_0, ast_up_down_counter_5_next_q_1, ast_up_down_counter_5_next_q_2, ast_up_down_counter_5_next_q_3, ast_up_down_counter_5_next_q_4]
    change s ⟨0, by decide⟩ = true at h_incr
    change s ⟨1, by decide⟩ = false at h_decr
    simp only [h_incr, h_decr]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    generalize h_val_q_4 : s ⟨6, by decide⟩ = val_q_4
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> cases val_q_4 <;> decide
  count_down := by
    intro s env h_incr h_decr
    have equiv (i : Fin 23) : evalCombinatorial up_down_counter_5 23 s i = evalExpr s (unrollDAG up_down_counter_5 23 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_5, bitsToNat]
    simp only [runCycle_up_down_counter_5_q_0, runCycle_up_down_counter_5_q_1, runCycle_up_down_counter_5_q_2, runCycle_up_down_counter_5_q_3, runCycle_up_down_counter_5_q_4]
    simp only [equiv]
    simp only [ast_up_down_counter_5_next_q_0, ast_up_down_counter_5_next_q_1, ast_up_down_counter_5_next_q_2, ast_up_down_counter_5_next_q_3, ast_up_down_counter_5_next_q_4]
    change s ⟨0, by decide⟩ = false at h_incr
    change s ⟨1, by decide⟩ = true at h_decr
    simp only [h_incr, h_decr]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    generalize h_val_q_4 : s ⟨6, by decide⟩ = val_q_4
    cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> cases val_q_4 <;> decide
  hold_on_invalid := by
    intro s env h_eq
    have equiv (i : Fin 23) : evalCombinatorial up_down_counter_5 23 s i = evalExpr s (unrollDAG up_down_counter_5 23 i) := by fin_cases i <;> rfl
    simp only [q_bus_up_down_counter_5, bitsToNat]
    simp only [runCycle_up_down_counter_5_q_0, runCycle_up_down_counter_5_q_1, runCycle_up_down_counter_5_q_2, runCycle_up_down_counter_5_q_3, runCycle_up_down_counter_5_q_4]
    simp only [equiv]
    simp only [ast_up_down_counter_5_next_q_0, ast_up_down_counter_5_next_q_1, ast_up_down_counter_5_next_q_2, ast_up_down_counter_5_next_q_3, ast_up_down_counter_5_next_q_4]
    change s ⟨0, by decide⟩ = s ⟨1, by decide⟩ at h_eq
    generalize h_in : s ⟨1, by decide⟩ = val_in
    rw [h_in] at h_eq
    simp only [h_eq]
    generalize h_val_q_0 : s ⟨2, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨3, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨4, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨5, by decide⟩ = val_q_3
    generalize h_val_q_4 : s ⟨6, by decide⟩ = val_q_4
    cases val_in <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> cases val_q_4 <;> decide

instance instVerifiedUpDownCounter5_up_down_counter_5 : VerifiedUpDownCounter5 up_down_counter_5 q_bus_up_down_counter_5 incr_up_down_counter_5 decr_up_down_counter_5 where
  proof := instIsUpDownCounter_up_down_counter_5

end hdl.examples.counter
