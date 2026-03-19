-- Adam Friesz, Winter 2026
import FormalHdl.Defs

namespace hdl.examples.parking_lot
open hdl

set_option linter.style.longLine false
set_option linter.style.whitespace false

-- ==========================================
-- 1. The Mathematical FSM Model
-- ==========================================

/-- Descriptive states replacing the generic A-I Verilog states -/
inductive SensorState
  | idle            -- A: 000
  | entering_outer  -- B: 001
  | entering_both   -- C: 011
  | entering_inner  -- D: 010
  | exiting_inner   -- G: 101
  | exiting_both    -- H: 110
  | exiting_outer   -- I: 100
  deriving Repr, DecidableEq

/-- The Next State transition logic based on the Verilog always_comb block -/
def next_sensor_state (state : SensorState) (outer inner : Bool) : SensorState :=
  match state, outer, inner with
  -- A: Idle
  | .idle, false, false => .idle
  | .idle, true, false  => .entering_outer
  | .idle, false, true  => .exiting_inner
  -- B, C, D: Entering Sequence
  | .entering_outer, true, false => .entering_outer
  | .entering_outer, true, true  => .entering_both
  | .entering_both,  true, true  => .entering_both
  | .entering_both,  false, true => .entering_inner
  | .entering_inner, false, true => .entering_inner
  | .entering_inner, false, false => .idle
  -- I, H, G: Exiting Sequence
  | .exiting_inner, false, true  => .exiting_inner
  | .exiting_inner, true, true   => .exiting_both
  | .exiting_both,  true, true   => .exiting_both
  | .exiting_both,  true, false  => .exiting_outer
  | .exiting_outer, true, false  => .exiting_outer
  | .exiting_outer, false, false => .idle
  -- Any other sequence immediately resets to Idle
  | _, _, _ => .idle

/-- Combinational logic for the 'enter' pulse -/
def is_enter (state : SensorState) (outer inner : Bool) : Bool :=
  state == .entering_inner && !outer && !inner

/-- Combinational logic for the 'exit' pulse -/
def is_exit (state : SensorState) (outer inner : Bool) : Bool :=
  state == .exiting_outer && !outer && !inner


-- ==========================================
-- 2. System Level Lot State
-- ==========================================

structure LotState where
  occupancy : Nat
  sensor : SensorState

/-- Decodes the 3-bit hardware state into the mathematical SensorState -/
def decode_sensor_state {C : Circuit} (s : State C) (ps2 ps1 ps0 : Fin C.gates.length) : SensorState :=
  match s ps2, s ps1, s ps0 with
  | false, false, false => .idle           -- 000 (A)
  | false, false, true  => .entering_outer -- 001 (B)
  | false, true,  false => .entering_inner -- 010 (D)
  | false, true,  true  => .entering_both  -- 011 (C)
  | true,  false, false => .exiting_outer  -- 100 (I)
  | true,  false, true  => .exiting_inner  -- 101 (G)
  | true,  true,  false => .exiting_both   -- 110 (H)
  | true,  true,  true  => .error          -- 111 (F)

-- ==========================================
-- 3. The Formal Contract (IsParkingLotCounter)
-- ==========================================

class IsParkingLotCounter (C : Circuit)
  (outer inner : Fin C.gates.length)
  (fsm_ps2 fsm_ps1 fsm_ps0 : Fin C.gates.length)
  (occupancy_bus : List (Fin C.gates.length))
  (full empty : Fin C.gates.length)
  (enter_wire exit_wire : Fin C.gates.length) : Prop where

  widths_match : occupancy_bus.length = 4
  inputs_are_valid : (C.gates.get outer).kind.ni = 0 ∧ (C.gates.get inner).kind.ni = 0

  -- 1. Combinational Status Properties (Outputs evaluated instantly)
  status_full : ∀ (s : State C),
    let stable_s := evalCombinatorial C C.gates.length s
    stable_s full = (bitsToNat stable_s occupancy_bus == 8)

  status_empty : ∀ (s : State C),
    let stable_s := evalCombinatorial C C.gates.length s
    stable_s empty = (bitsToNat stable_s occupancy_bus == 0)

  -- 2. Output Pulse Properties (enter/exit signals)
  -- Assuming decode_sensor_state maps the circuit's flip-flops to our SensorState enum
  pulses_correct : ∀ (s : State C),
    let stable_s := evalCombinatorial C C.gates.length s
    let math_state := decode_sensor_state s fsm_ps2 fsm_ps1 fsm_ps0
    let math_outer := stable_s outer
    let math_inner := stable_s inner
    (stable_s enter_wire = is_enter math_state math_outer math_inner) ∧
    (stable_s exit_wire = is_exit math_state math_outer math_inner)

  -- 3. Sequential Transition Property (runCycle paradigm)
  valid_transition : ∀ (s : State C) (env_outer env_inner : Bool),
    let current_math_state := decode_sensor_state s fsm_ps2 fsm_ps1 fsm_ps0
    let current_occupancy := bitsToNat s occupancy_bus
    let next_s := runCycle C s [env_outer, env_inner]
    let next_math_state := decode_sensor_state next_s fsm_ps2 fsm_ps1 fsm_ps0
    let next_occupancy := bitsToNat next_s occupancy_bus
    -- Verify FSM advances correctly
    (next_math_state = next_sensor_state current_math_state env_outer env_inner) ∧
    -- Verify Counter respects FSM pulses and capacity limits
    (if is_enter current_math_state env_outer env_inner then
      next_occupancy = min 8 (current_occupancy + 1)
    else if is_exit current_math_state env_outer env_inner then
      next_occupancy = current_occupancy - 1 -- Note: Nat subtraction naturally floors at 0 in Lean!
    else
      next_occupancy = current_occupancy)

-- Generated Code
-- COMPONENT: parking_lot
def parking_lot_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .dff false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk (.decoder_3 ⟨0, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨1, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨2, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨3, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨4, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨5, by decide⟩) false,
  Gate.mk (.decoder_3 ⟨6, by decide⟩) false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk (.up_down_count_4 ⟨0, by decide⟩) false,
  Gate.mk (.up_down_count_4 ⟨1, by decide⟩) false,
  Gate.mk (.up_down_count_4 ⟨2, by decide⟩) false,
  Gate.mk (.up_down_count_4 ⟨3, by decide⟩) false,
  Gate.mk .and_ false,
  Gate.mk .not_ false,
  Gate.mk .comp_4 false,
  Gate.mk .comp_4 false,
  Gate.mk .not_ false
]
def parking_lot_conns : List (List Nat) := [
  [],
  [],
  [41],
  [43],
  [45],
  [48],
  [49],
  [50],
  [51],
  [0],
  [1],
  [2, 3, 4],
  [2, 3, 4],
  [2, 3, 4],
  [2, 3, 4],
  [2, 3, 4],
  [2, 3, 4],
  [2, 3, 4],
  [9, 10],
  [0, 10],
  [9, 1],
  [0, 1],
  [11, 19],
  [12, 19],
  [22, 23],
  [12, 21],
  [14, 21],
  [25, 26],
  [14, 20],
  [13, 20],
  [28, 29],
  [11, 20],
  [16, 20],
  [31, 32],
  [16, 21],
  [17, 21],
  [34, 35],
  [17, 19],
  [15, 19],
  [37, 38],
  [24, 27],
  [40, 33],
  [30, 27],
  [42, 36],
  [39, 33],
  [44, 36],
  [13, 18],
  [15, 18],
  [46, 47, 5, 6, 7, 8],
  [46, 47, 5, 6, 7, 8],
  [46, 47, 5, 6, 7, 8],
  [46, 47, 5, 6, 7, 8],
  [46, 47],
  [52],
  [5, 6, 7, 8, 53, 52, 52, 52],
  [5, 6, 7, 8, 52, 52, 52, 53],
  [55]
]
def parking_lot : Circuit := { gates := parking_lot_gates, wiring := mkWiring parking_lot_gates parking_lot_conns (by decide), is_dag := by decide }
def occupancy_bus_parking_lot : List (Fin 57) := [⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]
def full_parking_lot : Fin 57 := ⟨56, by decide⟩
def empty_parking_lot : Fin 57 := ⟨54, by decide⟩
def enter_parking_lot : Fin 57 := ⟨46, by decide⟩
def exit_parking_lot : Fin 57 := ⟨47, by decide⟩
def outer_parking_lot : Fin 57 := ⟨0, by decide⟩
def inner_parking_lot : Fin 57 := ⟨1, by decide⟩

-- ==========================================
-- AST BOUNDARY LEMMAS & PROOF: parking_lot
-- ==========================================

@[simp] lemma ast_parking_lot_outer (s : State parking_lot) (i : Fin 57) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_inner (s : State parking_lot) (i : Fin 57) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ps_0 (s : State parking_lot) (i : Fin 57) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ps_1 (s : State parking_lot) (i : Fin 57) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ps_2 (s : State parking_lot) (i : Fin 57) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_q_0 (s : State parking_lot) (i : Fin 57) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_q_1 (s : State parking_lot) (i : Fin 57) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_q_2 (s : State parking_lot) (i : Fin 57) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨7, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_q_3 (s : State parking_lot) (i : Fin 57) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = s ⟨8, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ns_0 (s : State parking_lot) (i : Fin 57) (hi : i.val = 41 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = (((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 0) && ((s ⟨0, by decide⟩) && !((s ⟨1, by decide⟩)))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 1) && ((s ⟨0, by decide⟩) && !((s ⟨1, by decide⟩))))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 1) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 3) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 0) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 5) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩))))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ns_1 (s : State parking_lot) (i : Fin 57) (hi : i.val = 43 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = (((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 3) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩)))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 1) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 3) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 5) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 6) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_fsm_ns_2 (s : State parking_lot) (i : Fin 57) (hi : i.val = 45 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = (((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 6) && ((s ⟨0, by decide⟩) && !((s ⟨1, by decide⟩)))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && ((s ⟨0, by decide⟩) && !((s ⟨1, by decide⟩))))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 0) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 5) && (!((s ⟨0, by decide⟩)) && (s ⟨1, by decide⟩))))) || (((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 5) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))) || ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 6) && ((s ⟨0, by decide⟩) && (s ⟨1, by decide⟩))))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_next_q_0 (s : State parking_lot) (i : Fin 57) (hi : i.val = 48 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 1) % 16 else if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 15) % 16 else ((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_next_q_1 (s : State parking_lot) (i : Fin 57) (hi : i.val = 49 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 1) % 16 else if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 15) % 16 else ((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_next_q_2 (s : State parking_lot) (i : Fin 57) (hi : i.val = 50 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 1) % 16 else if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 15) % 16 else ((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_next_q_3 (s : State parking_lot) (i : Fin 57) (hi : i.val = 51 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 1) % 16 else if ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && !(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))) then (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) + 15) % 16 else ((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat))).testBit 3 := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_enter (s : State parking_lot) (i : Fin 57) (hi : i.val = 46 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_exit (s : State parking_lot) (i : Fin 57) (hi : i.val = 47 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_full (s : State parking_lot) (i : Fin 57) (hi : i.val = 56 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = !((((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) < ((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat + 2*(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat + 4*(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat + 8*!((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))))).toNat))) := by cases i; subst hi; rfl
@[simp] lemma ast_parking_lot_empty (s : State parking_lot) (i : Fin 57) (hi : i.val = 54 := by decide) : evalExpr s (unrollDAG parking_lot 57 i) = (((s ⟨5, by decide⟩).toNat + 2*(s ⟨6, by decide⟩).toNat + 4*(s ⟨7, by decide⟩).toNat + 8*(s ⟨8, by decide⟩).toNat) < (!((((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))))).toNat + 2*(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat + 4*(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat + 8*(((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 2) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩)))) && ((((s ⟨2, by decide⟩).toNat + 2*(s ⟨3, by decide⟩).toNat + 4*(s ⟨4, by decide⟩).toNat) == 4) && (!((s ⟨0, by decide⟩)) && !((s ⟨1, by decide⟩))))).toNat)) := by cases i; subst hi; rfl
@[simp] lemma runCycle_parking_lot_fsm_ps_0 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 2 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨41, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_fsm_ps_1 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 3 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨43, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_fsm_ps_2 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 4 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨45, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_q_0 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 5 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨48, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_q_1 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 6 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨49, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_q_2 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 7 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨50, by decide⟩ := by cases idx; subst h; rfl
@[simp] lemma runCycle_parking_lot_q_3 (s : State parking_lot) (env : List Bool) (idx : Fin 57) (h : idx.val = 8 := by decide) : (runCycle parking_lot s env) idx = evalCombinatorial parking_lot 57 s ⟨51, by decide⟩ := by cases idx; subst h; rfl

instance instIsParkingLotCounter_parking_lot : IsParkingLotCounter parking_lot
  outer_parking_lot inner_parking_lot
  ⟨4, by decide⟩ ⟨3, by decide⟩ ⟨2, by decide⟩
  occupancy_bus_parking_lot full_parking_lot empty_parking_lot
  enter_parking_lot exit_parking_lot where
  widths_match := by decide
  inputs_are_valid := by decide
  status_full := by
    intro s
    have equiv (i : Fin 57) : evalCombinatorial parking_lot 57 s i = evalExpr s (unrollDAG parking_lot 57 i) := by fin_cases i <;> rfl
    simp only [decode_sensor_state, is_enter, is_exit, next_sensor_state]
    simp only [occupancy_bus_parking_lot, full_parking_lot, empty_parking_lot, enter_parking_lot, exit_parking_lot, outer_parking_lot, inner_parking_lot, bitsToNat]
    simp only [equiv]
    simp only [ast_parking_lot_fsm_ns_0, ast_parking_lot_fsm_ns_1, ast_parking_lot_fsm_ns_2, ast_parking_lot_next_q_0, ast_parking_lot_next_q_1, ast_parking_lot_next_q_2, ast_parking_lot_next_q_3, ast_parking_lot_enter, ast_parking_lot_exit, ast_parking_lot_full, ast_parking_lot_empty]
    generalize h_val_outer : s ⟨0, by decide⟩ = val_outer
    generalize h_val_inner : s ⟨1, by decide⟩ = val_inner
    generalize h_val_fsm_ps_0 : s ⟨2, by decide⟩ = val_fsm_ps_0
    generalize h_val_fsm_ps_1 : s ⟨3, by decide⟩ = val_fsm_ps_1
    generalize h_val_fsm_ps_2 : s ⟨4, by decide⟩ = val_fsm_ps_2
    generalize h_val_q_0 : s ⟨5, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨6, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨7, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨8, by decide⟩ = val_q_3
    cases val_outer <;> cases val_inner <;> cases val_fsm_ps_0 <;> cases val_fsm_ps_1 <;> cases val_fsm_ps_2 <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  status_empty := by
    intro s
    have equiv (i : Fin 57) : evalCombinatorial parking_lot 57 s i = evalExpr s (unrollDAG parking_lot 57 i) := by fin_cases i <;> rfl
    simp only [decode_sensor_state, is_enter, is_exit, next_sensor_state]
    simp only [occupancy_bus_parking_lot, full_parking_lot, empty_parking_lot, enter_parking_lot, exit_parking_lot, outer_parking_lot, inner_parking_lot, bitsToNat]
    simp only [equiv]
    simp only [ast_parking_lot_fsm_ns_0, ast_parking_lot_fsm_ns_1, ast_parking_lot_fsm_ns_2, ast_parking_lot_next_q_0, ast_parking_lot_next_q_1, ast_parking_lot_next_q_2, ast_parking_lot_next_q_3, ast_parking_lot_enter, ast_parking_lot_exit, ast_parking_lot_full, ast_parking_lot_empty]
    generalize h_val_outer : s ⟨0, by decide⟩ = val_outer
    generalize h_val_inner : s ⟨1, by decide⟩ = val_inner
    generalize h_val_fsm_ps_0 : s ⟨2, by decide⟩ = val_fsm_ps_0
    generalize h_val_fsm_ps_1 : s ⟨3, by decide⟩ = val_fsm_ps_1
    generalize h_val_fsm_ps_2 : s ⟨4, by decide⟩ = val_fsm_ps_2
    generalize h_val_q_0 : s ⟨5, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨6, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨7, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨8, by decide⟩ = val_q_3
    cases val_outer <;> cases val_inner <;> cases val_fsm_ps_0 <;> cases val_fsm_ps_1 <;> cases val_fsm_ps_2 <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  pulses_correct := by
    intro s
    have equiv (i : Fin 57) : evalCombinatorial parking_lot 57 s i = evalExpr s (unrollDAG parking_lot 57 i) := by fin_cases i <;> rfl
    simp only [decode_sensor_state, is_enter, is_exit, next_sensor_state]
    simp only [occupancy_bus_parking_lot, full_parking_lot, empty_parking_lot, enter_parking_lot, exit_parking_lot, outer_parking_lot, inner_parking_lot, bitsToNat]
    simp only [equiv]
    simp only [ast_parking_lot_fsm_ns_0, ast_parking_lot_fsm_ns_1, ast_parking_lot_fsm_ns_2, ast_parking_lot_next_q_0, ast_parking_lot_next_q_1, ast_parking_lot_next_q_2, ast_parking_lot_next_q_3, ast_parking_lot_enter, ast_parking_lot_exit, ast_parking_lot_full, ast_parking_lot_empty]
    generalize h_val_outer : s ⟨0, by decide⟩ = val_outer
    generalize h_val_inner : s ⟨1, by decide⟩ = val_inner
    generalize h_val_fsm_ps_0 : s ⟨2, by decide⟩ = val_fsm_ps_0
    generalize h_val_fsm_ps_1 : s ⟨3, by decide⟩ = val_fsm_ps_1
    generalize h_val_fsm_ps_2 : s ⟨4, by decide⟩ = val_fsm_ps_2
    generalize h_val_q_0 : s ⟨5, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨6, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨7, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨8, by decide⟩ = val_q_3
    cases val_outer <;> cases val_inner <;> cases val_fsm_ps_0 <;> cases val_fsm_ps_1 <;> cases val_fsm_ps_2 <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> decide
  valid_transition := by
    intro s env_outer env_inner
    have equiv (i : Fin 57) : evalCombinatorial parking_lot 57 s i = evalExpr s (unrollDAG parking_lot 57 i) := by fin_cases i <;> rfl
    simp only [decode_sensor_state, is_enter, is_exit, next_sensor_state]
    simp only [occupancy_bus_parking_lot, full_parking_lot, empty_parking_lot, enter_parking_lot, exit_parking_lot, outer_parking_lot, inner_parking_lot, bitsToNat]
    simp only [runCycle_parking_lot_fsm_ps_0, runCycle_parking_lot_fsm_ps_1, runCycle_parking_lot_fsm_ps_2, runCycle_parking_lot_q_0, runCycle_parking_lot_q_1, runCycle_parking_lot_q_2, runCycle_parking_lot_q_3]
    simp only [equiv]
    simp only [ast_parking_lot_fsm_ns_0, ast_parking_lot_fsm_ns_1, ast_parking_lot_fsm_ns_2, ast_parking_lot_next_q_0, ast_parking_lot_next_q_1, ast_parking_lot_next_q_2, ast_parking_lot_next_q_3, ast_parking_lot_enter, ast_parking_lot_exit, ast_parking_lot_full, ast_parking_lot_empty]
    generalize h_val_outer : s ⟨0, by decide⟩ = val_outer
    generalize h_val_inner : s ⟨1, by decide⟩ = val_inner
    generalize h_val_fsm_ps_0 : s ⟨2, by decide⟩ = val_fsm_ps_0
    generalize h_val_fsm_ps_1 : s ⟨3, by decide⟩ = val_fsm_ps_1
    generalize h_val_fsm_ps_2 : s ⟨4, by decide⟩ = val_fsm_ps_2
    generalize h_val_q_0 : s ⟨5, by decide⟩ = val_q_0
    generalize h_val_q_1 : s ⟨6, by decide⟩ = val_q_1
    generalize h_val_q_2 : s ⟨7, by decide⟩ = val_q_2
    generalize h_val_q_3 : s ⟨8, by decide⟩ = val_q_3
    cases val_outer <;> cases val_inner <;> cases val_fsm_ps_0 <;> cases val_fsm_ps_1 <;> cases val_fsm_ps_2 <;> cases val_q_0 <;> cases val_q_1 <;> cases val_q_2 <;> cases val_q_3 <;> cases env_outer <;> cases env_inner <;> decide

end hdl.examples.parking_lot
