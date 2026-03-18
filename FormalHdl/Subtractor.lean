-- Adam Friesz, Winter 2026
import FormalHdl.Defs
namespace hdl.examples.subtractor
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- COMPONENT: subtractor_gate_1
def subtractor_gate_1_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .not_ false
]
def subtractor_gate_1_conns : List (List Nat) := [
  [],
  [],
  [],
  [2],
  [0],
  [1, 3],
  [1, 3],
  [5, 4],
  [5, 4],
  [6, 8],
  [9]
]
def subtractor_gate_1 : Circuit := { gates := subtractor_gate_1_gates, wiring := mkWiring subtractor_gate_1_gates subtractor_gate_1_conns (by decide), is_dag := by decide }
def a_bus_subtractor_gate_1 : List (Fin 11) := [⟨1, by decide⟩]
def b_bus_subtractor_gate_1 : List (Fin 11) := [⟨2, by decide⟩]
def diff_bus_subtractor_gate_1 : List (Fin 11) := [⟨7, by decide⟩]
def bin_subtractor_gate_1 : Fin 11 := ⟨0, by decide⟩
def bout_subtractor_gate_1 : Fin 11 := ⟨10, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: subtractor_gate_1
@[simp] lemma ast_subtractor_gate_1_bin (s : State subtractor_gate_1) (i : Fin 11) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG subtractor_gate_1 11 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_gate_1_a_0 (s : State subtractor_gate_1) (i : Fin 11) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG subtractor_gate_1 11 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_gate_1_b_0 (s : State subtractor_gate_1) (i : Fin 11) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG subtractor_gate_1 11 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_gate_1_diff_0 (s : State subtractor_gate_1) (i : Fin 11) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG subtractor_gate_1 11 i) = ((s ⟨1, by decide⟩ ^^ !(s ⟨2, by decide⟩)) ^^ !(s ⟨0, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_gate_1_bout (s : State subtractor_gate_1) (i : Fin 11) (hi : i.val = 10 := by decide) : evalExpr s (unrollDAG subtractor_gate_1 11 i) = !(((s ⟨1, by decide⟩ && !(s ⟨2, by decide⟩)) || ((s ⟨1, by decide⟩ ^^ !(s ⟨2, by decide⟩)) && !(s ⟨0, by decide⟩)))) := by cases i; subst hi; rfl

instance instIsSubtractor_subtractor_gate_1 : IsSubtractor subtractor_gate_1 1 a_bus_subtractor_gate_1 b_bus_subtractor_gate_1 diff_bus_subtractor_gate_1 bin_subtractor_gate_1 bout_subtractor_gate_1 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  sub_correct := by
    intro s
    have equiv (i : Fin 11) : evalCombinatorial subtractor_gate_1 subtractor_gate_1.gates.length s i = evalExpr s (unrollDAG subtractor_gate_1 11 i) := by fin_cases i <;> rfl
    simp only [a_bus_subtractor_gate_1, b_bus_subtractor_gate_1, diff_bus_subtractor_gate_1, bout_subtractor_gate_1, bin_subtractor_gate_1, bitsToNat]
    simp only [equiv]
    simp only [ast_subtractor_gate_1_bin, ast_subtractor_gate_1_a_0, ast_subtractor_gate_1_b_0, ast_subtractor_gate_1_diff_0, ast_subtractor_gate_1_bout]
    generalize h_bin : s ⟨0, by decide⟩ = bin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    cases bin <;> cases a_0 <;> cases b_0 <;> decide

instance instVerifiedSubtractor1_subtractor_gate_1 : VerifiedSubtractor1 subtractor_gate_1 a_bus_subtractor_gate_1 b_bus_subtractor_gate_1 diff_bus_subtractor_gate_1 bin_subtractor_gate_1 bout_subtractor_gate_1 where
  proof := instIsSubtractor_subtractor_gate_1

-- COMPONENT: subtractor_hier_2
def subtractor_hier_2_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk (.adder_2 ⟨0, by decide⟩) false,
  Gate.mk (.adder_2 ⟨1, by decide⟩) false,
  Gate.mk (.adder_2 ⟨2, by decide⟩) false,
  Gate.mk .not_ false
]
def subtractor_hier_2_conns : List (List Nat) := [
  [],
  [],
  [],
  [2],
  [],
  [],
  [5],
  [0],
  [7, 1, 4, 3, 6],
  [7, 1, 4, 3, 6],
  [7, 1, 4, 3, 6],
  [10]
]
def subtractor_hier_2 : Circuit := { gates := subtractor_hier_2_gates, wiring := mkWiring subtractor_hier_2_gates subtractor_hier_2_conns (by decide), is_dag := by decide }
def a_bus_subtractor_hier_2 : List (Fin 12) := [⟨1, by decide⟩, ⟨4, by decide⟩]
def b_bus_subtractor_hier_2 : List (Fin 12) := [⟨2, by decide⟩, ⟨5, by decide⟩]
def diff_bus_subtractor_hier_2 : List (Fin 12) := [⟨8, by decide⟩, ⟨9, by decide⟩]
def bin_subtractor_hier_2 : Fin 12 := ⟨0, by decide⟩
def bout_subtractor_hier_2 : Fin 12 := ⟨11, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: subtractor_hier_2
@[simp] lemma ast_subtractor_hier_2_bin (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_a_0 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_b_0 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_a_1 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_b_1 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_diff_0 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = (compute_adder_2 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_diff_1 (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 9 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = (compute_adder_2 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_2_bout (s : State subtractor_hier_2) (i : Fin 12) (hi : i.val = 11 := by decide) : evalExpr s (unrollDAG subtractor_hier_2 12 i) = !((compute_adder_2 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩))).testBit 2) := by cases i; subst hi; rfl

instance instIsSubtractor_subtractor_hier_2 : IsSubtractor subtractor_hier_2 2 a_bus_subtractor_hier_2 b_bus_subtractor_hier_2 diff_bus_subtractor_hier_2 bin_subtractor_hier_2 bout_subtractor_hier_2 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  sub_correct := by
    intro s
    have equiv (i : Fin 12) : evalCombinatorial subtractor_hier_2 subtractor_hier_2.gates.length s i = evalExpr s (unrollDAG subtractor_hier_2 12 i) := by fin_cases i <;> rfl
    simp only [a_bus_subtractor_hier_2, b_bus_subtractor_hier_2, diff_bus_subtractor_hier_2, bout_subtractor_hier_2, bin_subtractor_hier_2, bitsToNat]
    simp only [equiv]
    simp only [ast_subtractor_hier_2_bin, ast_subtractor_hier_2_a_0, ast_subtractor_hier_2_b_0, ast_subtractor_hier_2_a_1, ast_subtractor_hier_2_b_1, ast_subtractor_hier_2_diff_0, ast_subtractor_hier_2_diff_1, ast_subtractor_hier_2_bout]
    generalize h_bin : s ⟨0, by decide⟩ = bin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨4, by decide⟩ = a_1
    generalize h_b_1 : s ⟨5, by decide⟩ = b_1
    cases bin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> decide

instance instVerifiedSubtractor2_subtractor_hier_2 : VerifiedSubtractor2 subtractor_hier_2 a_bus_subtractor_hier_2 b_bus_subtractor_hier_2 diff_bus_subtractor_hier_2 bin_subtractor_hier_2 bout_subtractor_hier_2 where
  proof := instIsSubtractor_subtractor_hier_2

-- COMPONENT: subtractor_hier_4
def subtractor_hier_4_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk (.adder_4 ⟨0, by decide⟩) false,
  Gate.mk (.adder_4 ⟨1, by decide⟩) false,
  Gate.mk (.adder_4 ⟨2, by decide⟩) false,
  Gate.mk (.adder_4 ⟨3, by decide⟩) false,
  Gate.mk (.adder_4 ⟨4, by decide⟩) false,
  Gate.mk .not_ false
]
def subtractor_hier_4_conns : List (List Nat) := [
  [],
  [],
  [],
  [2],
  [],
  [],
  [5],
  [],
  [],
  [8],
  [],
  [],
  [11],
  [0],
  [13, 1, 4, 7, 10, 3, 6, 9, 12],
  [13, 1, 4, 7, 10, 3, 6, 9, 12],
  [13, 1, 4, 7, 10, 3, 6, 9, 12],
  [13, 1, 4, 7, 10, 3, 6, 9, 12],
  [13, 1, 4, 7, 10, 3, 6, 9, 12],
  [18]
]
def subtractor_hier_4 : Circuit := { gates := subtractor_hier_4_gates, wiring := mkWiring subtractor_hier_4_gates subtractor_hier_4_conns (by decide), is_dag := by decide }
def a_bus_subtractor_hier_4 : List (Fin 20) := [⟨1, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩]
def b_bus_subtractor_hier_4 : List (Fin 20) := [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩]
def diff_bus_subtractor_hier_4 : List (Fin 20) := [⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩]
def bin_subtractor_hier_4 : Fin 20 := ⟨0, by decide⟩
def bout_subtractor_hier_4 : Fin 20 := ⟨19, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: subtractor_hier_4
@[simp] lemma ast_subtractor_hier_4_bin (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_a_0 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_b_0 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_a_1 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_b_1 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_a_2 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨7, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_b_2 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨8, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_a_3 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 10 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨10, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_b_3 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 11 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = s ⟨11, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_diff_0 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 14 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = (compute_adder_4 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (s ⟨7, by decide⟩) (s ⟨10, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨8, by decide⟩)) (!(s ⟨11, by decide⟩))).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_diff_1 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 15 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = (compute_adder_4 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (s ⟨7, by decide⟩) (s ⟨10, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨8, by decide⟩)) (!(s ⟨11, by decide⟩))).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_diff_2 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 16 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = (compute_adder_4 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (s ⟨7, by decide⟩) (s ⟨10, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨8, by decide⟩)) (!(s ⟨11, by decide⟩))).testBit 2 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_diff_3 (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = (compute_adder_4 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (s ⟨7, by decide⟩) (s ⟨10, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨8, by decide⟩)) (!(s ⟨11, by decide⟩))).testBit 3 := by cases i; subst hi; rfl
@[simp] lemma ast_subtractor_hier_4_bout (s : State subtractor_hier_4) (i : Fin 20) (hi : i.val = 19 := by decide) : evalExpr s (unrollDAG subtractor_hier_4 20 i) = !((compute_adder_4 (!(s ⟨0, by decide⟩)) (s ⟨1, by decide⟩) (s ⟨4, by decide⟩) (s ⟨7, by decide⟩) (s ⟨10, by decide⟩) (!(s ⟨2, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨8, by decide⟩)) (!(s ⟨11, by decide⟩))).testBit 4) := by cases i; subst hi; rfl

instance instIsSubtractor_subtractor_hier_4 : IsSubtractor subtractor_hier_4 4 a_bus_subtractor_hier_4 b_bus_subtractor_hier_4 diff_bus_subtractor_hier_4 bin_subtractor_hier_4 bout_subtractor_hier_4 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  sub_correct := by
    intro s
    have equiv (i : Fin 20) : evalCombinatorial subtractor_hier_4 subtractor_hier_4.gates.length s i = evalExpr s (unrollDAG subtractor_hier_4 20 i) := by fin_cases i <;> rfl
    simp only [a_bus_subtractor_hier_4, b_bus_subtractor_hier_4, diff_bus_subtractor_hier_4, bout_subtractor_hier_4, bin_subtractor_hier_4, bitsToNat]
    simp only [equiv]
    simp only [ast_subtractor_hier_4_bin, ast_subtractor_hier_4_a_0, ast_subtractor_hier_4_b_0, ast_subtractor_hier_4_a_1, ast_subtractor_hier_4_b_1, ast_subtractor_hier_4_a_2, ast_subtractor_hier_4_b_2, ast_subtractor_hier_4_a_3, ast_subtractor_hier_4_b_3, ast_subtractor_hier_4_diff_0, ast_subtractor_hier_4_diff_1, ast_subtractor_hier_4_diff_2, ast_subtractor_hier_4_diff_3, ast_subtractor_hier_4_bout]
    generalize h_bin : s ⟨0, by decide⟩ = bin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨4, by decide⟩ = a_1
    generalize h_b_1 : s ⟨5, by decide⟩ = b_1
    generalize h_a_2 : s ⟨7, by decide⟩ = a_2
    generalize h_b_2 : s ⟨8, by decide⟩ = b_2
    generalize h_a_3 : s ⟨10, by decide⟩ = a_3
    generalize h_b_3 : s ⟨11, by decide⟩ = b_3
    cases bin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> cases a_2 <;> cases b_2 <;> cases a_3 <;> cases b_3 <;> decide

instance instVerifiedSubtractor4_subtractor_hier_4 : VerifiedSubtractor4 subtractor_hier_4 a_bus_subtractor_hier_4 b_bus_subtractor_hier_4 diff_bus_subtractor_hier_4 bin_subtractor_hier_4 bout_subtractor_hier_4 where
  proof := instIsSubtractor_subtractor_hier_4

end hdl.examples.subtractor
