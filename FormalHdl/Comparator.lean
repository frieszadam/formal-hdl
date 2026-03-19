-- Adam Friesz, Winter 2026
import FormalHdl.Defs
namespace hdl.examples.comparator
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- COMPONENT: comparator_gate_4
def comparator_gate_4_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk .not_ false,
  Gate.mk (.adder_4 ⟨4, by decide⟩) false,
  Gate.mk .not_ false
]
def comparator_gate_4_conns : List (List Nat) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [0],
  [0, 8],
  [9],
  [4],
  [5],
  [6],
  [7],
  [10, 0, 1, 2, 3, 11, 12, 13, 14],
  [15]
]
def comparator_gate_4 : Circuit := { gates := comparator_gate_4_gates, wiring := mkWiring comparator_gate_4_gates comparator_gate_4_conns (by decide), is_dag := by decide }
def a_bus_comparator_gate_4 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
def b_bus_comparator_gate_4 : List (Fin 17) := [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]
def out_comparator_gate_4 : Fin 17 := ⟨16, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: comparator_gate_4
@[simp] lemma ast_comparator_gate_4_a_0 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_a_1 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_a_2 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_a_3 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_b_0 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_b_1 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_b_2 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_b_3 (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = s ⟨7, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_comparator_gate_4_out (s : State comparator_gate_4) (i : Fin 17) (hi : i.val = 16 := by decide) : evalExpr s (unrollDAG comparator_gate_4 17 i) = !((compute_adder_4 (!((s ⟨0, by decide⟩ && !(s ⟨0, by decide⟩)))) (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨2, by decide⟩) (s ⟨3, by decide⟩) (!(s ⟨4, by decide⟩)) (!(s ⟨5, by decide⟩)) (!(s ⟨6, by decide⟩)) (!(s ⟨7, by decide⟩))).testBit 4) := by cases i; subst hi; rfl

instance instIsComp_comparator_gate_4 : IsComparator comparator_gate_4 4 a_bus_comparator_gate_4 b_bus_comparator_gate_4 out_comparator_gate_4 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  comp_correct := by
    intro s
    have equiv (i : Fin 17) : evalCombinatorial comparator_gate_4 comparator_gate_4.gates.length s i = evalExpr s (unrollDAG comparator_gate_4 17 i) := by fin_cases i <;> rfl
    simp only [a_bus_comparator_gate_4, b_bus_comparator_gate_4, out_comparator_gate_4, bitsToNat]
    simp only [equiv]
    simp only [ast_comparator_gate_4_a_0, ast_comparator_gate_4_a_1, ast_comparator_gate_4_a_2, ast_comparator_gate_4_a_3, ast_comparator_gate_4_b_0, ast_comparator_gate_4_b_1, ast_comparator_gate_4_b_2, ast_comparator_gate_4_b_3, ast_comparator_gate_4_out]
    generalize h_a_0 : s ⟨0, by decide⟩ = a_0
    generalize h_a_1 : s ⟨1, by decide⟩ = a_1
    generalize h_a_2 : s ⟨2, by decide⟩ = a_2
    generalize h_a_3 : s ⟨3, by decide⟩ = a_3
    generalize h_b_0 : s ⟨4, by decide⟩ = b_0
    generalize h_b_1 : s ⟨5, by decide⟩ = b_1
    generalize h_b_2 : s ⟨6, by decide⟩ = b_2
    generalize h_b_3 : s ⟨7, by decide⟩ = b_3
    cases a_0 <;> cases a_1 <;> cases a_2 <;> cases a_3 <;> cases b_0 <;> cases b_1 <;> cases b_2 <;> cases b_3 <;> decide

end hdl.examples.comparator
