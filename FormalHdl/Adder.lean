-- FormalHDL — Verified Adder Components
-- Adam Friesz, Winter 2026
--
-- Three adder designs are proved correct against `IsAdder`:
--
--   adder_rca_1          — 1-bit ripple-carry full adder (gate-level XOR/AND/OR)
--   adder_hierarchical_2 — 2-bit adder composed of two adder_1 cells
--   adder_hierarchical_4 — 4-bit adder composed of two adder_2 cells
--   adder_cla_2          — 2-bit carry-lookahead adder (flat gate-level)
--
-- All proofs follow the same four-step recipe (see Defs.lean §5):
--   1. Establish the unroll equivalence by `fin_cases i <;> rfl`.
--   2. Apply `@[simp]` boundary lemmas to rewrite circuit nodes to Bool exprs.
--   3. Generalise each input bit to a fresh variable.
--   4. Exhaust all 2^k input combinations with `decide`.

import FormalHdl.Defs
namespace hdl.examples.adder
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- ============================================================
-- COMPONENT: adder_rca_1
-- A standard 1-bit full adder: XOR for sum, AND/OR for carry.
-- ============================================================
def adder_rca_1_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false
]
def adder_rca_1_conns : List (List Nat) := [
  [],
  [],
  [],
  [1, 2],
  [1, 2],
  [3, 0],
  [3, 0],
  [4, 6]
]
def adder_rca_1 : Circuit := { gates := adder_rca_1_gates, wiring := mkWiring adder_rca_1_gates adder_rca_1_conns (by decide), is_dag := by decide }
def a_bus_adder_rca_1 : List (Fin 8) := [⟨1, by decide⟩]
def b_bus_adder_rca_1 : List (Fin 8) := [⟨2, by decide⟩]
def sum_bus_adder_rca_1 : List (Fin 8) := [⟨5, by decide⟩]
def cin_adder_rca_1 : Fin 8 := ⟨0, by decide⟩
def cout_adder_rca_1 : Fin 8 := ⟨7, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: adder_rca_1
@[simp] lemma ast_adder_rca_1_cin (s : State adder_rca_1) (i : Fin 8) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_rca_1 8 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_1_a_0 (s : State adder_rca_1) (i : Fin 8) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_rca_1 8 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_1_b_0 (s : State adder_rca_1) (i : Fin 8) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_rca_1 8 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_1_sum_0 (s : State adder_rca_1) (i : Fin 8) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG adder_rca_1 8 i) = ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) ^^ s ⟨0, by decide⟩) := by cases i; subst hi; rfl
@[simp] lemma ast_adder_rca_1_cout (s : State adder_rca_1) (i : Fin 8) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG adder_rca_1 8 i) = ((s ⟨1, by decide⟩ && s ⟨2, by decide⟩) || ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) && s ⟨0, by decide⟩)) := by cases i; subst hi; rfl

instance instIsAdder_adder_rca_1 : IsAdder adder_rca_1 1 a_bus_adder_rca_1 b_bus_adder_rca_1 sum_bus_adder_rca_1 cin_adder_rca_1 cout_adder_rca_1 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 8) : evalCombinatorial adder_rca_1 adder_rca_1.gates.length s i = evalExpr s (unrollDAG adder_rca_1 8 i) := by fin_cases i <;> rfl
    simp only [a_bus_adder_rca_1, b_bus_adder_rca_1, sum_bus_adder_rca_1, cout_adder_rca_1, cin_adder_rca_1, bitsToNat]
    simp only [equiv]
    simp only [ast_adder_rca_1_cin, ast_adder_rca_1_a_0, ast_adder_rca_1_b_0, ast_adder_rca_1_sum_0, ast_adder_rca_1_cout]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    cases cin <;> cases a_0 <;> cases b_0 <;> decide

instance instVerifiedAdder1_adder_rca_1 : VerifiedAdder1 adder_rca_1 a_bus_adder_rca_1 b_bus_adder_rca_1 sum_bus_adder_rca_1 cin_adder_rca_1 cout_adder_rca_1 where
  proof := instIsAdder_adder_rca_1

-- ============================================================
-- COMPONENT: adder_hierarchical_2
-- 2-bit adder built from two adder_1 standard cells connected in ripple-carry style.
-- ============================================================
def adder_hierarchical_2_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk (.adder_1 ⟨0, by decide⟩) false,
  Gate.mk (.adder_1 ⟨1, by decide⟩) false,
  Gate.mk (.adder_1 ⟨0, by decide⟩) false,
  Gate.mk (.adder_1 ⟨1, by decide⟩) false
]
def adder_hierarchical_2_conns : List (List Nat) := [
  [],
  [],
  [],
  [],
  [],
  [0, 1, 2],
  [0, 1, 2],
  [6, 3, 4],
  [6, 3, 4]
]
def adder_hierarchical_2 : Circuit := { gates := adder_hierarchical_2_gates, wiring := mkWiring adder_hierarchical_2_gates adder_hierarchical_2_conns (by decide), is_dag := by decide }
def a_bus_adder_hierarchical_2 : List (Fin 9) := [⟨1, by decide⟩, ⟨3, by decide⟩]
def b_bus_adder_hierarchical_2 : List (Fin 9) := [⟨2, by decide⟩, ⟨4, by decide⟩]
def sum_bus_adder_hierarchical_2 : List (Fin 9) := [⟨5, by decide⟩, ⟨7, by decide⟩]
def cin_adder_hierarchical_2 : Fin 9 := ⟨0, by decide⟩
def cout_adder_hierarchical_2 : Fin 9 := ⟨8, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: adder_hierarchical_2
@[simp] lemma ast_adder_hierarchical_2_cin (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_a_0 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_b_0 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_a_1 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_b_1 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_sum_0 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = (compute_adder_1 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨2, by decide⟩)).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_sum_1 (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = (compute_adder_1 ((compute_adder_1 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨2, by decide⟩)).testBit 1) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩)).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_2_cout (s : State adder_hierarchical_2) (i : Fin 9) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG adder_hierarchical_2 9 i) = (compute_adder_1 ((compute_adder_1 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨2, by decide⟩)).testBit 1) (s ⟨3, by decide⟩) (s ⟨4, by decide⟩)).testBit 1 := by cases i; subst hi; rfl

instance instIsAdder_adder_hierarchical_2 : IsAdder adder_hierarchical_2 2 a_bus_adder_hierarchical_2 b_bus_adder_hierarchical_2 sum_bus_adder_hierarchical_2 cin_adder_hierarchical_2 cout_adder_hierarchical_2 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 9) : evalCombinatorial adder_hierarchical_2 adder_hierarchical_2.gates.length s i = evalExpr s (unrollDAG adder_hierarchical_2 9 i) := by fin_cases i <;> rfl
    simp only [a_bus_adder_hierarchical_2, b_bus_adder_hierarchical_2, sum_bus_adder_hierarchical_2, cout_adder_hierarchical_2, cin_adder_hierarchical_2, bitsToNat]
    simp only [equiv]
    simp only [ast_adder_hierarchical_2_cin, ast_adder_hierarchical_2_a_0, ast_adder_hierarchical_2_b_0, ast_adder_hierarchical_2_a_1, ast_adder_hierarchical_2_b_1, ast_adder_hierarchical_2_sum_0, ast_adder_hierarchical_2_sum_1, ast_adder_hierarchical_2_cout]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨3, by decide⟩ = a_1
    generalize h_b_1 : s ⟨4, by decide⟩ = b_1
    cases cin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> decide

instance instVerifiedAdder2_adder_hierarchical_2 : VerifiedAdder2 adder_hierarchical_2 a_bus_adder_hierarchical_2 b_bus_adder_hierarchical_2 sum_bus_adder_hierarchical_2 cin_adder_hierarchical_2 cout_adder_hierarchical_2 where
  proof := instIsAdder_adder_hierarchical_2

-- ============================================================
-- COMPONENT: adder_hierarchical_4
--
-- 4-bit adder composed of two adder_2 cells in ripple-carry fashion.
-- Gates 0–8: primary inputs (cin, a[0..3], b[0..3]).
-- Gates 9–11: lower adder_2 cell (sum bits 0,1 and carry-mid).
-- Gates 12–14: upper adder_2 cell (sum bits 2,3 and cout).
-- ============================================================
def adder_hierarchical_4_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk (.adder_2 ⟨0, by decide⟩) false,
  Gate.mk (.adder_2 ⟨1, by decide⟩) false,
  Gate.mk (.adder_2 ⟨2, by decide⟩) false,
  Gate.mk (.adder_2 ⟨0, by decide⟩) false,
  Gate.mk (.adder_2 ⟨1, by decide⟩) false,
  Gate.mk (.adder_2 ⟨2, by decide⟩) false
]
def adder_hierarchical_4_conns : List (List Nat) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [0, 1, 3, 2, 4],
  [0, 1, 3, 2, 4],
  [0, 1, 3, 2, 4],
  [11, 5, 7, 6, 8],
  [11, 5, 7, 6, 8],
  [11, 5, 7, 6, 8]
]
def adder_hierarchical_4 : Circuit := { gates := adder_hierarchical_4_gates, wiring := mkWiring adder_hierarchical_4_gates adder_hierarchical_4_conns (by decide), is_dag := by decide }
def a_bus_adder_hierarchical_4 : List (Fin 15) := [⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩]
def b_bus_adder_hierarchical_4 : List (Fin 15) := [⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩]
def sum_bus_adder_hierarchical_4 : List (Fin 15) := [⟨9, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩]
def cin_adder_hierarchical_4 : Fin 15 := ⟨0, by decide⟩
def cout_adder_hierarchical_4 : Fin 15 := ⟨14, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: adder_hierarchical_4
@[simp] lemma ast_adder_hierarchical_4_cin (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_a_0 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_b_0 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_a_1 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_b_1 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_a_2 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 5 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨5, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_b_2 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 6 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨6, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_a_3 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨7, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_b_3 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 8 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = s ⟨8, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_sum_0 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 9 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨3, by decide⟩) (s ⟨2, by decide⟩) (s ⟨4, by decide⟩)).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_sum_1 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 10 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = (compute_adder_2 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨3, by decide⟩) (s ⟨2, by decide⟩) (s ⟨4, by decide⟩)).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_sum_2 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 12 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = (compute_adder_2 ((compute_adder_2 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨3, by decide⟩) (s ⟨2, by decide⟩) (s ⟨4, by decide⟩)).testBit 2) (s ⟨5, by decide⟩) (s ⟨7, by decide⟩) (s ⟨6, by decide⟩) (s ⟨8, by decide⟩)).testBit 0 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_sum_3 (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 13 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = (compute_adder_2 ((compute_adder_2 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨3, by decide⟩) (s ⟨2, by decide⟩) (s ⟨4, by decide⟩)).testBit 2) (s ⟨5, by decide⟩) (s ⟨7, by decide⟩) (s ⟨6, by decide⟩) (s ⟨8, by decide⟩)).testBit 1 := by cases i; subst hi; rfl
@[simp] lemma ast_adder_hierarchical_4_cout (s : State adder_hierarchical_4) (i : Fin 15) (hi : i.val = 14 := by decide) : evalExpr s (unrollDAG adder_hierarchical_4 15 i) = (compute_adder_2 ((compute_adder_2 (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) (s ⟨3, by decide⟩) (s ⟨2, by decide⟩) (s ⟨4, by decide⟩)).testBit 2) (s ⟨5, by decide⟩) (s ⟨7, by decide⟩) (s ⟨6, by decide⟩) (s ⟨8, by decide⟩)).testBit 2 := by cases i; subst hi; rfl

instance instIsAdder_adder_hierarchical_4 : IsAdder adder_hierarchical_4 4 a_bus_adder_hierarchical_4 b_bus_adder_hierarchical_4 sum_bus_adder_hierarchical_4 cin_adder_hierarchical_4 cout_adder_hierarchical_4 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 15) : evalCombinatorial adder_hierarchical_4 adder_hierarchical_4.gates.length s i = evalExpr s (unrollDAG adder_hierarchical_4 15 i) := by fin_cases i <;> rfl
    simp only [a_bus_adder_hierarchical_4, b_bus_adder_hierarchical_4, sum_bus_adder_hierarchical_4, cout_adder_hierarchical_4, cin_adder_hierarchical_4, bitsToNat]
    simp only [equiv]
    simp only [ast_adder_hierarchical_4_cin, ast_adder_hierarchical_4_a_0, ast_adder_hierarchical_4_b_0, ast_adder_hierarchical_4_a_1, ast_adder_hierarchical_4_b_1, ast_adder_hierarchical_4_a_2, ast_adder_hierarchical_4_b_2, ast_adder_hierarchical_4_a_3, ast_adder_hierarchical_4_b_3, ast_adder_hierarchical_4_sum_0, ast_adder_hierarchical_4_sum_1, ast_adder_hierarchical_4_sum_2, ast_adder_hierarchical_4_sum_3, ast_adder_hierarchical_4_cout]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨3, by decide⟩ = a_1
    generalize h_b_1 : s ⟨4, by decide⟩ = b_1
    generalize h_a_2 : s ⟨5, by decide⟩ = a_2
    generalize h_b_2 : s ⟨6, by decide⟩ = b_2
    generalize h_a_3 : s ⟨7, by decide⟩ = a_3
    generalize h_b_3 : s ⟨8, by decide⟩ = b_3
    cases cin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> cases a_2 <;> cases b_2 <;> cases a_3 <;> cases b_3 <;> decide

instance instVerifiedAdder4_adder_hierarchical_4 : VerifiedAdder4 adder_hierarchical_4 a_bus_adder_hierarchical_4 b_bus_adder_hierarchical_4 sum_bus_adder_hierarchical_4 cin_adder_hierarchical_4 cout_adder_hierarchical_4 where
  proof := instIsAdder_adder_hierarchical_4

-- ============================================================
-- COMPONENT: adder_cla_2
--
-- 2-bit carry-lookahead adder.  Unlike the hierarchical design, this circuit
-- computes carry signals in parallel using generate (G = a&b) and propagate
-- (P = a^b) terms, avoiding the ripple-carry delay.
--
-- Gate layout (18 gates):
--   0–4   : igate   (cin, a[0], b[0], a[1], b[1])
--   5     : xor_    P0 = a[0] ^ b[0]
--   6     : and_    G0 = a[0] & b[0]
--   7     : xor_    P1 = a[1] ^ b[1]
--   8     : and_    G1 = a[1] & b[1]
--   9     : and_    P0 & cin
--   10    : or_     c1 = G0 | (P0 & cin)        ← carry into bit 1
--   11    : and_    P1 & G0
--   12    : and_    P1 & P0
--   13    : and_    (P1 & P0) & cin
--   14    : or_     G1 | (P1 & G0)
--   15    : or_     cout = G1 | (P1&G0) | (P1&P0&cin)
--   16    : xor_    sum[0] = P0 ^ cin
--   17    : xor_    sum[1] = P1 ^ c1
-- ============================================================
def adder_cla_2_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .igate false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .xor_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .or_ false,
  Gate.mk .or_ false,
  Gate.mk .xor_ false,
  Gate.mk .xor_ false
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
def a_bus_adder_cla_2 : List (Fin 18) := [⟨1, by decide⟩, ⟨3, by decide⟩]
def b_bus_adder_cla_2 : List (Fin 18) := [⟨2, by decide⟩, ⟨4, by decide⟩]
def sum_bus_adder_cla_2 : List (Fin 18) := [⟨16, by decide⟩, ⟨17, by decide⟩]
def cin_adder_cla_2 : Fin 18 := ⟨0, by decide⟩
def cout_adder_cla_2 : Fin 18 := ⟨15, by decide⟩

-- AST BOUNDARY LEMMAS & PROOF: adder_cla_2
@[simp] lemma ast_adder_cla_2_cin (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_a_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 1 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨1, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_b_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_a_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 3 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨3, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_b_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_sum_0 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 16 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) ^^ s ⟨0, by decide⟩) := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_sum_1 (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) ^^ ((s ⟨1, by decide⟩ && s ⟨2, by decide⟩) || ((s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩) && s ⟨0, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_adder_cla_2_cout (s : State adder_cla_2) (i : Fin 18) (hi : i.val = 15 := by decide) : evalExpr s (unrollDAG adder_cla_2 18 i) = (((s ⟨3, by decide⟩ && s ⟨4, by decide⟩) || ((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) && (s ⟨1, by decide⟩ && s ⟨2, by decide⟩))) || (((s ⟨3, by decide⟩ ^^ s ⟨4, by decide⟩) && (s ⟨1, by decide⟩ ^^ s ⟨2, by decide⟩)) && s ⟨0, by decide⟩)) := by cases i; subst hi; rfl

-- KEY RESULT
-- Theorem: adder_cla_2 satisfies IsAdder with n=2.
-- This confirms that the CLA and hierarchical-2 designs are functionally equivalent.
instance instIsAdder_adder_cla_2 : IsAdder adder_cla_2 2 a_bus_adder_cla_2 b_bus_adder_cla_2 sum_bus_adder_cla_2 cin_adder_cla_2 cout_adder_cla_2 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  adder_correct := by
    intro s
    have equiv (i : Fin 18) : evalCombinatorial adder_cla_2 adder_cla_2.gates.length s i = evalExpr s (unrollDAG adder_cla_2 18 i) := by fin_cases i <;> rfl
    simp only [a_bus_adder_cla_2, b_bus_adder_cla_2, sum_bus_adder_cla_2, cout_adder_cla_2, cin_adder_cla_2, bitsToNat]
    simp only [equiv]
    simp only [ast_adder_cla_2_cin, ast_adder_cla_2_a_0, ast_adder_cla_2_b_0, ast_adder_cla_2_a_1, ast_adder_cla_2_b_1, ast_adder_cla_2_sum_0, ast_adder_cla_2_sum_1, ast_adder_cla_2_cout]
    generalize h_cin : s ⟨0, by decide⟩ = cin
    generalize h_a_0 : s ⟨1, by decide⟩ = a_0
    generalize h_b_0 : s ⟨2, by decide⟩ = b_0
    generalize h_a_1 : s ⟨3, by decide⟩ = a_1
    generalize h_b_1 : s ⟨4, by decide⟩ = b_1
    cases cin <;> cases a_0 <;> cases b_0 <;> cases a_1 <;> cases b_1 <;> decide

instance instVerifiedAdder2_adder_cla_2 : VerifiedAdder2 adder_cla_2 a_bus_adder_cla_2 b_bus_adder_cla_2 sum_bus_adder_cla_2 cin_adder_cla_2 cout_adder_cla_2 where
  proof := instIsAdder_adder_cla_2

end hdl.examples.adder
