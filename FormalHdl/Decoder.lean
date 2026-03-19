-- Adam Friesz, Winter 2026
import FormalHdl.Defs
namespace hdl.examples.decoder
open hdl
set_option linter.style.longLine false
set_option linter.style.whitespace false


-- COMPONENT: decoder_3
def decoder_3_gates : List Gate := [
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .igate false,
  Gate.mk .not_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false,
  Gate.mk .and_ false
]
def decoder_3_conns : List (List Nat) := [
  [],
  [0],
  [],
  [2],
  [],
  [4],
  [1, 3],
  [6, 5],
  [0, 3],
  [8, 5],
  [1, 2],
  [10, 5],
  [0, 2],
  [12, 5],
  [1, 3],
  [14, 4],
  [0, 3],
  [16, 4],
  [1, 2],
  [18, 4],
  [0, 2],
  [20, 4]
]
def decoder_3 : Circuit := { gates := decoder_3_gates, wiring := mkWiring decoder_3_gates decoder_3_conns (by decide), is_dag := by decide }
def sel_bus_decoder_3 : List (Fin 22) := [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩]
def out_bus_decoder_3 : List (Fin 22) := [⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩]

-- AST BOUNDARY LEMMAS & PROOF: decoder_3
@[simp] lemma ast_decoder_3_sel_0 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 0 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = s ⟨0, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_sel_1 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 2 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = s ⟨2, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_sel_2 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 4 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = s ⟨4, by decide⟩ := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_0 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 7 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = ((!((s ⟨0, by decide⟩)) && !((s ⟨2, by decide⟩))) && !((s ⟨4, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_1 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 9 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = (((s ⟨0, by decide⟩) && !((s ⟨2, by decide⟩))) && !((s ⟨4, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_2 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 11 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = ((!((s ⟨0, by decide⟩)) && (s ⟨2, by decide⟩)) && !((s ⟨4, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_3 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 13 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = (((s ⟨0, by decide⟩) && (s ⟨2, by decide⟩)) && !((s ⟨4, by decide⟩))) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_4 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 15 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = ((!((s ⟨0, by decide⟩)) && !((s ⟨2, by decide⟩))) && (s ⟨4, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_5 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 17 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = (((s ⟨0, by decide⟩) && !((s ⟨2, by decide⟩))) && (s ⟨4, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_6 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 19 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = ((!((s ⟨0, by decide⟩)) && (s ⟨2, by decide⟩)) && (s ⟨4, by decide⟩)) := by cases i; subst hi; rfl
@[simp] lemma ast_decoder_3_out_7 (s : State decoder_3) (i : Fin decoder_3.gates.length) (hi : i.val = 21 := by decide) : evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) = (((s ⟨0, by decide⟩) && (s ⟨2, by decide⟩)) && (s ⟨4, by decide⟩)) := by cases i; subst hi; rfl

instance instIsDecoder_decoder_3 : IsDecoder decoder_3 3 sel_bus_decoder_3 out_bus_decoder_3 where
  widths_match := by decide
  inputs_are_valid := by intro i h; fin_cases h <;> rfl
  decode_correct := by
    intro s
    have equiv (i : Fin decoder_3.gates.length) : evalCombinatorial decoder_3 decoder_3.gates.length s i = evalExpr s (unrollDAG decoder_3 decoder_3.gates.length i) := by fin_cases i <;> rfl
    simp only [sel_bus_decoder_3, out_bus_decoder_3, bitsToNat]
    simp only [equiv]
    simp only [ast_decoder_3_sel_0, ast_decoder_3_sel_1, ast_decoder_3_sel_2, ast_decoder_3_out_0, ast_decoder_3_out_1, ast_decoder_3_out_2, ast_decoder_3_out_3, ast_decoder_3_out_4, ast_decoder_3_out_5, ast_decoder_3_out_6, ast_decoder_3_out_7]
    generalize h_sel_0 : s ⟨0, by decide⟩ = sel_0
    generalize h_sel_1 : s ⟨2, by decide⟩ = sel_1
    generalize h_sel_2 : s ⟨4, by decide⟩ = sel_2
    cases sel_0 <;> cases sel_1 <;> cases sel_2 <;> decide

instance instVerifiedDecoder3_decoder_3 : VerifiedDecoder3 decoder_3 sel_bus_decoder_3 out_bus_decoder_3 where
  proof := instIsDecoder_decoder_3

end hdl.examples.decoder
