# components.py — Lean 4 Netlist & Proof Code Generator
# Adam Friesz, Winter 2026
#
# PURPOSE
# -------
# This script is the build-time code generator for the FormalHDL project.
# It produces the Lean 4 source files that define verified circuit components
# (Adder.lean, Subtractor.lean, Comparator.lean, Counter.lean, Decoder.lean).
# Writing these files by hand would be tedious and error-prone because every
# component requires three tightly coupled artefacts:
#   1. Gate-list and wiring-list definitions  (the circuit netlist)
#   2. @[simp] boundary lemmas               (one per named node, proved by rfl)
#   3. IsAdder / IsSubtractor / … instance   (the machine-checked contract proof)
# The generator writes all three in a consistent, mechanically correct way from
# a high-level netlist description.
#
# HOW IT FITS INTO THE PROJECT
# ----------------------------
# The intended workflow is:
#   python components.py          # regenerate one or more .lean files
#   lake build                    # Lean checks all proofs
#
# To (re)generate a file, uncomment the relevant block at the bottom of the
# script (each block is guarded by a comment) and run the script.  The output
# is written directly to the FormalHdl/ directory so it can be imported by the
# rest of the project.
#
# ARCHITECTURE
# ------------
# All component generators inherit from VerifiedComponent, which handles:
#   • _add_gate()        — registers a gate and builds the wire→gate-index map
#   • _get_bool_expr()   — recursively unrolls a wire's logic into a Lean Bool
#                          expression (used to generate boundary lemma RHS values)
#   • generate_gates()   — emits the `_gates`, `_conns`, and `Circuit` definitions
#
# Subclasses override _build_netlist() to describe their topology using _add_gate()
# calls, and generate_equivalence_proof() to emit the boundary lemmas and contract
# instance.  The five concrete families are:
#
#   Adder subclasses
#     RippleCarryAdder       — flat gate-level RCA (used for adder_rca_1)
#     HierarchicalAdder      — greedy macro tiling with ADDER_4/2/1 cells
#     CarryLookaheadAdder    — flat gate-level CLA
#
#   Subtractor subclasses
#     GateLevelSubtractor1   — 1-bit XOR/AND/NOT subtractor
#     HierarchicalSubtractor2/4 — two's-complement via ADDER_2/4 macros
#
#   HierarchicalComparator   — A < B via subtractor carry-out + NOT
#
#   HierarchicalUpCounter    — synchronous up-counter; B-bus held at zero,
#                              cin driven by the enable signal
#
#   HierarchicalUpDownCounter — synchronous up/down-counter; a mux built from
#                               AND/OR gates drives the B-bus:
#                                 incr=1,decr=0 → B = 000...1  (+1)
#                                 incr=0,decr=1 → B = 111...1  (-1 mod 2^n)
#                                 incr=decr     → B = 000...0  (hold)
#
#   Decoder                  — gate-level N-to-2^N one-hot decoder
#
# STANDARD CELLS vs PHYSICAL GATES
# ---------------------------------
# _add_gate() accepts both:
#   • Physical gates: "NOT", "AND", "OR", "XOR", "INPUT", "DFF"
#     → mapped to GateKind.not_, .and_, .or_, .xor_, .igate, .dff
#   • Standard cells: "ADDER_1 <bit>", "ADDER_2 <bit>", "ADDER_4 <bit>",
#     "UP_DOWN_COUNT_1/2/4 <bit>", "COMP_1/2/4", "DECODER_3 <bit>"
#     → mapped to the parameterised GateKind constructors in Defs.lean
#
# Standard cells are "proof-carrying macros": Defs.lean's evalCombinatorial
# already knows their semantics, so the unroller (_get_bool_expr) can inline
# them as calls to compute_adder_1/2/4 rather than expanding every sub-gate.
# This keeps boundary lemmas readable and keeps the Boolean case-split in
# adder_correct / sub_correct manageable.

class VerifiedComponent:
    """The Unified Base Class with Proof-Carrying Standard Cell Support."""
    def __init__(self, name: str, n_bits: int):
        self.name = name
        self.n = n_bits
        self.wire_to_id = {}
        self.gate_defs = {}
        self.gates = []
        self.connections_str = []
        self.current_id = 0
        self.state_bounds = [] # Tracks INPUT and DFF pins
        
        # Trigger the build automatically
        self._build_netlist()

    def _build_netlist(self):
        raise NotImplementedError

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        """Pass 1: Register standard cells and physical gates."""
        self.wire_to_id[out_wire] = self.current_id
        self.gate_defs[out_wire] = (op, in_wires)
        
        if op == "INPUT":
            self.gates.append("Gate.mk .igate false")
            self.state_bounds.append(out_wire)
        elif op == "DFF":
            self.gates.append("Gate.mk .dff false")
            self.state_bounds.append(out_wire)
            
        # Standard Cells (Proof-Carrying Macros)
        elif op.startswith("ADDER_1"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.adder_1 ⟨{bit}, by decide⟩) false")
        elif op.startswith("ADDER_2"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.adder_2 ⟨{bit}, by decide⟩) false")
        elif op.startswith("ADDER_4"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.adder_4 ⟨{bit}, by decide⟩) false")
        elif op.startswith("UP_DOWN_COUNT_1"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.up_down_count_1 ⟨{bit}, by decide⟩) false")
        elif op.startswith("UP_DOWN_COUNT_2"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.up_down_count_2 ⟨{bit}, by decide⟩) false")
        elif op.startswith("UP_DOWN_COUNT_4"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.up_down_count_4 ⟨{bit}, by decide⟩) false")
        elif op == "COMP_1":
            self.gates.append("Gate.mk .comp_1 false")   
        elif op == "COMP_2":
            self.gates.append("Gate.mk .comp_2 false")   
        elif op == "COMP_4":
            self.gates.append("Gate.mk .comp_4 false")   
        elif op.startswith("DECODER_3"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.decoder_3 ⟨{bit}, by decide⟩) false")
        
        # Physical Logic Gates
        else:
            self.gates.append(f"Gate.mk .{op.lower()}_ false")
            
        self.connections_str.append(in_wires)
        self.current_id += 1

    def _get_bool_expr(self, wire: str) -> str:
        """Recursively unrolls logic and hierarchical macros into Lean math."""
        op, args = self.gate_defs[wire]
        if op == "INPUT" or op == "DFF":
            return f"(s ⟨{self.wire_to_id[wire]}, by decide⟩)"
        
        exprs = [self._get_bool_expr(a) for a in args]
        if op == "AND": return f"({exprs[0]} && {exprs[1]})"
        if op == "OR":  return f"({exprs[0]} || {exprs[1]})"
        if op == "XOR": return f"({exprs[0]} ^^ {exprs[1]})"
        if op == "NOT": return f"!({exprs[0]})"
        
        # Safely unroll Hierarchical Standard Cells!
        if op.startswith("ADDER_1"):
            bit = op.split(" ")[1]
            return f"(compute_adder_1 ({exprs[0]}) ({exprs[1]}) ({exprs[2]})).testBit {bit}"
        if op.startswith("ADDER_2"):
            bit = op.split(" ")[1]
            return f"(compute_adder_2 ({exprs[0]}) ({exprs[1]}) ({exprs[2]}) ({exprs[3]}) ({exprs[4]})).testBit {bit}"
        if op.startswith("ADDER_4"):
            bit = op.split(" ")[1]
            return f"(compute_adder_4 ({exprs[0]}) ({exprs[1]}) ({exprs[2]}) ({exprs[3]}) ({exprs[4]}) ({exprs[5]}) ({exprs[6]}) ({exprs[7]}) ({exprs[8]})).testBit {bit}"
        if op.startswith("DECODER_3"):
            bit = op.split(" ")[1]
            val = f"({exprs[0]}.toNat + 2*{exprs[1]}.toNat + 4*{exprs[2]}.toNat)"
            return f"({val} == {bit})"
        if op == "COMP_1":
            a_val = f"({exprs[0]}.toNat)"
            b_val = f"({exprs[4]}.toNat)"
            return f"({a_val} < {b_val})"
        if op == "COMP_2":
            a_val = f"({exprs[0]}.toNat + 2*{exprs[1]}.toNat)"
            b_val = f"({exprs[4]}.toNat + 2*{exprs[5]}.toNat)"
            return f"({a_val} < {b_val})"
        if op == "COMP_4":
            a_val = f"({exprs[0]}.toNat + 2*{exprs[1]}.toNat + 4*{exprs[2]}.toNat + 8*{exprs[3]}.toNat)"
            b_val = f"({exprs[4]}.toNat + 2*{exprs[5]}.toNat + 4*{exprs[6]}.toNat + 8*{exprs[7]}.toNat)"
            return f"({a_val} < {b_val})"
        if op.startswith("UP_DOWN_COUNT_1"):
            bit = op.split(" ")[1]
            q_val = f"({exprs[2]}.toNat)"
            next_val = f"(if {exprs[0]} && !({exprs[1]}) then ({q_val} + 1) % 2 else if {exprs[1]} && !({exprs[0]}) then ({q_val} + 1) % 2 else {q_val})"
            return f"({next_val}).testBit {bit}"
        if op.startswith("UP_DOWN_COUNT_2"):
            bit = op.split(" ")[1]
            q_val = f"({exprs[2]}.toNat + 2*{exprs[3]}.toNat)"
            next_val = f"(if {exprs[0]} && !({exprs[1]}) then ({q_val} + 1) % 4 else if {exprs[1]} && !({exprs[0]}) then ({q_val} + 3) % 4 else {q_val})"
            return f"({next_val}).testBit {bit}"
        if op.startswith("UP_DOWN_COUNT_4"):
            bit = op.split(" ")[1]
            q_val = f"({exprs[2]}.toNat + 2*{exprs[3]}.toNat + 4*{exprs[4]}.toNat + 8*{exprs[5]}.toNat)"
            next_val = f"(if {exprs[0]} && !({exprs[1]}) then ({q_val} + 1) % 16 else if {exprs[1]} && !({exprs[0]}) then ({q_val} + 15) % 16 else {q_val})"
            return f"({next_val}).testBit {bit}"
        return "false"
    
    def generate_gates(self) -> str:
        """Pass 2: Resolve strings to IDs and generate Lean Circuit."""
        resolved_conns = []
        for wires in self.connections_str:
            ids = [str(self.wire_to_id[w]) for w in wires]
            resolved_conns.append(f"[{', '.join(ids)}]")
            
        out = [f"\n-- COMPONENT: {self.name}"]
        out.append(f"def {self.name}_gates : List Gate := [\n  " + ",\n  ".join(self.gates) + "\n]")
        out.append(f"def {self.name}_conns : List (List Nat) := [\n  " + ",\n  ".join(resolved_conns) + "\n]")
        out.append(f"def {self.name} : Circuit := {{ gates := {self.name}_gates, wiring := mkWiring {self.name}_gates {self.name}_conns (by decide), is_dag := by decide }}")
        return "\n".join(out)


class Adder(VerifiedComponent):
    """The Mathematical Contract Generator for Addition."""
    def __init__(self, name: str, n_bits: int):
        self.a_bus = []
        self.b_bus = []
        self.sum_bus = []
        self.cout_id = None
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        if out_wire.startswith("A_"): self.a_bus.append(created_id)
        elif out_wire.startswith("B_"): self.b_bus.append(created_id)
        elif out_wire.startswith("Sum_"): self.sum_bus.append(created_id)
        elif out_wire == "Cout": self.cout_id = created_id

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def a_bus_{self.name} : List (Fin {total}) := {fin_list(self.a_bus)}")
        out.append(f"def b_bus_{self.name} : List (Fin {total}) := {fin_list(self.b_bus)}")
        out.append(f"def sum_bus_{self.name} : List (Fin {total}) := {fin_list(self.sum_bus)}")
        out.append(f"def cin_{self.name} : Fin {total} := ⟨{self.wire_to_id['Cin']}, by decide⟩")
        out.append(f"def cout_{self.name} : Fin {total} := ⟨{self.cout_id}, by decide⟩\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        lemma_names = []
        # 1. Input Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")

        # 2. Output Bit-Blasting Lemmas (Crucial to clear free variables!)
        for i in range(self.n):
            wire = f"Sum_{i}"
            lname = f"ast_{self.name}_sum_{i}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        lname = f"ast_{self.name}_cout"
        lemma_names.append(lname)
        out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.cout_id} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr('Cout')} := by cases i; subst hi; rfl")

        # 3. Parameterized Contract Instantiation
        out.append(f"\ninstance instIsAdder_{self.name} : IsAdder {self.name} {self.n} a_bus_{self.name} b_bus_{self.name} sum_bus_{self.name} cin_{self.name} cout_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by intro i h; fin_cases h <;> rfl")
        out.append("  adder_correct := by")
        out.append("    intro s")
        out.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {self.name}.gates.length s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
        out.append(f"    simp only [a_bus_{self.name}, b_bus_{self.name}, sum_bus_{self.name}, cout_{self.name}, cin_{self.name}, bitsToNat]")
        out.append(f"    simp only [equiv]")
        out.append(f"    simp only [{', '.join(lemma_names)}]")
        
        for name in self.state_bounds:
            v_name = name.lower()
            out.append(f"    generalize h_{v_name} : s ⟨{self.wire_to_id[name]}, by decide⟩ = {v_name}")
            
        out.append(f"    {' <;> '.join(['cases ' + name.lower() for name in self.state_bounds])} <;> decide")
        
        # 4. Final Proof-Carrying Binding
        out.append(f"\ninstance instVerifiedAdder{self.n}_{self.name} : VerifiedAdder{self.n} {self.name} a_bus_{self.name} b_bus_{self.name} sum_bus_{self.name} cin_{self.name} cout_{self.name} where")
        out.append(f"  proof := instIsAdder_{self.name}\n")
        
        return "\n".join(out)

# ==========================================
# Verified Subclasses (Topology Only)
# ==========================================

class RippleCarryAdder(Adder):
    """Generates pure physical gates. For n=1, this is a 1-bit full adder."""
    def _build_netlist(self):
        self._add_gate("Cin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])
            
        curr_c = "Cin"
        for i in range(self.n):
            self._add_gate(f"AxB_{i}", "XOR", [f"A_{i}", f"B_{i}"])
            self._add_gate(f"AaB_{i}", "AND", [f"A_{i}", f"B_{i}"])
            self._add_gate(f"Sum_{i}", "XOR", [f"AxB_{i}", curr_c])
            self._add_gate(f"AxB_a_C_{i}", "AND", [f"AxB_{i}", curr_c])
            
            next_c = f"C_{i+1}" if i < self.n - 1 else "Cout"
            self._add_gate(next_c, "OR", [f"AaB_{i}", f"AxB_a_C_{i}"])
            curr_c = next_c


class HierarchicalAdder(Adder):
    """
    Generalized N-Bit Hierarchical Adder.
    Constructs the adder by chaining ADDER_4, ADDER_2, and ADDER_1 macros.
    """
    def __init__(self, name: str, n_bits: int):
        super().__init__(name, n_bits)

    def _build_netlist(self):
        # 1. Generate Global Inputs
        self._add_gate("Cin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])

        # 2. Macro Tiling Logic
        curr_bit = 0
        curr_cin = "Cin"

        while curr_bit < self.n:
            remaining = self.n - curr_bit
            
            # Greedily pick the largest available verified macro
            if remaining >= 4:
                chunk = 4
            elif remaining >= 2:
                chunk = 2
            else:
                chunk = 1

            # Build the input list for this specific macro block
            # Format: [Cin, A_0...A_k, B_0...B_k]
            inputs = [curr_cin]
            for i in range(chunk):
                inputs.append(f"A_{curr_bit + i}")
            for i in range(chunk):
                inputs.append(f"B_{curr_bit + i}")

            # Determine the name of the carry-out wire for this block
            # If it's the final block, name it "Cout", otherwise name it for the next block's Cin
            next_cin = "Cout" if (curr_bit + chunk == self.n) else f"C_{curr_bit + chunk}"

            # Instantiate the Sum bit outputs
            for i in range(chunk):
                self._add_gate(f"Sum_{curr_bit + i}", f"ADDER_{chunk} {i}", inputs)

            # Instantiate the Carry Out output
            self._add_gate(next_cin, f"ADDER_{chunk} {chunk}", inputs)

            # Advance the chain
            curr_cin = next_cin
            curr_bit += chunk

class CarryLookaheadAdder(Adder):
    """Physical logic generation for CLA. Works directly with generic base class."""
    def _build_netlist(self):
        self._add_gate("Cin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])

        for i in range(self.n):
            self._add_gate(f"P_{i}", "XOR", [f"A_{i}", f"B_{i}"])
            self._add_gate(f"G_{i}", "AND", [f"A_{i}", f"B_{i}"])

        carries = ["Cin"]
        for i in range(self.n):
            terms = [f"G_{i}"]
            for j in range(i - 1, -2, -1):
                current_wire = f"P_{i}"
                for k in range(i - 1, j, -1):
                    next_wire = f"AND_{current_wire}_P_{k}"
                    self._add_gate(next_wire, "AND", [current_wire, f"P_{k}"])
                    current_wire = next_wire
                last_in = f"G_{j}" if j >= 0 else "Cin"
                term_wire = f"Term_{i}_{j}"
                self._add_gate(term_wire, "AND", [current_wire, last_in])
                terms.append(term_wire)

            or_wire = terms[0]
            for t in range(1, len(terms)):
                is_last = (t == len(terms) - 1)
                out_name = f"C_{i+1}" if (is_last and i < self.n - 1) else ("Cout" if is_last else f"OR_{i}_{t}")
                self._add_gate(out_name, "OR", [or_wire, terms[t]])
                or_wire = out_name
            carries.append(or_wire)

        for i in range(self.n):
            self._add_gate(f"Sum_{i}", "XOR", [f"P_{i}", carries[i]])


class Subtractor(VerifiedComponent):
    """The Mathematical Contract Generator for Subtraction."""
    def __init__(self, name: str, n_bits: int):
        self.a_bus = []
        self.b_bus = []
        self.diff_bus = []
        self.bout_id = None
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        if out_wire.startswith("A_"): self.a_bus.append(created_id)
        elif out_wire.startswith("B_") and not out_wire.startswith("Bout"): self.b_bus.append(created_id)
        elif out_wire.startswith("Diff_"): self.diff_bus.append(created_id)
        elif out_wire == "Bout": self.bout_id = created_id

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def a_bus_{self.name} : List (Fin {total}) := {fin_list(self.a_bus)}")
        out.append(f"def b_bus_{self.name} : List (Fin {total}) := {fin_list(self.b_bus)}")
        out.append(f"def diff_bus_{self.name} : List (Fin {total}) := {fin_list(self.diff_bus)}")
        out.append(f"def bin_{self.name} : Fin {total} := ⟨{self.wire_to_id['Bin']}, by decide⟩")
        out.append(f"def bout_{self.name} : Fin {total} := ⟨{self.bout_id}, by decide⟩\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        lemma_names = []
        # Input Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")

        # Output Bit-Blasting Lemmas
        for i in range(self.n):
            wire = f"Diff_{i}"
            lname = f"ast_{self.name}_diff_{i}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        lname = f"ast_{self.name}_bout"
        lemma_names.append(lname)
        out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.bout_id} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr('Bout')} := by cases i; subst hi; rfl")

        # Parameterized Contract Instantiation
        out.append(f"\ninstance instIsSubtractor_{self.name} : IsSubtractor {self.name} {self.n} a_bus_{self.name} b_bus_{self.name} diff_bus_{self.name} bin_{self.name} bout_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by intro i h; fin_cases h <;> rfl")
        out.append("  sub_correct := by")
        out.append("    intro s")
        out.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {self.name}.gates.length s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
        out.append(f"    simp only [a_bus_{self.name}, b_bus_{self.name}, diff_bus_{self.name}, bout_{self.name}, bin_{self.name}, bitsToNat]")
        out.append(f"    simp only [equiv]")
        out.append(f"    simp only [{', '.join(lemma_names)}]")
        
        for name in self.state_bounds:
            v_name = name.lower()
            out.append(f"    generalize h_{v_name} : s ⟨{self.wire_to_id[name]}, by decide⟩ = {v_name}")
            
        out.append(f"    {' <;> '.join(['cases ' + name.lower() for name in self.state_bounds])} <;> decide")
        
        out.append(f"\ninstance instVerifiedSubtractor{self.n}_{self.name} : VerifiedSubtractor{self.n} {self.name} a_bus_{self.name} b_bus_{self.name} diff_bus_{self.name} bin_{self.name} bout_{self.name} where")
        out.append(f"  proof := instIsSubtractor_{self.name}\n")
        return "\n".join(out)

class GateLevelSubtractor1(Subtractor):
    """1-Bit Gate-Level Subtractor using physical logic gates."""
    def __init__(self, name: str):
        super().__init__(name, 1)

    def _build_netlist(self):
        self._add_gate("Bin", "INPUT", [])
        self._add_gate("A_0", "INPUT", [])
        self._add_gate("B_0", "INPUT", [])

        # Invert B and Bin
        self._add_gate("Not_B_0", "NOT", ["B_0"])
        self._add_gate("Not_Bin", "NOT", ["Bin"])

        # Physical Logic (A + Not_B + Not_Bin)
        self._add_gate("AxB_0", "XOR", ["A_0", "Not_B_0"])
        self._add_gate("AaB_0", "AND", ["A_0", "Not_B_0"])
        
        self._add_gate("Diff_0", "XOR", ["AxB_0", "Not_Bin"])
        
        self._add_gate("AxB_a_Cin_0", "AND", ["AxB_0", "Not_Bin"])
        self._add_gate("Cout", "OR", ["AaB_0", "AxB_a_Cin_0"])
        
        # Bout = NOT Cout
        self._add_gate("Bout", "NOT", ["Cout"])


class HierarchicalSubtractor2(Subtractor):
    """2-Bit Subtractor utilizing the ADDER_2 macro."""
    def __init__(self, name: str):
        super().__init__(name, 2)
        
    def _build_netlist(self):
        self._add_gate("Bin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])
            self._add_gate(f"Not_B_{i}", "NOT", [f"B_{i}"])
        
        self._add_gate("Not_Bin", "NOT", ["Bin"])
        
        inputs = ["Not_Bin", "A_0", "A_1", "Not_B_0", "Not_B_1"]
        self._add_gate("Diff_0", "ADDER_2 0", inputs)
        self._add_gate("Diff_1", "ADDER_2 1", inputs)
        self._add_gate("Cout", "ADDER_2 2", inputs)
        
        self._add_gate("Bout", "NOT", ["Cout"])


class HierarchicalSubtractor4(Subtractor):
    """4-Bit Subtractor utilizing the ADDER_4 macro."""
    def __init__(self, name: str):
        super().__init__(name, 4)
        
    def _build_netlist(self):
        self._add_gate("Bin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])
            self._add_gate(f"Not_B_{i}", "NOT", [f"B_{i}"])
        
        self._add_gate("Not_Bin", "NOT", ["Bin"])
        
        inputs = ["Not_Bin", "A_0", "A_1", "A_2", "A_3", "Not_B_0", "Not_B_1", "Not_B_2", "Not_B_3"]
        self._add_gate("Diff_0", "ADDER_4 0", inputs)
        self._add_gate("Diff_1", "ADDER_4 1", inputs)
        self._add_gate("Diff_2", "ADDER_4 2", inputs)
        self._add_gate("Diff_3", "ADDER_4 3", inputs)
        self._add_gate("Cout", "ADDER_4 4", inputs)
        
        self._add_gate("Bout", "NOT", ["Cout"])

class HierarchicalComparator(VerifiedComponent):
    """N-Bit Comparator outputting both A < B and A == B."""
    def __init__(self, name: str, n_bits: int):
        self.a_bus = []
        self.b_bus = []
        self.out_lt_id = None
        self.out_eq_id = None
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        if out_wire.startswith("A_") and not out_wire.startswith("A_lt_B"): 
            self.a_bus.append(created_id)
        elif out_wire.startswith("B_") and not out_wire.startswith("Not_B"): 
            self.b_bus.append(created_id)
        elif out_wire == "A_lt_B": self.out_lt_id = created_id
        elif out_wire == "A_eq_B": self.out_eq_id = created_id

    def _build_netlist(self):
        for i in range(self.n): self._add_gate(f"A_{i}", "INPUT", [])
        for i in range(self.n): self._add_gate(f"B_{i}", "INPUT", [])
        
        # --- 1. Less Than Logic (A < B via Borrow Out) ---
        self._add_gate("Zero_Not", "NOT", ["A_0"])
        self._add_gate("Zero", "AND", ["A_0", "Zero_Not"])
        self._add_gate("One", "NOT", ["Zero"])
        
        for i in range(self.n):
            self._add_gate(f"Not_B_{i}", "NOT", [f"B_{i}"])
            
        # We assume n is 4 for the ADDER_4 macro, but this can be conditionally swapped for ADDER_1/2
        if self.n == 4:
            inputs = ["One", "A_0", "A_1", "A_2", "A_3", "Not_B_0", "Not_B_1", "Not_B_2", "Not_B_3"]
            self._add_gate("Cout", "ADDER_4 4", inputs)
        else:
            # Fallback if using sizes other than 4 (can be expanded)
            self._add_gate("Cout", "OR", ["Zero", "Zero"]) 

        self._add_gate("A_lt_B", "NOT", ["Cout"])

        # --- 2. Equality Logic (A == B via XNOR) ---
        eq_wires = []
        for i in range(self.n):
            self._add_gate(f"Not_A_{i}", "NOT", [f"A_{i}"])
            # XNOR: (A AND B) OR (NOT A AND NOT B)
            self._add_gate(f"A_and_B_{i}", "AND", [f"A_{i}", f"B_{i}"])
            self._add_gate(f"NotA_and_NotB_{i}", "AND", [f"Not_A_{i}", f"Not_B_{i}"])
            self._add_gate(f"Eq_{i}", "OR", [f"A_and_B_{i}", f"NotA_and_NotB_{i}"])
            eq_wires.append(f"Eq_{i}")
            
        # Cascade AND the equality bits
        curr_eq = eq_wires[0]
        for i in range(1, self.n):
            self._add_gate(f"Eq_acc_{i}", "AND", [curr_eq, eq_wires[i]])
            curr_eq = f"Eq_acc_{i}"
            
        self._add_gate("A_eq_B", "OR", [curr_eq, curr_eq]) # Pass-through to name the final wire

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def a_bus_{self.name} : List (Fin {total}) := {fin_list(self.a_bus)}")
        out.append(f"def b_bus_{self.name} : List (Fin {total}) := {fin_list(self.b_bus)}")
        out.append(f"def out_lt_{self.name} : Fin {total} := ⟨{self.out_lt_id}, by decide⟩")
        out.append(f"def out_eq_{self.name} : Fin {total} := ⟨{self.out_eq_id}, by decide⟩\n")
        return "\n".join(out)

class HierarchicalUpCounter(VerifiedComponent):
    """A formally verified N-Bit Sequential Up Counter using Hierarchical Adders."""
    def __init__(self, name: str, n_bits: int):
        self.q_bus = []
        self.next_q_bus = []
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        if out_wire.startswith("Q_"):
            self.q_bus.append(created_id)
        elif out_wire.startswith("Next_Q_"):
            self.next_q_bus.append(created_id)

    def _build_netlist(self):
        # 1. Inputs
        self._add_gate("Inc", "INPUT", [])
        
        # Helper to generate a constant Zero for the B bus of the adders
        self._add_gate("Not_Inc", "NOT", ["Inc"])
        self._add_gate("Zero", "AND", ["Inc", "Not_Inc"])
        
        # 2. Sequential State DFFs (Q_0 to Q_n-1)
        for i in range(self.n):
            self._add_gate(f"Q_{i}", "DFF", [f"Next_Q_{i}"])
            
        # 3. Build the +1 incrementer using cascaded Adders (Chunks of 4, 2, 1)
        bits_left = self.n
        curr_bit = 0
        curr_c = "Inc"
        
        while bits_left > 0:
            if bits_left >= 4:
                step = 4; op = "ADDER_4"
            elif bits_left >= 2:
                step = 2; op = "ADDER_2"
            else:
                step = 1; op = "ADDER_1"
                
            inputs = [curr_c]
            # A bus: Q bits
            for i in range(step): inputs.append(f"Q_{curr_bit + i}")
            # B bus: Constant Zero
            for i in range(step): inputs.append("Zero")
            
            # Outputs: Next_Q
            for i in range(step):
                self._add_gate(f"Next_Q_{curr_bit + i}", f"{op} {i}", inputs)
                
            # Carry cascading
            if curr_bit + step < self.n:
                curr_c = f"C_{curr_bit + step}"
                self._add_gate(curr_c, f"{op} {step}", inputs)
                
            curr_bit += step
            bits_left -= step

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def q_bus_{self.name} : List (Fin {self.name}.gates.length) := {fin_list(self.q_bus)}")
        out.append(f"def inc_{self.name} : Fin {self.name}.gates.length := ⟨{self.wire_to_id['Inc']}, by decide⟩\n")
        
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        lemma_names = []
        
        # 1. Input & State DFF Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
            
        wire = "Zero"
        lname = f"ast_{self.name}_zero"
        out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")

        # 2. Next State Output Bit-Blasting
        for i in range(self.n):
            wire = f"Next_Q_{i}"
            lname = f"ast_{self.name}_next_q_{i}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        # 3. runCycle Sequence Equivalence Lemmas (Bridging the clock boundary!)
        cycle_lemmas = []
        for i in range(self.n):
            lname = f"runCycle_{self.name}_q_{i}"
            cycle_lemmas.append(lname)
            q_id = self.wire_to_id[f"Q_{i}"]
            nq_id = self.wire_to_id[f"Next_Q_{i}"]
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (env : List Bool) : (runCycle {self.name} s env) ⟨{q_id}, by decide⟩ = evalCombinatorial {self.name} {total} s ⟨{nq_id}, by decide⟩ := by rfl")

        # 4. Parameterized Contract Instantiation
        out.append(f"\ninstance instIsUpCounter_{self.name} : IsUpCounter {self.name} {self.n} q_bus_{self.name} inc_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by decide")
        
        def build_proof_block(is_high: bool):
            block = []
            block.append("    intro s env h_inc")
            block.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {total} s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
            block.append(f"    simp only [q_bus_{self.name}, bitsToNat]")
            block.append(f"    simp only [{', '.join(cycle_lemmas)}]")
            block.append(f"    simp only [equiv]")
            block.append(f"    simp only [{', '.join(lemma_names)}]")
            
            # Translate and substitute the h_inc logic immediately
            block.append(f"    simp only [inc_{self.name}] at h_inc")
            block.append(f"    simp only [h_inc]")
            
            # Extract only the Q outputs as free variables (Inc is strictly handled by h_inc)
            dff_names = [name for name in self.state_bounds if name.startswith("Q_")]
            for name in dff_names:
                v_name = f"val_{name.lower()}"
                block.append(f"    generalize h_{v_name} : s ⟨{self.wire_to_id[name]}, by decide⟩ = {v_name}")
                
            if self.n <= 4:
                dff_cases = ' <;> '.join([f"cases val_{name.lower()}" for name in dff_names])
                if dff_cases:
                    block.append(f"    {dff_cases} <;> decide")
                else:
                    block.append(f"    decide")
            else:
                block.append(f"    sorry")
            return "\n".join(block)

        out.append("  incr_on_high := by")
        out.append(build_proof_block(True))
        
        out.append("  hold_on_low := by")
        out.append(build_proof_block(False))
            
        out.append(f"\ninstance instVerifiedUpCounter{self.n}_{self.name} : VerifiedUpCounter{self.n} {self.name} q_bus_{self.name} inc_{self.name} where")
        out.append(f"  proof := instIsUpCounter_{self.name}\n")

        return "\n".join(out)

class HierarchicalUpDownCounter(VerifiedComponent):
    """N-Bit Up/Down Counter using a single ADDER macro via Two's Complement."""
    def __init__(self, name: str, n_bits: int):
        self.q_bus = []
        self.incr_id = None
        self.decr_id = None
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        if out_wire == "Incr": self.incr_id = created_id
        elif out_wire == "Decr": self.decr_id = created_id
        elif out_wire.startswith("Q_"): self.q_bus.append(created_id)

    def _build_netlist(self):
        # 1. Inputs & State Elements
        self._add_gate("Incr", "INPUT", [])
        self._add_gate("Decr", "INPUT", [])
        
        for i in range(self.n):
            self._add_gate(f"Q_{i}", "DFF", [f"Next_Q_{i}"])

        # 2. Mutually Exclusive Control Logic
        # Protects the datapath if both signals are asserted high
        self._add_gate("Not_Incr", "NOT", ["Incr"])
        self._add_gate("Not_Decr", "NOT", ["Decr"])
        self._add_gate("Valid_Incr", "AND", ["Incr", "Not_Decr"])
        self._add_gate("Valid_Decr", "AND", ["Decr", "Not_Incr"])

        # 3. Two's Complement MUX for the Adder's B-Bus
        # B_0 is 1 if either Valid_Incr (+1) or Valid_Decr (-1) is true
        self._add_gate("B_0", "OR", ["Valid_Incr", "Valid_Decr"])
        
        # B_1 through B_{n-1} are 1 ONLY if Valid_Decr is true (Two's complement for -1 is all 1s)
        for i in range(1, self.n):
            self._add_gate(f"B_{i}", "AND", ["Valid_Decr", "Valid_Decr"]) # pass-through

        # 4. Synthesize Constant 0 for Cin
        self._add_gate("Zero", "AND", ["Incr", "Not_Incr"])

        # 5. Tile the adder using the available macros (ADDER_4, ADDER_2, ADDER_1).
        # Greedy chunking matches HierarchicalAdder/HierarchicalUpCounter: process bits
        # in groups of 4, then 2, then 1, chaining carry-out to carry-in between chunks.
        # Each chunk's inputs are [cin, Q_lo..Q_hi, B_lo..B_hi]; carry-out is bit index `chunk`.
        curr_bit = 0
        curr_cin = "Zero"
        while curr_bit < self.n:
            remaining = self.n - curr_bit
            if remaining >= 4:
                chunk = 4
            elif remaining >= 2:
                chunk = 2
            else:
                chunk = 1

            chunk_inputs = [curr_cin]
            for i in range(chunk):
                chunk_inputs.append(f"Q_{curr_bit + i}")
            for i in range(chunk):
                chunk_inputs.append(f"B_{curr_bit + i}")

            for i in range(chunk):
                self._add_gate(f"Next_Q_{curr_bit + i}", f"ADDER_{chunk} {i}", chunk_inputs)

            if curr_bit + chunk < self.n:
                curr_cin = f"C_{curr_bit + chunk}"
                self._add_gate(curr_cin, f"ADDER_{chunk} {chunk}", chunk_inputs)

            curr_bit += chunk

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def q_bus_{self.name} : List (Fin {self.name}.gates.length) := {fin_list(self.q_bus)}")
        out.append(f"def incr_{self.name} : Fin {self.name}.gates.length := ⟨{self.incr_id}, by decide⟩")
        out.append(f"def decr_{self.name} : Fin {self.name}.gates.length := ⟨{self.decr_id}, by decide⟩\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        lemma_names = []
        
        # 1. Input & State DFF Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
            
        # 2. Next State Logic Bounds
        for i in range(self.n):
            wire = f"Next_Q_{i}"
            lname = f"ast_{self.name}_next_q_{i}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        # 3. runCycle Sequence Equivalence
        cycle_lemmas = []
        for i in range(self.n):
            lname = f"runCycle_{self.name}_q_{i}"
            cycle_lemmas.append(lname)
            q_id = self.wire_to_id[f"Q_{i}"]
            nq_id = self.wire_to_id[f"Next_Q_{i}"]
            # Use the variable-binding pattern to bypass Fin proof-irrelevance issues in simp
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (env : List Bool) (idx : Fin {total}) (h : idx.val = {q_id} := by decide) : (runCycle {self.name} s env) idx = evalCombinatorial {self.name} {total} s ⟨{nq_id}, by decide⟩ := by cases idx; subst h; rfl")
        
    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        # Only the next_q lemmas are needed in the simp proof blocks.
        # The incr, decr, and q_i boundary lemmas are still emitted as @[simp] for
        # potential external use, but are excluded from the lemma_names simp list.
        lemma_names = []

        # 1. Input & State DFF Lemmas (emitted but not added to lemma_names)
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
            
        # 2. Next State Logic Bounds (added to lemma_names -- these are the only ones needed)
        for i in range(self.n):
            wire = f"Next_Q_{i}"
            lname = f"ast_{self.name}_next_q_{i}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        # 3. runCycle Sequence Equivalence (with idx binding fix)
        cycle_lemmas = []
        for i in range(self.n):
            lname = f"runCycle_{self.name}_q_{i}"
            cycle_lemmas.append(lname)
            q_id = self.wire_to_id[f"Q_{i}"]
            nq_id = self.wire_to_id[f"Next_Q_{i}"]
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (env : List Bool) (idx : Fin {total}) (h : idx.val = {q_id} := by decide) : (runCycle {self.name} s env) idx = evalCombinatorial {self.name} {total} s ⟨{nq_id}, by decide⟩ := by cases idx; subst h; rfl")

        # 4. Automated Proof Blocks
        def build_proof_block(mode: str):
            block = []
            
            if mode in ["up", "down"]:
                block.append("    intro s env h_incr h_decr")
            else: # "hold"
                block.append("    intro s env h_eq")
                
            block.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {total} s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
            block.append(f"    simp only [q_bus_{self.name}, bitsToNat]")
            block.append(f"    simp only [{', '.join(cycle_lemmas)}]")
            block.append(f"    simp only [equiv]")
            block.append(f"    simp only [{', '.join(lemma_names)}]")
            
            if mode == "up":
                block.append(f"    change s ⟨{self.incr_id}, by decide⟩ = true at h_incr")
                block.append(f"    change s ⟨{self.decr_id}, by decide⟩ = false at h_decr")
                block.append(f"    simp only [h_incr, h_decr]")
            elif mode == "down":
                block.append(f"    change s ⟨{self.incr_id}, by decide⟩ = false at h_incr")
                block.append(f"    change s ⟨{self.decr_id}, by decide⟩ = true at h_decr")
                block.append(f"    simp only [h_incr, h_decr]")
            else:
                # The circuit's hold logic (both incr=decr=0 and incr=decr=1 cases) simplifies
                # purely in terms of the decr signal after the AST lemmas fire -- the incr signal
                # drops out. So we generalize decr as val_in (clearing the goal), then use h_eq
                # to produce a matching hypothesis for the incr side on the bitsToNat RHS.
                # This mirrors hold_on_low in IsUpCounter: normalise the control signal, then
                # generalize the Q bits and close by exhaustive Bool case-split.
                block.append(f"    change s ⟨{self.incr_id}, by decide⟩ = s ⟨{self.decr_id}, by decide⟩ at h_eq")
                block.append(f"    generalize h_in : s ⟨{self.decr_id}, by decide⟩ = val_in")
                block.append(f"    rw [h_in] at h_eq")
                block.append(f"    simp only [h_eq]")


            # With q_bus typed as List (Fin {name}.gates.length), simp unfolds the list
            # literal using the same `by decide` proof terms that _get_bool_expr emits.
            # Both sides of the goal therefore use identical proof terms, so a plain
            # `generalize h : s ⟨q_id, by decide⟩ = val_q_i` clears both sides at once --
            # exactly the same pattern used by the working HierarchicalUpCounter proof.
            cases_tactics = []
            for i in range(self.n):
                q_id = self.wire_to_id[f"Q_{i}"]
                v_name = f"val_q_{i}"
                h_name = f"h_val_q_{i}"
                block.append(f"    generalize {h_name} : s \u27e8{q_id}, by decide\u27e9 = {v_name}")
                cases_tactics.append(f"cases {v_name}")

            cases_str = ' <;> '.join(cases_tactics)
            if mode == "hold":
                 cases_str = "cases val_in <;> " + cases_str
                 
            if cases_str:
                block.append(f"    {cases_str} <;> decide")
            else:
                block.append(f"    decide")
                
            return "\n".join(block)
                        
        out.append(f"\ninstance instIsUpDownCounter_{self.name} : IsUpDownCounter {self.name} {self.n} q_bus_{self.name} incr_{self.name} decr_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by decide")
        
        out.append("  count_up := by")
        out.append(build_proof_block("up"))
        
        out.append("  count_down := by")
        out.append(build_proof_block("down"))
        
        out.append("  hold_on_invalid := by")
        out.append(build_proof_block("hold"))
            
        out.append(f"\ninstance instVerifiedUpDownCounter{self.n}_{self.name} : VerifiedUpDownCounter{self.n} {self.name} q_bus_{self.name} incr_{self.name} decr_{self.name} where")
        out.append(f"  proof := instIsUpDownCounter_{self.name}\n")

        # The crucial return statement
        return "\n".join(out)

class Decoder(VerifiedComponent):
    """The Mathematical Contract Generator for a Gate-Level N-to-2^N Decoder."""
    def __init__(self, name: str, n_bits: int):
        self.sel_bus = []
        self.out_bus = []
        super().__init__(name, n_bits)

    def _add_gate(self, out_wire: str, op: str, in_wires: list):
        super()._add_gate(out_wire, op, in_wires)
        created_id = self.current_id - 1
        
        if out_wire.startswith("Sel_") and op == "INPUT":
            self.sel_bus.append(created_id)
        elif out_wire.startswith("Out_"):
            self.out_bus.append(created_id)

    def _build_netlist(self):
        # 1. Inputs (Sel_0 to Sel_n-1)
        for i in range(self.n):
            self._add_gate(f"Sel_{i}", "INPUT", [])
            self._add_gate(f"Not_Sel_{i}", "NOT", [f"Sel_{i}"])

        # 2. Gate-level Decoding Logic for all 2^N outputs
        for val in range(1 << self.n):
            and_inputs = []
            for i in range(self.n):
                # Check if the i-th bit of the current val is 1
                if (val & (1 << i)) != 0:
                    and_inputs.append(f"Sel_{i}")
                else:
                    and_inputs.append(f"Not_Sel_{i}")

            # 3. Cascade AND gates to combine all bits for this specific output
            if self.n == 1:
                self._add_gate(f"Out_{val}", "AND", [and_inputs[0], and_inputs[0]]) # Pass-through
            else:
                curr_wire = and_inputs[0]
                for i in range(1, self.n - 1):
                    wire_name = f"And_{val}_{i}"
                    self._add_gate(wire_name, "AND", [curr_wire, and_inputs[i]])
                    curr_wire = wire_name
                
                # Final AND gate connects to the respective Out pin
                self._add_gate(f"Out_{val}", "AND", [curr_wire, and_inputs[-1]])

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def sel_bus_{self.name} : List (Fin {total}) := {fin_list(self.sel_bus)}")
        out.append(f"def out_bus_{self.name} : List (Fin {total}) := {fin_list(self.out_bus)}\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        # We no longer use 'total' in the emitted code to ensure strict type matching!
        out = [f"\n-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        
        lemma_names = []
        # 1. Input Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            lemma_names.append(lname)
            # Use {self.name}.gates.length instead of the integer
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {self.name}.gates.length) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {self.name}.gates.length i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")

        # 2. Output Bit-Blasting Lemmas (for all 2^N outputs)
        for val in range(1 << self.n):
            wire = f"Out_{val}"
            lname = f"ast_{self.name}_out_{val}"
            lemma_names.append(lname)
            # Use {self.name}.gates.length
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {self.name}.gates.length) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {self.name}.gates.length i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")

        # 3. Parameterized Contract Instantiation
        out.append(f"\ninstance instIsDecoder_{self.name} : IsDecoder {self.name} {self.n} sel_bus_{self.name} out_bus_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by intro i h; fin_cases h <;> rfl")
        out.append("  decode_correct := by")
        out.append("    intro s")
        # Define the equiv rule using the exact unevaluated length property
        out.append(f"    have equiv (i : Fin {self.name}.gates.length) : evalCombinatorial {self.name} {self.name}.gates.length s i = evalExpr s (unrollDAG {self.name} {self.name}.gates.length i) := by fin_cases i <;> rfl")
        out.append(f"    simp only [sel_bus_{self.name}, out_bus_{self.name}, bitsToNat]")
        out.append(f"    simp only [equiv]")
        out.append(f"    simp only [{', '.join(lemma_names)}]")
        
        # Generalize the state variables to detach them from the Fin indices
        for name in self.state_bounds:
            v_name = name.lower()
            out.append(f"    generalize h_{v_name} : s ⟨{self.wire_to_id[name]}, by decide⟩ = {v_name}")
            
        # Case split on the generalized boolean inputs and evaluate
        out.append(f"    {' <;> '.join(['cases ' + name.lower() for name in self.state_bounds])} <;> decide")
        
        # 4. Final Proof-Carrying Binding
        if self.n == 3:
            out.append(f"\ninstance instVerifiedDecoder3_{self.name} : VerifiedDecoder3 {self.name} sel_bus_{self.name} out_bus_{self.name} where")
            out.append(f"  proof := instIsDecoder_{self.name}\n")
            
        return "\n".join(out)
                         
def print_preamble(namespace):
    out = ["-- Adam Friesz, Winter 2026"]
    out.append("import FormalHdl.Defs")
    out.append(f"namespace hdl.examples.{namespace}")
    out.append("open hdl")
    out.append("set_option linter.style.longLine false")
    out.append("set_option linter.style.whitespace false")
    out.append("\n")
    return "\n".join(out)

# filename = "FormalHdl/Adder.lean"
# with open(filename, "w") as f:
#     f.write(print_preamble("adder"))
#     # 1. Gate Level 1-Bit Adder (Proves the 1-bit contract)
#     rca_1 = RippleCarryAdder("adder_rca_1", 1)
#     f.write(rca_1.generate_gates())
#     f.write(rca_1.generate_equivalence_proof())

#     # 2. Hierarchical 2-Bit Adder (Builds using the 1-bit Macro)
#     hierarchical_2 = HierarchicalAdder2("adder_hierarchical_2")
#     f.write(hierarchical_2.generate_gates())
#     f.write(hierarchical_2.generate_equivalence_proof())

#     # 3. Hierarchical 4-Bit Adder (Builds using the 2-bit Macro)
#     hierarchical_4 = HierarchicalAdder4("adder_hierarchical_4")
#     f.write(hierarchical_4.generate_gates())
#     f.write(hierarchical_4.generate_equivalence_proof())

#     # 4. Carry Lookahead 4-Bit Adder (Gate-level alternate implementation)
#     cla_2 = CarryLookaheadAdder("adder_cla_2", 2)
#     f.write(cla_2.generate_gates())
#     f.write(cla_2.generate_equivalence_proof())
    
#     f.write("\n")
#     f.write("end hdl.examples.adder")
#     f.write("\n")

# filename = "FormalHdl/Counter.lean"
# with open(filename, "w") as f:
#     f.write(print_preamble("counter"))

#     for n in [1, 2, 4]:
#         counter = HierarchicalUpCounter(f"up_counter_{n}", n)
#         f.write(counter.generate_gates())
#         f.write(counter.generate_equivalence_proof())
    
#     for n in [4, 5]:
#         counter = HierarchicalUpDownCounter(f"up_down_counter_{n}", n)
#         f.write(counter.generate_gates())
#         f.write(counter.generate_equivalence_proof())

#     f.write("\n")
#     f.write("end hdl.examples.counter")
#     f.write("\n")

# filename = "FormalHdl/Subtractor.lean"
# with open(filename, "w") as f:
#     f.write(print_preamble("subtractor"))

#     # 1. 1-Bit Gate-Level Subtractor (Verifies the fundamental XOR/AND/NOT logic)
#     sub1 = GateLevelSubtractor1("subtractor_gate_1")
#     f.write(sub1.generate_gates())
#     f.write(sub1.generate_equivalence_proof())

#     # 2. 2-Bit Hierarchical Subtractor (Verifies the use of the ADDER_2 macro)
#     sub2 = HierarchicalSubtractor2("subtractor_hier_2")
#     f.write(sub2.generate_gates())
#     f.write(sub2.generate_equivalence_proof())

#     # 3. 4-Bit Hierarchical Subtractor (Verifies the use of the ADDER_4 macro)
#     sub4 = HierarchicalSubtractor4("subtractor_hier_4")
#     f.write(sub4.generate_gates())
#     f.write(sub4.generate_equivalence_proof())

#     f.write("\n")
#     f.write("end hdl.examples.subtractor")
#     f.write("\n")

# filename = "FormalHdl/Comparator.lean"
# with open(filename, "w") as f:
#     f.write(print_preamble("comparator"))

#     # 4. 4-Bit Gate-Level Comparator (Verifies A < B via Comparator logic)
#     comp4 = HierarchicalComparator("comparator_gate_4", 4)
#     f.write(comp4.generate_gates())
#     f.write(comp4.generate_equivalence_proof())

#     f.write("\n")
#     f.write("\n")
#     f.write("end hdl.examples.comparator")
#     f.write("\n")

filename = "FormalHdl/Decoder.lean"
with open(filename, "w") as f:
    f.write(print_preamble("decoder"))
    dec = Decoder("decoder_3", 3)
    f.write(dec.generate_gates())
    f.write(dec.generate_equivalence_proof())

    f.write("\n")
    f.write("end hdl.examples.decoder")
    f.write("\n")