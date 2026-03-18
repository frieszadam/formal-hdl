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
        elif op == "COMP_LT_4":
            self.gates.append("Gate.mk .comp_lt_4 false")
        elif op.startswith("INC_4"):
            bit = op.split(" ")[1]
            self.gates.append(f"Gate.mk (.inc_4 ⟨{bit}, by decide⟩) false")
            
        # Physical Logic Gates
        else:
            self.gates.append(f"Gate.mk .{op.lower()}_ false")
            
        self.connections_str.append(in_wires)
        self.current_id += 1

    def _get_bool_expr(self, wire: str) -> str:
        """Recursively unrolls logic and hierarchical macros into Lean math."""
        op, args = self.gate_defs[wire]
        if op == "INPUT" or op == "DFF":
            return f"s ⟨{self.wire_to_id[wire]}, by decide⟩"
        
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


class HierarchicalAdder2(Adder):
    """Hierarchical Adder that automatically specifies n=2."""
    def __init__(self, name: str):
        super().__init__(name, 2)

    def _build_netlist(self):
        self._add_gate("Cin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])

        # Bit 0
        inputs_0 = ["Cin", "A_0", "B_0"]
        self._add_gate("Sum_0", "ADDER_1 0", inputs_0)
        self._add_gate("C_1", "ADDER_1 1", inputs_0)

        # Bit 1
        inputs_1 = ["C_1", "A_1", "B_1"]
        self._add_gate("Sum_1", "ADDER_1 0", inputs_1)
        self._add_gate("Cout", "ADDER_1 1", inputs_1)


class HierarchicalAdder4(Adder):
    """Hierarchical Adder that automatically specifies n=4."""
    def __init__(self, name: str):
        super().__init__(name, 4)

    def _build_netlist(self):
        self._add_gate("Cin", "INPUT", [])
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self._add_gate(f"B_{i}", "INPUT", [])

        # Lower 2 bits
        inputs_lo = ["Cin", "A_0", "A_1", "B_0", "B_1"]
        self._add_gate("Sum_0", "ADDER_2 0", inputs_lo)
        self._add_gate("Sum_1", "ADDER_2 1", inputs_lo)
        self._add_gate("C_2", "ADDER_2 2", inputs_lo)

        # Upper 2 bits
        inputs_hi = ["C_2", "A_2", "A_3", "B_2", "B_3"]
        self._add_gate("Sum_2", "ADDER_2 0", inputs_hi)
        self._add_gate("Sum_3", "ADDER_2 1", inputs_hi)
        self._add_gate("Cout", "ADDER_2 2", inputs_hi)


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


class MacroComparator(VerifiedComponent):
    """Generates IsComparator proof and theorem for the Standard Cell Comparator."""
    def __init__(self, name: str, n_bits: int):
        self.a_bus = []
        self.b_bus = []
        self.out_id = None
        super().__init__(name, n_bits)

    def _build_netlist(self):
        for i in range(self.n):
            self._add_gate(f"A_{i}", "INPUT", [])
            self.a_bus.append(self.current_id - 1)
        for i in range(self.n):
            self._add_gate(f"B_{i}", "INPUT", [])
            self.b_bus.append(self.current_id - 1)

        inputs = [f"A_{i}" for i in range(self.n)] + [f"B_{i}" for i in range(self.n)]
        self._add_gate("A_lt_B", "COMP_LT_4", inputs)
        self.out_id = self.current_id - 1

    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def a_bus_{self.name} : List (Fin {total}) := {fin_list(self.a_bus)}")
        out.append(f"def b_bus_{self.name} : List (Fin {total}) := {fin_list(self.b_bus)}")
        out.append(f"def out_{self.name} : Fin {total} := ⟨{self.out_id}, by decide⟩\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"-- AST BOUNDARY LEMMAS & PROOF: {self.name}"]
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
            
        out.append(f"\ninstance instIsComp_{self.name} : IsComparator {self.name} {self.n} a_bus_{self.name} b_bus_{self.name} out_{self.name} where")
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by intro i h; fin_cases h <;> rfl")
        out.append("  comp_correct := by")
        out.append("    intro s")
        out.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {total} s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
        out.append(f"    simp only [a_bus_{self.name}, b_bus_{self.name}, out_{self.name}, bitsToNat]")
        out.append(f"    simp only [equiv]")
        lemmas = [f"ast_{self.name}_{node.lower()}" for node in self.state_bounds]
        out.append(f"    simp only [{', '.join(lemmas)}]")
        
        cases_list = []
        for name in self.state_bounds:
            v_name = name.lower()
            cases_list.append(f"cases {v_name}")
            out.append(f"    generalize h_{v_name} : s ⟨{self.wire_to_id[name]}, by decide⟩ = {v_name}")
            
        out.append(f"    {' <;> '.join(cases_list)} <;> decide")
        out.append(f"\ntheorem valid_{self.name}_exists : ValidComp{self.n}Exists := ⟨{self.name}, _, _, _, instIsComp_{self.name}⟩\n")
        return "\n".join(out)

def print_preamble():
    out = ["-- Adam Friesz, Winter 2026"]
    out.append("import FormalHdl.Defs")
    out.append("namespace hdl.examples.adder")
    out.append("open hdl")
    out.append("set_option linter.style.longLine false")
    out.append("set_option linter.style.whitespace false")
    out.append("\n")
    return "\n".join(out)

filename = "FormalHdl/Adder.lean"
with open(filename, "w") as f:
    f.write(print_preamble())
    # 1. Gate Level 1-Bit Adder (Proves the 1-bit contract)
    rca_1 = RippleCarryAdder("adder_rca_1", 1)
    f.write(rca_1.generate_gates())
    f.write(rca_1.generate_equivalence_proof())

    # 2. Hierarchical 2-Bit Adder (Builds using the 1-bit Macro)
    hierarchical_2 = HierarchicalAdder2("adder_hierarchical_2")
    f.write(hierarchical_2.generate_gates())
    f.write(hierarchical_2.generate_equivalence_proof())

    # 3. Hierarchical 4-Bit Adder (Builds using the 2-bit Macro)
    hierarchical_4 = HierarchicalAdder4("adder_hierarchical_4")
    f.write(hierarchical_4.generate_gates())
    f.write(hierarchical_4.generate_equivalence_proof())

    # 4. Carry Lookahead 4-Bit Adder (Gate-level alternate implementation)
    cla_2 = CarryLookaheadAdder("adder_cla_2", 2)
    f.write(cla_2.generate_gates())
    f.write(cla_2.generate_equivalence_proof())
    
    f.write("\n")
    f.write("end hdl.examples.adder")
    f.write("\n")
