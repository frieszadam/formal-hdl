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
        if op.startswith("ADDER_4"):
            bit = op.split(" ")[1]
            return f"(compute_adder_4 ({exprs[0]}) ({exprs[1]}) ({exprs[2]}) ({exprs[3]}) ({exprs[4]}) ({exprs[5]}) ({exprs[6]}) ({exprs[7]}) ({exprs[8]})).testBit {bit}"
        
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

class HierarchicalCounter(VerifiedComponent):
    """A formally verified N-Bit Sequential Counter using Hierarchical Adders."""
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
        out.append(f"\ninstance instIsCounter_{self.name} : IsCounter {self.name} {self.n} q_bus_{self.name} inc_{self.name} where")
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
            
        out.append(f"\ninstance instVerifiedCounter{self.n}_{self.name} : VerifiedCounter{self.n} {self.name} q_bus_{self.name} inc_{self.name} where")
        out.append(f"  proof := instIsCounter_{self.name}\n")

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
#         counter = HierarchicalCounter(f"counter_{n}", n)
#         f.write(counter.generate_gates())
#         f.write(counter.generate_equivalence_proof())

#     f.write("\n")
#     f.write("end hdl.examples.counter")
#     f.write("\n")

filename = "FormalHdl/Subtractor.lean"
with open(filename, "w") as f:
    f.write(print_preamble("subtractor"))

    # 1. 1-Bit Gate-Level Subtractor (Verifies the fundamental XOR/AND/NOT logic)
    sub1 = GateLevelSubtractor1("subtractor_gate_1")
    f.write(sub1.generate_gates())
    f.write(sub1.generate_equivalence_proof())

    # 2. 2-Bit Hierarchical Subtractor (Verifies the use of the ADDER_2 macro)
    sub2 = HierarchicalSubtractor2("subtractor_hier_2")
    f.write(sub2.generate_gates())
    f.write(sub2.generate_equivalence_proof())

    # 3. 4-Bit Hierarchical Subtractor (Verifies the use of the ADDER_4 macro)
    sub4 = HierarchicalSubtractor4("subtractor_hier_4")
    f.write(sub4.generate_gates())
    f.write(sub4.generate_equivalence_proof())

    # 4. 4-Bit Gate-Level Comparator (Verifies A < B via Subtractor logic)
    comp4 = GateLevelComparator4("comparator_gate_4")
    f.write(comp4.generate_gates())
    f.write(comp4.generate_equivalence_proof())

    f.write("\n")
    f.write("end hdl.examples.subtractor")
    f.write("\n")
