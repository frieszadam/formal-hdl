# build_parking_lot.py
from components import VerifiedComponent, HierarchicalComparator

class ParkingLotCounter(VerifiedComponent):
    """The Parking Lot System: FSM + 5-bit Up/Down Counter + Comparators"""
    def __init__(self, name: str):
        self.occupancy_bus = []
        self.full_id = None
        self.empty_id = None
        self.enter_id = None
        self.exit_id = None
        # Capacity is 8, which requires exactly 4 bits (to represent 0 through 8)
        super().__init__(name, 4) 

    def _build_netlist(self):
        # --------------------------------------------------------
        # 1. Inputs & State Elements (DFFs)
        # --------------------------------------------------------
        self._add_gate("Outer", "INPUT", [])
        self._add_gate("Inner", "INPUT", [])
        
        # FSM State DFFs (3 bits)
        for i in range(3):
            self._add_gate(f"FSM_PS_{i}", "DFF", [f"FSM_NS_{i}"])
            
        # Counter State DFFs (4 bits instead of 5)
        for i in range(4):
            self._add_gate(f"Q_{i}", "DFF", [f"Next_Q_{i}"])
            self.occupancy_bus.append(self.current_id - 1)

        self._add_gate("Not_Outer", "NOT", ["Outer"])
        self._add_gate("Not_Inner", "NOT", ["Inner"])

        # --------------------------------------------------------
        # 2. FSM Combinational Logic (One-Hot Decoder -> Target SOP)
        # --------------------------------------------------------
        # Decode the 3-bit state into one-hot wires using the verified macro.
        # Order is LSB to MSB: [PS_0, PS_1, PS_2]
        decoder_inputs = ["FSM_PS_0", "FSM_PS_1", "FSM_PS_2"]
        
        self._add_gate("S_A", "DECODER_3 0", decoder_inputs) # 000
        self._add_gate("S_B", "DECODER_3 1", decoder_inputs) # 001
        self._add_gate("S_D", "DECODER_3 2", decoder_inputs) # 010
        self._add_gate("S_C", "DECODER_3 3", decoder_inputs) # 011
        self._add_gate("S_I", "DECODER_3 4", decoder_inputs) # 100
        self._add_gate("S_G", "DECODER_3 5", decoder_inputs) # 101
        self._add_gate("S_H", "DECODER_3 6", decoder_inputs) # 110

        # Input Decoders
        self._add_gate("In_00", "AND", ["Not_Outer", "Not_Inner"])
        self._add_gate("In_10", "AND", ["Outer", "Not_Inner"])
        self._add_gate("In_01", "AND", ["Not_Outer", "Inner"])
        self._add_gate("In_11", "AND", ["Outer", "Inner"])

        self._add_gate("A_10", "AND", ["S_A", "In_10"])
        self._add_gate("B_10", "AND", ["S_B", "In_10"])
        self._add_gate("To_B", "OR", ["A_10", "B_10"])

        self._add_gate("B_11", "AND", ["S_B", "In_11"])
        self._add_gate("C_11", "AND", ["S_C", "In_11"])
        self._add_gate("To_C", "OR", ["B_11", "C_11"])

        self._add_gate("C_01", "AND", ["S_C", "In_01"])
        self._add_gate("D_01", "AND", ["S_D", "In_01"])
        self._add_gate("To_D", "OR", ["C_01", "D_01"])

        self._add_gate("A_01", "AND", ["S_A", "In_01"])
        self._add_gate("G_01", "AND", ["S_G", "In_01"])
        self._add_gate("To_G", "OR", ["A_01", "G_01"])

        self._add_gate("G_11", "AND", ["S_G", "In_11"])
        self._add_gate("H_11", "AND", ["S_H", "In_11"])
        self._add_gate("To_H", "OR", ["G_11", "H_11"])

        self._add_gate("H_10", "AND", ["S_H", "In_10"])
        self._add_gate("I_10", "AND", ["S_I", "In_10"])
        self._add_gate("To_I", "OR", ["H_10", "I_10"])

        # NS_0 is 1 for targets B(001), C(011), G(101)
        self._add_gate("NS0_tmp", "OR", ["To_B", "To_C"])
        self._add_gate("FSM_NS_0", "OR", ["NS0_tmp", "To_G"])

        # NS_1 is 1 for targets D(010), C(011), H(110)
        self._add_gate("NS1_tmp", "OR", ["To_D", "To_C"])
        self._add_gate("FSM_NS_1", "OR", ["NS1_tmp", "To_H"])

        # NS_2 is 1 for targets I(100), G(101), H(110)
        self._add_gate("NS2_tmp", "OR", ["To_I", "To_G"])
        self._add_gate("FSM_NS_2", "OR", ["NS2_tmp", "To_H"])

        # Enter Pulse = State D & In_00
        self._add_gate("Enter", "AND", ["S_D", "In_00"])
        self.enter_id = self.current_id - 1
        
        # Exit Pulse = State I & In_00
        self._add_gate("Exit", "AND", ["S_I", "In_00"])
        self.exit_id = self.current_id - 1

        # --------------------------------------------------------
        # 3. Counter Datapath (Using Primitive UP_DOWN_COUNT_4)
        # --------------------------------------------------------
        # Inputs: [Incr, Decr, Q_0, Q_1, Q_2, Q_3]
        counter_inputs = ["Enter", "Exit", "Q_0", "Q_1", "Q_2", "Q_3"]
        
        # Instantiate the verified macro for each bit of the next state
        for i in range(4):
            self._add_gate(f"Next_Q_{i}", f"UP_DOWN_COUNT_4 {i}", counter_inputs)

        # --------------------------------------------------------
        # 4. Status Flags (Using Primitive COMP_4)
        # --------------------------------------------------------
        # We need physical Logic-0 and Logic-1 signals for the comparator's B buses
        self._add_gate("Logic_0", "AND", ["Enter", "Exit"]) # Enter and Exit are mutually exclusive = 0
        self._add_gate("Logic_1", "NOT", ["Logic_0"])       # NOT 0 = 1

        # EMPTY := Occupancy < 1. 
        # B-Bus = 1 (LSB is 1, others 0 -> [1, 0, 0, 0])
        empty_b_bus = ["Logic_1", "Logic_0", "Logic_0", "Logic_0"]
        empty_inputs = ["Q_0", "Q_1", "Q_2", "Q_3"] + empty_b_bus
        self._add_gate("EMPTY", "COMP_4", empty_inputs)
        self.empty_id = self.current_id - 1

        # FULL := Occupancy == 8.
        # Since occupancy strictly cannot exceed 8, "Occupancy == 8" is mathematically 
        # equivalent to "!(Occupancy < 8)".
        # B-Bus = 8 (MSB is 1, others 0 -> [0, 0, 0, 1])
        full_b_bus = ["Logic_0", "Logic_0", "Logic_0", "Logic_1"]
        full_inputs = ["Q_0", "Q_1", "Q_2", "Q_3"] + full_b_bus
        self._add_gate("Occ_lt_8", "COMP_4", full_inputs)
        self._add_gate("FULL", "NOT", ["Occ_lt_8"])
        self.full_id = self.current_id - 1
    
    def generate_gates(self) -> str:
        base_out = super().generate_gates()
        total = len(self.gates)
        def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
        
        out = [base_out]
        out.append(f"def occupancy_bus_{self.name} : List (Fin {total}) := {fin_list(self.occupancy_bus)}")
        out.append(f"def full_{self.name} : Fin {total} := ⟨{self.full_id}, by decide⟩")
        out.append(f"def empty_{self.name} : Fin {total} := ⟨{self.empty_id}, by decide⟩")
        out.append(f"def enter_{self.name} : Fin {total} := ⟨{self.enter_id}, by decide⟩")
        out.append(f"def exit_{self.name} : Fin {total} := ⟨{self.exit_id}, by decide⟩")
        out.append(f"def outer_{self.name} : Fin {total} := ⟨{self.wire_to_id['Outer']}, by decide⟩")
        out.append(f"def inner_{self.name} : Fin {total} := ⟨{self.wire_to_id['Inner']}, by decide⟩\n")
        return "\n".join(out)

    def generate_equivalence_proof(self) -> str:
        total = len(self.gates)
        out = [f"\n-- =========================================="]
        out.append(f"-- AST BOUNDARY LEMMAS & PROOF: {self.name}")
        out.append(f"-- ==========================================\n")
        
        lemma_names = []
        
        # 1. Input & State DFF Lemmas
        for node in self.state_bounds:
            idx = self.wire_to_id[node]
            lname = f"ast_{self.name}_{node.lower()}"
            # Not adding state bounds to lemma_names to prevent over-eager rewriting
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
            
        # 2. Next State Logic and Output Bounds
        output_wires = [
            "FSM_NS_0", "FSM_NS_1", "FSM_NS_2",
            "Next_Q_0", "Next_Q_1", "Next_Q_2", "Next_Q_3",
            "Enter", "Exit", "FULL", "EMPTY"
        ]
        for wire in output_wires:
            lname = f"ast_{self.name}_{wire.lower()}"
            lemma_names.append(lname)
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (i : Fin {total}) (hi : i.val = {self.wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {self.name} {total} i) = {self._get_bool_expr(wire)} := by cases i; subst hi; rfl")
            
        # 3. runCycle Sequence Equivalence
        cycle_lemmas = []
        sequential_pairs = [
            ("FSM_PS_0", "FSM_NS_0"), ("FSM_PS_1", "FSM_NS_1"), ("FSM_PS_2", "FSM_NS_2"),
            ("Q_0", "Next_Q_0"), ("Q_1", "Next_Q_1"), ("Q_2", "Next_Q_2"), ("Q_3", "Next_Q_3")
        ]
        for ps, ns in sequential_pairs:
            lname = f"runCycle_{self.name}_{ps.lower()}"
            cycle_lemmas.append(lname)
            ps_id = self.wire_to_id[ps]
            ns_id = self.wire_to_id[ns]
            out.append(f"@[simp] lemma {lname} (s : State {self.name}) (env : List Bool) (idx : Fin {total}) (h : idx.val = {ps_id} := by decide) : (runCycle {self.name} s env) idx = evalCombinatorial {self.name} {total} s ⟨{ns_id}, by decide⟩ := by cases idx; subst h; rfl")

        # 4. Proof Block Generator Helper
        def build_proof_block(is_sequential: bool):
            block = []
            if is_sequential:
                block.append("    intro s env_outer env_inner")
            else:
                block.append("    intro s")
                
            block.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {self.name} {total} s i = evalExpr s (unrollDAG {self.name} {total} i) := by fin_cases i <;> rfl")
            
            # Unfold math definitions
            math_defs = ["decode_sensor_state", "is_enter", "is_exit", "next_sensor_state"]
            block.append(f"    simp only [{', '.join(math_defs)}]")
            block.append(f"    simp only [occupancy_bus_{self.name}, full_{self.name}, empty_{self.name}, enter_{self.name}, exit_{self.name}, outer_{self.name}, inner_{self.name}, bitsToNat]")
            
            if is_sequential:
                block.append(f"    simp only [{', '.join(cycle_lemmas)}]")
                
            block.append(f"    simp only [equiv]")
            block.append(f"    simp only [{', '.join(lemma_names)}]")
            
            # Generalize state variables for case splitting
            cases_tactics = []
            for node in self.state_bounds:
                v_name = f"val_{node.lower()}"
                h_name = f"h_{v_name}"
                block.append(f"    generalize {h_name} : s \u27e8{self.wire_to_id[node]}, by decide\u27e9 = {v_name}")
                cases_tactics.append(f"cases {v_name}")
                
            if is_sequential:
                cases_tactics.extend(["cases env_outer", "cases env_inner"])
                
            # Execute the case split
            cases_str = ' <;> '.join(cases_tactics)
            block.append(f"    {cases_str} <;> decide")
            return "\n".join(block)

        # 5. Typeclass Instantiation
        out.append(f"\ninstance instIsParkingLotCounter_{self.name} : IsParkingLotCounter {self.name}")
        out.append(f"  outer_{self.name} inner_{self.name}")
        out.append(f"  ⟨{self.wire_to_id['FSM_PS_2']}, by decide⟩ ⟨{self.wire_to_id['FSM_PS_1']}, by decide⟩ ⟨{self.wire_to_id['FSM_PS_0']}, by decide⟩")
        out.append(f"  occupancy_bus_{self.name} full_{self.name} empty_{self.name}")
        out.append(f"  enter_{self.name} exit_{self.name} where")
        
        out.append("  widths_match := by decide")
        out.append("  inputs_are_valid := by decide")
        
        out.append("  status_full := by")
        out.append(build_proof_block(False))
        
        out.append("  status_empty := by")
        out.append(build_proof_block(False))
        
        out.append("  pulses_correct := by")
        out.append(build_proof_block(False))
        
        out.append("  valid_transition := by")
        out.append(build_proof_block(True))
        
        return "\n".join(out)
    
if __name__ == "__main__":
    lot = ParkingLotCounter("parking_lot")
    
    with open("FormalHdl/ParkingLotCircuit.lean", "w") as f:
        f.write("-- Generated Parking Lot System\n")
        f.write("import FormalHdl.Defs\n")
        f.write("namespace hdl.examples.parking_lot\nopen hdl\n\n")
        
        f.write(lot.generate_gates())
        f.write(lot.generate_equivalence_proof())

        f.write("\nend hdl.examples.parking_lot\n")