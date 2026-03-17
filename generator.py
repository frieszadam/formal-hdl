import re

def generate_rca_bench(n: int) -> str:
    """Generates the standard Ripple Carry Adder."""
    lines = ["INPUT(Cin)"]
    for i in range(n):
        lines.append(f"INPUT(A_{i})")
        lines.append(f"INPUT(B_{i})")
    
    curr_c = "Cin"
    for i in range(n):
        lines.append(f"AxB_{i} = XOR(A_{i}, B_{i})")
        lines.append(f"AaB_{i} = AND(A_{i}, B_{i})")
        lines.append(f"Sum_{i} = XOR(AxB_{i}, {curr_c})")
        lines.append(f"AxB_a_C_{i} = AND(AxB_{i}, {curr_c})")
        next_c = f"C_{i+1}" if i < n - 1 else "Cout"
        lines.append(f"{next_c} = OR(AaB_{i}, AxB_a_C_{i})")
        curr_c = next_c
    return "\n".join(lines)

def generate_cla_bench(n: int) -> str:
    """Generates a fully flattened Carry Look-Ahead Adder."""
    lines = ["INPUT(Cin)"]
    for i in range(n):
        lines.append(f"INPUT(A_{i})")
        lines.append(f"INPUT(B_{i})")

    # 1. Propagate and Generate bits
    for i in range(n):
        lines.append(f"P_{i} = XOR(A_{i}, B_{i})")
        lines.append(f"G_{i} = AND(A_{i}, B_{i})")

    # 2. Fully expanded Carry Logic
    carries = ["Cin"]
    for i in range(n):
        terms = [f"G_{i}"]
        # Generate the cascaded AND terms: P_i * P_{i-1} * ... * G_j
        for j in range(i - 1, -2, -1):
            current_wire = f"P_{i}"
            for k in range(i - 1, j, -1):
                next_wire = f"AND_{current_wire}_P_{k}"
                lines.append(f"{next_wire} = AND({current_wire}, P_{k})")
                current_wire = next_wire
            
            last_in = f"G_{j}" if j >= 0 else "Cin"
            term_wire = f"Term_{i}_{j}"
            lines.append(f"{term_wire} = AND({current_wire}, {last_in})")
            terms.append(term_wire)

        # Generate the cascaded OR tree for this carry bit
        or_wire = terms[0]
        for t in range(1, len(terms)):
            is_last = (t == len(terms) - 1)
            out_name = f"C_{i+1}" if (is_last and i < n - 1) else ("Cout" if is_last else f"OR_{i}_{t}")
            lines.append(f"{out_name} = OR({or_wire}, {terms[t]})")
            or_wire = out_name
        carries.append(or_wire)

    # 3. Sum Logic
    for i in range(n):
        lines.append(f"Sum_{i} = XOR(P_{i}, {carries[i]})")

    return "\n".join(lines)

def compile_to_lean(bench_text: str, n: int, arch: str) -> str:
    """Compiles the netlist into Lean, parameterized by architecture name."""
    wire_to_id = {}
    gate_defs = {}
    gates, connections = [], []
    current_id = 0
    a_bus, b_bus, sum_bus, inputs_list = [], [], [], []
    
    # [Netlist Parsing logic remains identical, just routing into data structures]
    for line in bench_text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"): continue
        if line.startswith("INPUT"):
            name = line.split("(")[1].split(")")[0]
            wire_to_id[name] = current_id
            gate_defs[name] = "INPUT"
            inputs_list.append(name)
            if name.startswith("A_"): a_bus.append(current_id)
            elif name.startswith("B_"): b_bus.append(current_id)
            gates.append("igate false")
            connections.append("[]")
            current_id += 1
        elif "=" in line:
            out_wire, rest = line.split("=")
            out_wire = out_wire.strip()
            op = rest.split("(")[0].strip()
            in_wires = [w.strip() for w in rest.split("(")[1].split(")")[0].split(",")]
            wire_to_id[out_wire] = current_id
            gate_defs[out_wire] = (op, in_wires)
            if out_wire.startswith("Sum_"): sum_bus.append(current_id)
            gates.append(f"{op.lower()} false")
            connections.append(f"[{', '.join([str(wire_to_id[w]) for w in in_wires])}]")
            current_id += 1

    cout_id = wire_to_id["Cout"]
    total = len(gates)
    prefix = f"adder_{arch}_{n}"

    def get_bool_expr(wire):
        if gate_defs[wire] == "INPUT": return f"s ⟨{wire_to_id[wire]}, by decide⟩"
        op, args = gate_defs[wire]
        exprs = [get_bool_expr(a) for a in args]
        if op == "AND": return f"({exprs[0]} && {exprs[1]})"
        if op == "OR":  return f"({exprs[0]} || {exprs[1]})"
        if op == "XOR": return f"({exprs[0]} ^^ {exprs[1]})"

    # Write Lean Output
    out = [f"-- {arch.upper()} {n}-Bit Adder Implementation"]
    out.append(f"def {prefix}_gates : List Gate := [\n  " + ",\n  ".join(gates) + "\n]")
    out.append(f"def {prefix}_conns : List (List Nat) := [\n  " + ",\n  ".join(connections) + "\n]")
    out.append(f"def {prefix} : Circuit := {{ gates := {prefix}_gates, wiring := mkWiring {prefix}_gates {prefix}_conns (by decide), is_dag := by decide }}")
    
    def fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
    out.append(f"def a_bus_{arch}_{n} : List (Fin {total}) := {fin_list(a_bus)}")
    out.append(f"def b_bus_{arch}_{n} : List (Fin {total}) := {fin_list(b_bus)}")
    out.append(f"def sum_bus_{arch}_{n} : List (Fin {total}) := {fin_list(sum_bus)}")
    out.append(f"def cin_{arch}_{n} : Fin {total} := ⟨{wire_to_id['Cin']}, by decide⟩")
    out.append(f"def cout_{arch}_{n} : Fin {total} := ⟨{cout_id}, by decide⟩\n")

    lemma_names = []
    for name in inputs_list:
        idx = wire_to_id[name]
        lname = f"ast_{arch}_{name.lower()}"
        lemma_names.append(lname)
        out.append(f"@[simp] lemma {lname} (s : State {prefix}) (i : Fin {total}) (hi : i.val = {idx} := by decide) : evalExpr s (unrollDAG {prefix} {total} i) = s ⟨{idx}, by decide⟩ := by cases i; subst hi; rfl")
    
    for i in range(n):
        wire = f"Sum_{i}"
        lname = f"ast_{arch}_sum_{i}"
        lemma_names.append(lname)
        out.append(f"@[simp] lemma {lname} (s : State {prefix}) (i : Fin {total}) (hi : i.val = {wire_to_id[wire]} := by decide) : evalExpr s (unrollDAG {prefix} {total} i) = {get_bool_expr(wire)} := by cases i; subst hi; rfl")
        
    out.append(f"@[simp] lemma ast_{arch}_cout_{n} (s : State {prefix}) (i : Fin {total}) (hi : i.val = {cout_id} := by decide) : evalExpr s (unrollDAG {prefix} {total} i) = {get_bool_expr('Cout')} := by cases i; subst hi; rfl")
    lemma_names.append(f"ast_{arch}_cout_{n}")

    # Generate the Proof
    out.append(f"\ninstance : IsAdder {prefix} {n} a_bus_{arch}_{n} b_bus_{arch}_{n} sum_bus_{arch}_{n} cin_{arch}_{n} cout_{arch}_{n} where")
    out.append("  widths_match := by decide")
    out.append("  inputs_are_valid := by intro i h; fin_cases h <;> rfl")
    out.append("  adder_correct := by")
    out.append(f"    intro s")
    out.append(f"    have equiv (i : Fin {total}) : evalCombinatorial {prefix} {prefix}.gates.length s i = evalExpr s (unrollDAG {prefix} {total} i) := by fin_cases i <;> rfl")
    out.append(f"    simp only [a_bus_{arch}_{n}, b_bus_{arch}_{n}, sum_bus_{arch}_{n}, cout_{arch}_{n}, cin_{arch}_{n}, bitsToNat, Bool.toNat]")
    out.append(f"    simp only [equiv]")
    out.append(f"    simp only [{', '.join(lemma_names)}]")
    
    cases_list = []
    for name in inputs_list:
        v_name = name.lower()
        cases_list.append(f"cases {v_name}")
        out.append(f"    generalize h_{v_name} : s ⟨{wire_to_id[name]}, by decide⟩ = {v_name}")
        
    out.append(f"    {' <;> '.join(cases_list)} <;> decide\n")
    
    return "\n".join(out)

# Generate both implementations!
n_bits = 2
print(compile_to_lean(generate_rca_bench(n_bits), n_bits, "rca"))
print(compile_to_lean(generate_cla_bench(n_bits), n_bits, "cla"))
