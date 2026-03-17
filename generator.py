import re

def generate_adder_bench(n: int) -> str:
    """Phase 1: Generates standard .bench format."""
    lines = []
    lines.append("INPUT(Cin)")
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

def compile_to_lean(bench_text: str, n: int) -> str:
    """Phase 2: Compiles to Lean with Bus Indexing."""
    wire_to_id = {}
    gates, connections = [], []
    current_id = 0
    
    # Track buses for the IsAdder class
    a_bus, b_bus, sum_bus = [], [], []
    cout_id = None

    for line in bench_text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"): continue
            
        if line.startswith("INPUT"):
            name = line.split("(")[1].split(")")[0]
            wire_to_id[name] = current_id
            if name.startswith("A_"): a_bus.append(current_id)
            elif name.startswith("B_"): b_bus.append(current_id)
            gates.append("igate false")
            connections.append("[]")
            current_id += 1
            
        elif "=" in line:
            out_wire, rest = line.split("=")
            out_wire = out_wire.strip()
            gate_type = rest.split("(")[0].strip()
            in_wires = [w.strip() for w in rest.split("(")[1].split(")")[0].split(",")]
            
            in_ids = [str(wire_to_id[w]) for w in in_wires]
            wire_to_id[out_wire] = current_id
            
            if out_wire.startswith("Sum_"): sum_bus.append(current_id)
            if out_wire == "Cout": cout_id = current_id
            
            gates.append(f"{gate_type.lower()} false")
            connections.append(f"[{', '.join(in_ids)}]")
            current_id += 1

    # Format Lean Code
    out = [f"def adder_{n}_gates : List Gate := [\n  " + ",\n  ".join(gates) + "\n]\n"]
    out.append(f"def adder_{n}_conns : List (List Nat) := [\n  " + ",\n  ".join(connections) + "\n]\n")
    
    # Generate the Bus definitions
    total = len(gates)
    def to_fin_list(l): return "[" + ", ".join([f"⟨{x}, by decide⟩" for x in l]) + "]"
    
    out.append(f"def a_bus_{n} : List (Fin {total}) := {to_fin_list(a_bus)}")
    out.append(f"def b_bus_{n} : List (Fin {total}) := {to_fin_list(b_bus)}")
    out.append(f"def sum_bus_{n} : List (Fin {total}) := {to_fin_list(sum_bus)}")
    out.append(f"def cout_{n} : Fin {total} := ⟨{cout_id}, by decide⟩")
    
    return "\n".join(out)

print(compile_to_lean(generate_adder_bench(2), 2))