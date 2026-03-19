# FormalHDL — Verified Digital Circuit Components in Lean 4

**Author:** Adam Friesz, Winter 2026

## Goal

FormalHDL is a Lean 4 library for defining, simulating, and formally verifying gate-level digital circuits. The project provides:

1. A **circuit model** — a DAG of typed gates with a topological-order constraint enforced in the type system.
2. A **simulator** — a pure functional evaluator that runs combinatorial propagation and clocked (DFF) state steps.
3. A **contract language** — Lean typeclasses (`IsAdder`, `IsSubtractor`, `IsComparator`, `IsUpCounter`, `IsUpDownCounter`, `IsDecoder`) that state what it means for a concrete gate netlist to implement a mathematical function.
4. A **proof strategy** — an AST unroller (`unrollDAG`) that converts the netlist evaluator into a symbolic expression, followed by Boolean exhaustion via `decide`.
5. A **library of verified components** — six families of arithmetic/sequential circuits (adders, subtractors, a comparator, up-counters, an up/down-counter, and a decoder), each accompanied by a machine-checked proof of correctness.

---

## File Structure

| File | Contents |
|---|---|
| `Defs.lean` | Core types, evaluator, contract typeclasses, AST infrastructure |
| `Adder.lean` | Three verified adder designs (RCA-1, hierarchical-2, hierarchical-4, CLA-2) |
| `Subtractor.lean` | Three verified subtractors (gate-1, hierarchical-2, hierarchical-4) |
| `Comparator.lean` | A verified 4-bit unsigned comparator |
| `Counter.lean` | Verified up-counters (1-, 2-, 4-bit) and up/down-counters (4- and 5-bit) |
| `Decoder.lean` | A verified 3-to-8 decoder |
| `components.py` | Python code generator that emits the Lean netlist definitions |

---

## Main Definitions

### `Defs.lean`

#### `bitsToNat`
```
bitsToNat {N : Nat} (s : Fin N → Bool) : List (Fin N) → Nat
```
Converts a list of gate indices (a "bus") to a natural number using LSB-first positional notation. Used in all arithmetic correctness statements.

#### `GateKind`
An inductive type enumerating every primitive gate the framework knows about: `igate` (primary input), `dff` (D flip-flop), `not_`, `and_`, `or_`, `xor_`, and parameterised compound cells `adder_1/2/4`, `comp_1/2/4`, `up_down_count_1/2/4`, `decoder_3`. Each constructor carries the output-bit index for multi-output cells.

#### `GateKind.ni`
```
GateKind.ni : GateKind → Nat
```
Returns the number of inputs for each gate kind. Used to type-check wiring.

#### `Circuit`
```
structure Circuit where
  gates   : List Gate
  wiring  : (i : Fin gates.length) → Fin (gates.get i).kind.ni → Fin gates.length
  is_dag  : ∀ i p, (gates.get i).kind.is_seq = false → wiring i p < i
```
A gate-level netlist. `is_dag` enforces that every combinatorial gate's input comes from a gate with a strictly smaller index, guaranteeing acyclicity and a well-defined evaluation order. Sequential gates (`dff`) are exempt so they can form feedback loops across clock boundaries.

#### `evalCombinatorial`
```
evalCombinatorial (C : Circuit) (fuel : Nat)
  (curr_state : Fin C.gates.length → Bool)
  (i : Fin C.gates.length) : Bool
```
Recursively evaluates gate `i` in circuit `C` using `fuel` as a termination counter. For DFFs it returns the stored state; for combinatorial gates it recursively evaluates inputs and applies the gate function. Because `is_dag` ensures strict index decrease, `fuel = C.gates.length` always suffices.

#### `step` / `runCycle` / `runCycles`
```
step      (C : Circuit) (stable_state : State C) (env_inputs : List Bool) : State C
runCycle  (C : Circuit) (s : State C) (env_inputs : List Bool)            : State C
runCycles (C : Circuit) (s : State C) : List (List Bool) → List (State C)
```
- `step` computes the next register state: primary inputs take new values from `env_inputs`; DFFs capture the value of their combinatorial predecessor.
- `runCycle` first stabilises the combinatorial outputs, then calls `step`.
- `runCycles` threads an input trace through the circuit, collecting the state snapshot before each cycle.

#### `compute_adder_1 / 2 / 4`
Pure natural-number implementations of 1-, 2-, and 4-bit ripple-carry addition. Used as reference functions inside gate evaluations and in the AST unroller proofs.

#### `CombExpr` / `evalExpr` / `unrollDAG`
```
inductive CombExpr (Idx : Type) ...
evalExpr  {Idx} (state : Idx → Bool) : CombExpr Idx → Bool
unrollDAG (C : Circuit) (fuel : Nat) (i : Fin C.gates.length) : CombExpr (Fin C.gates.length)
```
`CombExpr` is a symbolic Boolean expression AST mirroring the gate vocabulary. `evalExpr` is its denotational semantics. `unrollDAG` converts a circuit node into a `CombExpr` by recursively inlining its combinatorial fanin cone. The key proof lemma used throughout is:
```
evalCombinatorial C C.gates.length s i = evalExpr s (unrollDAG C C.gates.length i)
```
which is established per-circuit by `fin_cases` + `rfl`.

#### `AstCircuit` / `stepAst`
An alternative circuit representation as a function from node index to `CombExpr`. `stepAst` evaluates one clock cycle using `evalExpr` directly; `to_ast` converts a `Circuit` into an `AstCircuit`.

---

### Contract Typeclasses

Each typeclass bundles three things: a width-consistency proof, an input-validity proof (all bus pins are primary inputs), and a correctness theorem stated in terms of natural numbers.

#### `IsAdder C n a_bus b_bus sum_bus cin cout`
States that for every circuit state `s`:
```
bitsToNat s sum_bus + (if s cout then 2^n else 0) =
  bitsToNat s a_bus + bitsToNat s b_bus + (if s cin then 1 else 0)
```

#### `IsSubtractor C n a_bus b_bus diff_bus bin bout`
Uses the borrow-complement form to avoid negative integers:
```
A + Bout·2^n = B + Diff + Bin
```

#### `IsComparator C n a_bus b_bus out`
States `s out = (bitsToNat s a_bus < bitsToNat s b_bus)`.

#### `IsUpCounter C n q_bus inc`
States two properties (universally quantified over states and environment inputs):
- `s inc = true  →  bitsToNat (runCycle C s env) q_bus = (bitsToNat s q_bus + 1) % 2^n`
- `s inc = false →  bitsToNat (runCycle C s env) q_bus = bitsToNat s q_bus`

#### `IsUpDownCounter C n q_bus incr decr`
States three properties:
- `incr=1, decr=0  →  count up by 1 mod 2^n`
- `incr=0, decr=1  →  count down by 1 mod 2^n  (equivalently, add 2^n-1)`
- `incr=decr       →  hold (both asserted or both de-asserted)`

#### `IsDecoder C n sel_bus out_bus`
States `bitsToNat s out_bus = 2^(bitsToNat s sel_bus)`, i.e., exactly the output line corresponding to the binary selector address is high.

---

### Specific Verified-Instance Typeclasses

Thin wrappers that lock in the bit-width:

| Typeclass | Width | Kind |
|---|---|---|
| `VerifiedAdder1/2/4` | 1, 2, 4 | Adder |
| `VerifiedSubtractor1/2/4` | 1, 2, 4 | Subtractor |
| `VerifiedComp4` | 4 | Comparator |
| `VerifiedUpCounter1/2/4` | 1, 2, 4 | Up-counter |
| `VerifiedUpDownCounter4/5` | 4, 5 | Up/Down-counter |
| `VerifiedDecoder3` | 3→8 | Decoder |

---

## Main Theorems / Instances

All theorems are stated as `instance` declarations so that Lean's typeclass system can resolve them automatically.

### Adders (`Adder.lean`)

| Instance | Circuit | Theorem |
|---|---|---|
| `instVerifiedAdder1_adder_rca_1` | `adder_rca_1` | 8-gate ripple-carry full adder over 1 bit is a correct `VerifiedAdder1` |
| `instVerifiedAdder2_adder_hierarchical_2` | `adder_hierarchical_2` | Hierarchical 2-bit adder built from two `adder_1` cells is a correct `VerifiedAdder2` |
| `instVerifiedAdder4_adder_hierarchical_4` | `adder_hierarchical_4` | Hierarchical 4-bit adder built from two `adder_2` cells is a correct `VerifiedAdder4` |
| `instVerifiedAdder2_adder_cla_2` | `adder_cla_2` | 18-gate 2-bit carry-lookahead adder is a correct `VerifiedAdder2` |

### Subtractors (`Subtractor.lean`)

| Instance | Circuit | Theorem |
|---|---|---|
| `instVerifiedSubtractor1_subtractor_gate_1` | `subtractor_gate_1` | 11-gate borrow-propagate subtractor over 1 bit |
| `instVerifiedSubtractor2_subtractor_hier_2` | `subtractor_hier_2` | 2-bit subtractor via two's-complement: negates B, feeds into `adder_2` |
| `instVerifiedSubtractor4_subtractor_hier_4` | `subtractor_hier_4` | 4-bit subtractor via two's-complement feeding `adder_4` |

### Comparator (`Comparator.lean`)

| Instance | Circuit | Theorem |
|---|---|---|
| `instIsComp_comparator_gate_4` | `comparator_gate_4` | 17-gate 4-bit unsigned less-than comparator (implemented via subtractor carry-out) |

### Counters (`Counter.lean`)

| Instance | Circuit | Theorem |
|---|---|---|
| `instVerifiedUpCounter1_up_counter_1` | `up_counter_1` | 1-bit synchronous up-counter with enable |
| `instVerifiedUpCounter2_up_counter_2` | `up_counter_2` | 2-bit synchronous up-counter |
| `instVerifiedUpCounter4_up_counter_4` | `up_counter_4` | 4-bit synchronous up-counter |
| `instVerifiedUpDownCounter4_up_down_counter_4` | `up_down_counter_4` | 4-bit up/down-counter; hold when inputs agree |
| `instVerifiedUpDownCounter5_up_down_counter_5` | `up_down_counter_5` | 5-bit up/down-counter; 5th bit computed via carry out of the lower 4-bit slice |

### Decoder (`Decoder.lean`)

| Instance | Circuit | Theorem |
|---|---|---|
| `instVerifiedDecoder3_decoder_3` | `decoder_3` | 22-gate 3-to-8 decoder; output bus encodes exactly one-hot position |

---

## Proof Strategy

Every correctness proof follows the same four-step recipe:

1. **Unroll equivalence.** Establish `evalCombinatorial C C.gates.length s i = evalExpr s (unrollDAG C C.gates.length i)` for all gate indices by `fin_cases i <;> rfl`. This step works because both sides reduce definitionally once the index is known.

2. **Boundary lemmas.** For each interesting gate (inputs and outputs), provide a `@[simp]` lemma of the form:
   ```
   evalExpr s (unrollDAG C n ⟨k, _⟩) = <explicit Boolean expression>
   ```
   These are proved by `rfl` after fixing the index.

3. **Symbolic substitution.** `simp only [equiv, boundary_lemmas...]` rewrites the goal from a circuit evaluation to a purely Boolean proposition over fresh `Bool` variables.

4. **Boolean exhaustion.** `cases b₁ <;> cases b₂ <;> ... <;> decide` checks all 2^k input combinations.

Sequential proofs additionally use `runCycle` lemmas that unfold `(runCycle C s env) ⟨i, _⟩` to the appropriate `evalCombinatorial` call.

---

## References

- A. Cimatti, E. Clarke, E. Giunchiglia, F. Giunchiglia, M. Pistore, M. Roveri, R. Sebastiani, A. Tacchella. "NuSMV 2: An OpenSource Tool for Symbolic Model Checking." *CAV 2002*.
- K. Slind, M. Norrish. "A Brief Overview of HOL4." *TPHOLs 2008*.
- G. Gonthier et al. "A Machine-Checked Proof of the Odd Order Theorem." *ITP 2013*.
- The Mathlib Community. "The Lean 4 Mathematical Library." https://leanprover-community.github.io/mathlib4_docs/
- Patterson, D., Hennessy, J. *Computer Organization and Design: The Hardware/Software Interface.* Morgan Kaufmann.
- Weste, N., Harris, D. *CMOS VLSI Design: A Circuits and Systems Perspective.* Addison-Wesley.

---

## Future Work

- **Carry-lookahead and prefix adders.** The framework already contains `comp_4` and `adder_4` cells; a Kogge–Stone or Brent–Kung 4-bit adder would demonstrate that `VerifiedAdder4` admits multiple correct implementations.
- **Parametric proofs.** Current correctness theorems are for fixed widths (1, 2, 4, 5 bits). A general inductive proof of the form "if `VerifiedAdder n` holds then `VerifiedAdder (2n)` holds for the hierarchical composition" would eliminate the per-width case explosion.
- **Larger sequential circuits.** The counter and decoder infrastructure could be extended to registers, shift registers, and finite-state machines. The `runCycles` function already supports multi-cycle traces.
- **Automated netlist generation.** `components.py` currently generates Lean source text; integrating it as a Lean meta-program (via `Lean.Elab`) would make circuit import type-safe.
- **LTL / CTL model checking.** The `runCycles` trace semantics provides a natural hook for expressing and checking temporal properties on verified circuits.
- **Timing and area metrics.** The `GateKind` type already encodes structural information; gate-count and critical-path depth could be computed and proved as additional contracts alongside correctness.
- **Integration with hardware synthesis flows.** Exporting verified circuits to Verilog or FIRRTL and checking equivalence with the Lean model using third-party model checkers (e.g., Yosys + ABC) would close the gap to real silicon.
