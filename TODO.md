# TODO List

1. Core DSL Syntax: Define Gate and Circuit inductive types, ensure circuits
can be composed from sub-circuits to enable structure replication.
2. Core DSL Semantics: Implement the eval function. Include support for BitVec
to handle multi-bit buses.
3. Proof Engine: Define basic theorems and annotate with @simp.
4. Sequential Integration: Add Register as an additional component in Circuit
that define the step : State → Input → State × Output function.
5. Assertion Framework: Define the Trigger → Check property model and temporal
predicates.
6. Adder Example: Define a golden model adder class which holds assertion
theorems. Implment an N-bit Ripple Carry Adder that extends the class, thus
proving the relevant properties.
7. Counter Example: Repeat the process but now for a counter which utilizes
sequential logic.
8. FSM Example: Define a traffic light Moore-style FSM and relevant assertion
properties which will have more complex triggers.
9. (Extra) Netlist Parser: Implement a parser to import netlist into the DSL.
