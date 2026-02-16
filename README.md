# Formal Hardware Description Language (HDL)

This project implements an emedded domain specific language (DSL) with [Lean4](https://lean-lang.org) for
interactive formal verification of digital systems. The DSL provides representation
of combinational and sequential (state-based) logic and enables functional equivalence
checking between gate-level implementations and high-level specification. Verification
of system properties, such as overflow or state reachability, is also supported. A
gallery of examples including verification of an adder and counter is included to
showcase the DSL's functionality. A stretch goal of the project is the development
of a parser to enable direct import of post-synthesis netlists for automated verification.
