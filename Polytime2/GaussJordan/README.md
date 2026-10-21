# Gauss–Jordan elimination

[Project guide](../README.md) · [Matrix operations](../Matrices/README.md)

Start with [Operations.lean](Operations.lean): `gaussJordan` is the public
computation, and `gaussJordan_realizable` certifies it. Specialization fixes a
finite field enumeration. The public sizes are rows and columns; all matrices
of that shape are admissible, including empty rectangular shapes.

## Contract and examples

`gaussJordan_correct` connects the result to reduced row-echelon form and an
invertible row transformation. The result is the reduced matrix; the
mathematical
existence of a transformation is not an additional returned matrix. Read the
exact theorem in [Operations.lean](Operations.lean).

[Examples/GaussJordan.lean](../Examples/GaussJordan.lean) is the application
entry point. [TM0/GaussJordan.lean](../TM0/GaussJordan.lean) provides a
dedicated
backend certificate; the generic export route is explained in the
[TM0 guide](../TM0/README.md). The target mathematical problem and acceptance
requirements are in [EXAMPLES.md][target].

[target]: ../../EXAMPLES.md#gauss-jordan

## Follow the proof layers

1. [Basic.lean](Basic.lean) and [EliminationMath.lean](EliminationMath.lean)
   describe mathematical elimination and its invariants.
2. [PivotSearchAlgorithm.lean](PivotSearchAlgorithm.lean) finds an eligible row.
   Its row-count sentinel is an internal search convention.
3. [PivotAlgorithm.lean](PivotAlgorithm.lean) and
   [ClearAlgorithm.lean](ClearAlgorithm.lean) use the shared matrix row rules.
4. [ColumnAlgorithm.lean](ColumnAlgorithm.lean) and
   [EliminationAlgorithm.lean](EliminationAlgorithm.lean) compose the stages
   and establish the full execution contract.
5. [Operations.lean](Operations.lean) hides counter capacities, prepares their
   unary headers, and exposes only the mathematical matrix computation.

Application changes should start at the public interface or row-operation
rules. For controller changes, inspect the corresponding `Calls`, `Loop`, and
initialization modules. They reuse live-value and bounded-range certificates;
private scratch does not need a mathematical value or clearing on return.
See the [machine convention](../Machine/README.md) before changing that layer.
