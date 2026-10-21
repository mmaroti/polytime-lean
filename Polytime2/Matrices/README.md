# Matrices and row operations

[Project guide](../README.md) · [Arrays](../Arrays/README.md)

Public carriers are ordinary matrices or finite row functions. The codecs reuse
row-major array storage. Start with [Operations.lean](Operations.lean) for
coordinate-pair access, or [EntryOperations.lean](EntryOperations.lean) for
separate row and column arguments.

## Choose an interface

| Need | Source |
| --- | --- |
| Lookup/update by coordinate pair | [Operations.lean][op] |
| Entry access and replacement using separate coordinates | [entry] |
| A specialization-fixed row transformation | [RowsOperations.lean][rows] |
| Scalar field identities used by row algorithms | [FieldRow.lean][field] |
| Mathematical row transformations | [RowsMath.lean](RowsMath.lean) |

[op]: Operations.lean
[entry]: EntryOperations.lean
[rows]: RowsOperations.lean
[field]: FieldRow.lean

Public entry and row operations expose row and column counts as sizes. Their
coordinates express mathematical admissibility; extra counter capacity and
unary headers are prepared internally. Replacement returns a separate matrix.
Row transformations take ordinary scalar functions fixed by specialization.
Read the operation's contract before assuming behavior for coincident rows.

## Composition and examples

Entry access composes the array access rules for rows and entries. Reuse this
route when adding a matrix operation rather than proving another flattened
address machine. [MatrixAccess.lean](../Examples/MatrixAccess.lean) exercises
matrix access; [MatrixRows.lean](../Examples/MatrixRows.lean) and
[MatrixRowField.lean](../Examples/MatrixRowField.lean) show row transformations.

For elimination, continue with the [Gauss–Jordan
guide](../GaussJordan/README.md).
Integer matrices are a [proposed next task](../tasks/smith-normal-form.md), not
an existing specialization of finite-field row operations.

## Foundational work

[AddressContract.lean](AddressContract.lean),
[EntryContract.lean](EntryContract.lean), and
[ReplaceContract.lean](ReplaceContract.lean) certify the lower-level accessors.
[RowsContract.lean](RowsContract.lean) and
[RowsPresentation.lean](RowsPresentation.lean) connect shared row workspaces to
mathematical interfaces. They own address arithmetic, scratch, initialization,
and tape restoration. The generic [bounded traversal][traversal] avoids
repeating counter and guard arguments in each row algorithm.

[traversal]: ../Arithmetic/BoundedTraversal.lean
