/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Machine.Basic
import Polytime2.Computation.Basic
import Polytime2.Computation.Realizable
import Polytime2.TM0.Computation
import Polytime2.Computation.Composition
import Polytime2.Computation.Constant
import Polytime2.Computation.Arguments
import Polytime2.Computation.Branch
import Polytime2.Computation.While
import Polytime2.Examples.Loop
import Polytime2.Computation.Layout
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Primitives.SizeOperations
import Polytime2.Primitives.ConstantOperations
import Polytime2.Primitives.FiniteOperations
import Polytime2.Arithmetic.Operations
import Polytime2.Arrays.Operations
import Polytime2.Arrays.IndexedMap
import Polytime2.Examples.IndexedMaps
import Polytime2.Matrices.Operations
import Polytime2.Matrices.AddressOperations
import Polytime2.Matrices.EntryOperations
import Polytime2.Matrices.RowsOperations
import Polytime2.Examples.MatrixAccess
import Polytime2.Arithmetic.GcdOperations
import Polytime2.GaussJordan.Operations
import Polytime2.Examples.GaussJordan
import Polytime2.Examples.TM0
import Polytime2.Examples.Computation
import Polytime2.Encoding.EncodedDomain
import Polytime2.Encoding.PolynomialEvaluator
import Polytime2.Examples.PolynomialEvaluator
import Polytime2.Machine.CallingConvention
import Polytime2.TM0.CallingConventionSimulation
import Polytime2.TM0.CallingConventionOutput
import Polytime2.Primitives.Copy
import Polytime2.Primitives.Constant
import Polytime2.Primitives.TerminatedCopy
import Polytime2.Arithmetic.BinaryRipple
import Polytime2.Primitives.RestoringScan
import Polytime2.Primitives.ScanReturn
import Polytime2.Arithmetic.BinaryScan
import Polytime2.Encoding.BinaryEncoding
import Polytime2.Arithmetic.BinaryArithmetic
import Polytime2.Arithmetic.BinaryReduce
import Polytime2.Arithmetic.BinaryDivisionStep
import Polytime2.Arithmetic.BinaryRemainder
import Polytime2.Arithmetic.BinaryGuard
import Polytime2.Arithmetic.GcdStep
import Polytime2.Primitives.TapeCommands
import Polytime2.Arithmetic.GcdMachine
import Polytime2.Arithmetic.Gcd
import Polytime2.Arithmetic.BitFold
import Polytime2.Arithmetic.BinaryMultiplyStep
import Polytime2.Arithmetic.BinaryMultiplication
import Polytime2.Arithmetic.BinaryIncrement
import Polytime2.Arithmetic.CounterZero
import Polytime2.Primitives.SizeReadContract
import Polytime2.Examples.SizeRead
import Polytime2.Arithmetic.BinaryDecrement
import Polytime2.Primitives.Head
import Polytime2.Arrays.Counter
import Polytime2.Arrays.Seek
import Polytime2.Arrays.BlockCopy
import Polytime2.Arrays.Update
import Polytime2.Arrays.FixedBlockCopy
import Polytime2.Arrays.RuntimeBlockCopy
import Polytime2.Arrays.FixedSeek
import Polytime2.Arrays.FixedLookup
import Polytime2.Encoding.EncodedArray
import Polytime2.Arrays.FixedUpdate
import Polytime2.Examples.Array
import Polytime2.Examples.Multiplication
import Polytime2.Examples.EncodedDomains
import Polytime2.Machine.Complexity
import Polytime2.Examples.Context
import Polytime2.Arithmetic.GcdMath
import Polytime2.Examples.Gcd
import Polytime2.Machine.Wiring
import Polytime2.Machine.While
import Polytime2.Primitives.FixedCopy
import Polytime2.Primitives.UnaryCopy
import Polytime2.Primitives.UnaryMove
import Polytime2.Arrays.RuntimeSeek
import Polytime2.Arrays.RuntimeLookup
import Polytime2.Arrays.RuntimeLookupContract
import Polytime2.Arrays.RuntimeUpdate
import Polytime2.Arrays.RuntimeUpdateContract
import Polytime2.Machine.Branch
import Polytime2.Machine.Storage
import Polytime2.Encoding.Binary
import Polytime2.Arithmetic.BinaryAddition
import Polytime2.Arithmetic.RippleMath
import Polytime2.Arithmetic.BinarySubtraction
import Polytime2.Arithmetic.ScanMath
import Polytime2.Arithmetic.MultiplyAdd
import Polytime2.Examples.MultiplyAdd
import Polytime2.Matrices.AddressContract
import Polytime2.Examples.MatrixAddress
import Polytime2.Matrices.EntryContract
import Polytime2.Examples.MatrixEntry
import Polytime2.Matrices.ReplaceContract
import Polytime2.Examples.MatrixReplace
import Polytime2.Machine.Pipeline
import Polytime2.Primitives.Initialization
import Polytime2.Examples.Arithmetic
import Polytime2.Examples.FiniteTables
import Polytime2.Arrays.MapContract
import Polytime2.Examples.ArrayMaps
import Polytime2.Matrices.RowCombine
import Polytime2.Examples.RowCombine
import Polytime2.Matrices.RowEntry
import Polytime2.Examples.MatrixRowEntry
import Polytime2.Matrices.RowEntryContract
import Polytime2.Examples.MatrixRowController
import Polytime2.Matrices.RowStep
import Polytime2.Examples.MatrixRowSteps
import Polytime2.Matrices.RowsContract
import Polytime2.Examples.MatrixRows
import Polytime2.Matrices.RowsPresentation
import Polytime2.Examples.MatrixRowField
import Polytime2.Primitives.FinitePredicate
import Polytime2.Examples.FinitePredicate
import Polytime2.GaussJordan.PivotSearch
import Polytime2.GaussJordan.PivotSearchCalls
import Polytime2.GaussJordan.PivotSearchGuard
import Polytime2.GaussJordan.PivotSearchAdvance
import Polytime2.GaussJordan.PivotSearchLoop
import Polytime2.GaussJordan.PivotSearchAlgorithm
import Polytime2.GaussJordan.PivotSearchField
import Polytime2.Examples.PivotGuard
import Polytime2.GaussJordan.ClearTarget
import Polytime2.GaussJordan.ClearStep
import Polytime2.GaussJordan.ClearIntervalMath
import Polytime2.GaussJordan.ClearAlgorithm
import Polytime2.GaussJordan.PivotAlgorithm
import Polytime2.GaussJordan.ColumnInit
import Polytime2.GaussJordan.ColumnAlgorithm
import Polytime2.GaussJordan.EliminationAlgorithm
import Polytime2.TM0.GaussJordan
import Polytime2.Primitives.FixedHead
import Polytime2.TM0.SingleTape
import Polytime2.TM0.Sweep
import Polytime2.TM0.Tracks
import Polytime2.TM0.MoveMarker
import Polytime2.TM0.Extend
import Polytime2.TM0.MoveHead
import Polytime2.TM0.MoveAll
import Polytime2.TM0.Act
import Polytime2.TM0.Simulation
import Polytime2.TM0.Encoding
import Polytime2.TM0.TM0Input
import Polytime2.TM0.Array
import Polytime2.Matrices.Basic
import Polytime2.GaussJordan.Basic
import Polytime2.Arrays.TableTraversal
import Polytime2.Matrices.FieldRow
import Polytime2.Matrices.RowField

/-! # Polytime2

Root module for the second implementation alternative.
-/
