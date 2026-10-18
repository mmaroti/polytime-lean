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

import Polytime2.Machine
import Polytime2.Computation
import Polytime2.Computation.Realizable
import Polytime2.Computation.TM0
import Polytime2.Computation.Composition
import Polytime2.Computation.Constant
import Polytime2.Computation.Arguments
import Polytime2.Computation.Branch
import Polytime2.Computation.While
import Polytime2.Examples.Loop
import Polytime2.Computation.Layout
import Polytime2.Computations.Counter
import Polytime2.Computations.Size
import Polytime2.Computations.Constant
import Polytime2.Computations.FiniteTable
import Polytime2.Computations.Arithmetic
import Polytime2.Computations.Array
import Polytime2.Computations.IndexedMap
import Polytime2.Examples.IndexedMaps
import Polytime2.Computations.Matrix
import Polytime2.Computations.MatrixAddress
import Polytime2.Computations.MatrixEntry
import Polytime2.Computations.MatrixRows
import Polytime2.Examples.MatrixAccess
import Polytime2.Computations.Gcd
import Polytime2.Computations.GaussJordan
import Polytime2.Examples.GaussJordan
import Polytime2.Examples.TM0
import Polytime2.Examples.Computation
import Polytime2.EncodedDomain
import Polytime2.PolynomialEvaluator
import Polytime2.Examples.PolynomialEvaluator
import Polytime2.CallingConvention
import Polytime2.CallingConventionSimulation
import Polytime2.CallingConventionOutput
import Polytime2.StandardCopy
import Polytime2.StandardConstant
import Polytime2.StandardTerminatedCopy
import Polytime2.StandardBinaryRipple
import Polytime2.RestoringScan
import Polytime2.ScanReturn
import Polytime2.StandardBinaryScan
import Polytime2.BinaryEncoding
import Polytime2.StandardBinaryArithmetic
import Polytime2.StandardBinaryReduce
import Polytime2.StandardBinaryDivisionStep
import Polytime2.StandardBinaryRemainder
import Polytime2.StandardBinaryGuard
import Polytime2.StandardGcdStep
import Polytime2.StandardTapeCommands
import Polytime2.StandardGcdMachine
import Polytime2.StandardGcd
import Polytime2.StandardBitFold
import Polytime2.StandardBinaryMultiplyStep
import Polytime2.StandardBinaryMultiplication
import Polytime2.StandardBinaryIncrement
import Polytime2.StandardCounterZero
import Polytime2.StandardSizeReadContract
import Polytime2.Examples.SizeRead
import Polytime2.StandardBinaryDecrement
import Polytime2.StandardHead
import Polytime2.ArrayCounter
import Polytime2.ArraySeek
import Polytime2.ArrayBlockCopy
import Polytime2.ArrayUpdate
import Polytime2.FixedArrayBlockCopy
import Polytime2.RuntimeArrayBlockCopy
import Polytime2.FixedArraySeek
import Polytime2.FixedArrayLookup
import Polytime2.EncodedArray
import Polytime2.FixedArrayUpdate
import Polytime2.Examples.Array
import Polytime2.Examples.Multiplication
import Polytime2.Examples.EncodedDomains
import Polytime2.Complexity
import Polytime2.Examples.Context
import Polytime2.Gcd
import Polytime2.Examples.Gcd
import Polytime2.Wiring
import Polytime2.While
import Polytime2.Copy
import Polytime2.UnaryCopy
import Polytime2.UnaryMove
import Polytime2.RuntimeArraySeek
import Polytime2.RuntimeArrayLookup
import Polytime2.RuntimeArrayLookupContract
import Polytime2.RuntimeArrayUpdate
import Polytime2.RuntimeArrayUpdateContract
import Polytime2.Branch
import Polytime2.Storage
import Polytime2.Binary
import Polytime2.BinaryAddition
import Polytime2.BinaryRipple
import Polytime2.BinarySubtraction
import Polytime2.BinaryScan
import Polytime2.MultiplyAdd
import Polytime2.Examples.MultiplyAdd
import Polytime2.StandardMatrixAddressContract
import Polytime2.Examples.MatrixAddress
import Polytime2.StandardMatrixEntryContract
import Polytime2.Examples.MatrixEntry
import Polytime2.StandardMatrixReplaceContract
import Polytime2.Examples.MatrixReplace
import Polytime2.Pipeline
import Polytime2.Initialization
import Polytime2.Examples.Arithmetic
import Polytime2.Examples.FiniteTables
import Polytime2.StandardArrayMapContract
import Polytime2.Examples.ArrayMaps
import Polytime2.StandardRowCombineContract
import Polytime2.Examples.RowCombine
import Polytime2.StandardMatrixRowEntry
import Polytime2.Examples.MatrixRowEntry
import Polytime2.StandardMatrixRowEntryContract
import Polytime2.Examples.MatrixRowController
import Polytime2.StandardMatrixRowStep
import Polytime2.Examples.MatrixRowSteps
import Polytime2.StandardMatrixRowsContract
import Polytime2.Examples.MatrixRows
import Polytime2.StandardMatrixRowsPresentation
import Polytime2.Examples.MatrixRowField
import Polytime2.StandardFinitePredicate
import Polytime2.Examples.FinitePredicate
import Polytime2.StandardPivotSearch
import Polytime2.StandardPivotSearchCalls
import Polytime2.StandardPivotSearchGuard
import Polytime2.StandardPivotSearchAdvance
import Polytime2.StandardPivotSearchLoop
import Polytime2.StandardPivotSearchAlgorithm
import Polytime2.StandardPivotSearchField
import Polytime2.Examples.PivotGuard
import Polytime2.StandardGaussJordanClearTarget
import Polytime2.StandardGaussJordanClearStep
import Polytime2.StandardGaussJordanClearIntervalMath
import Polytime2.StandardGaussJordanClearAlgorithm
import Polytime2.StandardGaussJordanPivotAlgorithm
import Polytime2.StandardGaussJordanColumnInit
import Polytime2.StandardGaussJordanColumnAlgorithm
import Polytime2.StandardGaussJordanEliminationAlgorithm
import Polytime2.StandardGaussJordanEliminationTM0
import Polytime2.Head
import Polytime2.SingleTape
import Polytime2.Sweep
import Polytime2.Tracks
import Polytime2.MoveMarker
import Polytime2.Extend
import Polytime2.MoveHead
import Polytime2.MoveAll
import Polytime2.Act
import Polytime2.Simulation
import Polytime2.Encoding
import Polytime2.TM0Input
import Polytime2.ArrayTM0
import Polytime2.Matrix
import Polytime2.GaussJordan
import Polytime2.TableTraversal
import Polytime2.FieldRow
import Polytime2.MatrixRowField

/-! # Polytime2

Root module for the second implementation alternative.
-/
