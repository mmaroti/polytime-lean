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
import Polytime2.Complexity
import Polytime2.Contracts
import Polytime2.Context
import Polytime2.Examples.Context
import Polytime2.Search
import Polytime2.Gcd
import Polytime2.GcdMachine
import Polytime2.GcdInput
import Polytime2.GcdExternal
import Polytime2.Examples.Gcd
import Polytime2.Fold
import Polytime2.Wiring
import Polytime2.While
import Polytime2.Copy
import Polytime2.Branch
import Polytime2.Storage
import Polytime2.Binary
import Polytime2.BinaryAddition
import Polytime2.BinaryRipple
import Polytime2.BinarySubtraction
import Polytime2.BinaryScan
import Polytime2.BinaryInPlace
import Polytime2.BinaryReduce
import Polytime2.BinaryRemainder
import Polytime2.BinaryMultiplication
import Polytime2.AddMultiply
import Polytime2.ReadBlock
import Polytime2.Pipeline
import Polytime2.BinaryOutput
import Polytime2.AddMultiplyInput
import Polytime2.AddMultiplyExternal
import Polytime2.Examples.Arithmetic
import Polytime2.CatalogueMap
import Polytime2.TerminatedCopy
import Polytime2.BinaryGuard
import Polytime2.Head
import Polytime2.Array
import Polytime2.IndexedCopy
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
import Polytime2.ScalarAccess
import Polytime2.MatrixAccess
import Polytime2.HeadTable
import Polytime2.Unary
import Polytime2.UnaryAppend
import Polytime2.MatrixAddress
import Polytime2.Alphabet
import Polytime2.MatrixEntry
import Polytime2.MatrixEntryTM0
import Polytime2.UnaryCompare
import Polytime2.PivotSearch
import Polytime2.MatrixRows
import Polytime2.MatrixRowField
import Polytime2.MatrixRowsTM0
import Polytime2.UnaryCopy
import Polytime2.UnaryRead
import Polytime2.ReturnToMarker
import Polytime2.ScalarCodec
import Polytime2.ScalarStreams
import Polytime2.GaussJordanWorkspace
import Polytime2.GaussJordanClear
import Polytime2.GaussJordanPivot
import Polytime2.GaussJordanColumn
import Polytime2.GaussJordanMachine
import Polytime2.GaussJordanTM0
import Polytime2.SparseInput
import Polytime2.GaussJordanInput
import Polytime2.GaussJordanExternal
import Polytime2.GaussJordanExternalTM0
import Polytime2.GaussJordanOutput

/-! # Polytime2

Root module for the second implementation alternative.
-/
