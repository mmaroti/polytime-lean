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

import Polytime1.Size
import Polytime1.Realization
import Polytime1.SizeFrame
import Polytime1.NamedHeader
import Polytime1.RealizationLoop
import Polytime1.MatrixStorage
import Polytime1.BinaryAddition
import Polytime1.Encoding
import Polytime1.Domain
import Polytime1.EncodedDomain
import Polytime1.Algorithm
import Polytime1.Examples.Matrices
import Polytime1.Examples.MatrixAccess
import Polytime1.Examples.MatrixAddress
import Polytime1.Examples.MatrixWrite
import Polytime1.Examples.MatrixRowMap
import Polytime1.Examples.MatrixRowScale
import Polytime1.Examples.MatrixNormalizeRow
import Polytime1.Examples.MatrixNormalizeRowSaved
import Polytime1.Examples.MatrixEntryCombine
import Polytime1.Examples.MatrixRowCombine
import Polytime1.Examples.MatrixRowAdd
import Polytime1.Examples.MatrixRowSwap
import Polytime1.Examples.MatrixClearRow
import Polytime1.Examples.MatrixClearRowSaved
import Polytime1.Examples.MatrixClearTargetStep
import Polytime1.Examples.MatrixClearRange
import Polytime1.Examples.MatrixClearColumn
import Polytime1.Examples.MatrixPivotStep
import Polytime1.Examples.MatrixPivotDispatch
import Polytime1.Examples.MatrixColumnStep
import Polytime1.Examples.MatrixEliminate
import Polytime1.Examples.MatrixEntryTest
import Polytime1.Examples.MatrixPivotGuard
import Polytime1.Examples.MatrixPivotSearch
import Polytime1.Examples.AddressPreparation
import Polytime1.Examples.Domains
import Polytime1.Examples.TupleLookup
import Polytime1.Examples.TupleComposition
import Polytime1.Examples.FramePreparation
import Polytime1.Examples.SizeEvaluation
import Polytime1.Examples.GaussJordan
import Polytime1.Examples.FiniteTables
import Polytime1.Examples.CatalogueMap
import Polytime1.Examples.While
