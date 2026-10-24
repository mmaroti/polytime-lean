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

import Polytime2.Matrices.IntegerCyclicMembership
import Polytime2.TM0.Computation

/-! # Certified cyclic membership and full augmentation

The complete augmented matrix and cyclic decision procedure have standalone
machine certificates. Tests retain a generator column beside the modulus
block, reject a target with no generators, and accept empty coordinate sets.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.CyclicMembership

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter]
    (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ) :
    (integerMatrixAppendColumns rows firstColumns secondColumns width).TM0Realizable :=
  (integerMatrixAppendColumns_realizable rows firstColumns secondColumns width).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    (integerAugmentedMatrix rows generators generatorWidth modulusWidth).TM0Realizable :=
  (integerAugmentedMatrix_realizable rows generators generatorWidth modulusWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicMembership rows generators generatorWidth modulusWidth targetWidth).TM0Realizable :=
  (integerCyclicMembership_realizable rows generators generatorWidth modulusWidth targetWidth).tm0

private noncomputable def generatorOne :
    (integerCyclicMembership (Parameter := Empty) 1 1 2 2 2).Arguments Empty.elim
  | 0 => ⟨fun _ _ => 1, by intros; norm_num⟩
  | 1 => fun _ => ⟨2, by norm_num⟩
  | 2 => fun _ => ⟨1, by norm_num⟩

example : (integerCyclicMembership (Parameter := Empty) 1 1 2 2 2).compute Empty.elim
    ⟨generatorOne, trivial⟩ = true := by
  apply (integerCyclicMembership_correct 1 1 2 2 2 Empty.elim generatorOne).mpr
  refine ⟨fun _ => 1, ?_⟩
  intro row
  norm_num [generatorOne]

private noncomputable def noGenerators :
    (integerCyclicMembership (Parameter := Empty) 1 0 2 2 2).Arguments Empty.elim
  | 0 => ⟨fun _ _ => 0, by intros; norm_num⟩
  | 1 => fun _ => ⟨2, by norm_num⟩
  | 2 => fun _ => ⟨1, by norm_num⟩

example : (integerCyclicMembership (Parameter := Empty) 1 0 2 2 2).compute Empty.elim
    ⟨noGenerators, trivial⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨coefficients, equal⟩ := (integerCyclicMembership_correct 1 0 2 2 2 Empty.elim noGenerators).mp accepted
  have impossible := equal ⟨0, by norm_num⟩
  change (∑ generator, (coefficients generator : ZMod 2) * 0) = 1 at impossible
  simp at impossible

example {Parameter : Type} [Fintype Parameter]
    (generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicMembership 0 generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    (integerCyclicMembership 0 generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true := by
  apply (integerCyclicMembership_correct 0 generators generatorWidth modulusWidth targetWidth sizes arguments).mpr
  refine ⟨fun _ => 0, ?_⟩
  intro row
  have impossible := row.isLt
  simp at impossible

example {Parameter : Type} [Fintype Parameter]
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).TM0Realizable :=
  (integerCyclicSolve_realizable rows generators generatorWidth modulusWidth targetWidth).tm0

example : ∃ values, (integerCyclicSolve (Parameter := Empty) 1 1 2 2 2).compute Empty.elim
    ⟨generatorOne, trivial⟩ = some values := by
  apply Option.ne_none_iff_exists'.mp
  intro absent
  have impossible := (integerCyclicSolve_none_iff 1 1 2 2 2 Empty.elim generatorOne).mp absent
  apply impossible
  refine ⟨fun _ => 1, ?_⟩
  intro row
  norm_num [generatorOne]

example : (integerCyclicSolve (Parameter := Empty) 1 0 2 2 2).compute Empty.elim
    ⟨noGenerators, trivial⟩ = none := by
  apply (integerCyclicSolve_none_iff 1 0 2 2 2 Empty.elim noGenerators).mpr
  rintro ⟨coefficients, equal⟩
  have impossible := equal ⟨0, by norm_num⟩
  change (∑ generator, (coefficients generator : ZMod 2) * 0) = 1 at impossible
  simp at impossible

example {Parameter : Type} [Fintype Parameter]
    (generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicSolve 0 generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    ∃ values, (integerCyclicSolve 0 generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values := by
  apply Option.ne_none_iff_exists'.mp
  intro absent
  have impossible := (integerCyclicSolve_none_iff 0 generators generatorWidth modulusWidth targetWidth sizes arguments).mp absent
  apply impossible
  refine ⟨fun _ => 0, ?_⟩
  intro row
  have empty := row.isLt
  simp at empty

end Polytime2.Examples.CyclicMembership
