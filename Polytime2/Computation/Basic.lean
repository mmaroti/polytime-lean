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

import Polytime2.Encoding.EncodedDomain

/-! # Mathematical computations on admissible encoded arguments -/

namespace Polytime2

-- carrierLevel: mathematical values; finite parameter and argument names use Type.
universe carrierLevel

/-- A specification contains no machine, scratch layout, or running-time witness. -/
structure Computation (Parameter InputName : Type) [Fintype Parameter] [Fintype InputName] where
  inputDomains : InputName → EncodedDomain.{0, carrierLevel} Parameter
  outputDomain : EncodedDomain.{0, carrierLevel} Parameter
  precondition : ∀ sizes : Parameter → ℕ,
    ((name : InputName) → (inputDomains name).Carrier sizes) → Prop
  compute : ∀ sizes : Parameter → ℕ,
    {arguments : (name : InputName) → (inputDomains name).Carrier sizes //
      precondition sizes arguments} → outputDomain.Carrier sizes

namespace Computation

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

abbrev Arguments (computation : Computation.{carrierLevel} Parameter InputName)
    (sizes : Parameter → ℕ) :=
  (name : InputName) → (computation.inputDomains name).Carrier sizes

/-- A unary mathematical map, total on its admissible inputs. -/
def unaryMap (inputDomain outputDomain : EncodedDomain.{0, carrierLevel} Parameter)
    (precondition : ∀ sizes, inputDomain.Carrier sizes → Prop)
    (compute : ∀ sizes, {value : inputDomain.Carrier sizes // precondition sizes value} →
      outputDomain.Carrier sizes) : Computation Parameter Unit where
  inputDomains _ := inputDomain
  outputDomain := outputDomain
  precondition sizes arguments := precondition sizes (arguments ())
  compute sizes arguments := compute sizes ⟨arguments.val (), arguments.property⟩

/-- A mathematical caller may restrict the admissible inputs without changing
the computation on those inputs. -/
def withPrecondition (computation : Computation.{carrierLevel} Parameter InputName)
    (precondition : ∀ sizes, computation.Arguments sizes → Prop)
    (implies : ∀ sizes arguments, precondition sizes arguments →
      computation.precondition sizes arguments) : Computation Parameter InputName where
  inputDomains := computation.inputDomains
  outputDomain := computation.outputDomain
  precondition := precondition
  compute sizes arguments := computation.compute sizes
    ⟨arguments.val, implies sizes arguments.val arguments.property⟩

/-- Use selected arguments from a larger context, leaving the others unused. -/
def withArguments {ContextName : Type} [Fintype ContextName]
    (computation : Computation.{carrierLevel} Parameter InputName)
    (contextDomains : ContextName → EncodedDomain.{0, carrierLevel} Parameter)
    (selection : InputName ↪ ContextName)
    (domainEqual : ∀ name, contextDomains (selection name) = computation.inputDomains name) :
    Computation Parameter ContextName where
  inputDomains := contextDomains
  outputDomain := computation.outputDomain
  precondition sizes arguments := computation.precondition sizes
    (fun name => domainEqual name ▸ arguments (selection name))
  compute sizes arguments := computation.compute sizes
    ⟨(fun name => domainEqual name ▸ arguments.val (selection name)), arguments.property⟩

/-- Bind a result while retaining all original arguments for the continuation.
Nested bindings describe a DAG of mathematical computations. -/
def letThen (first : Computation.{carrierLevel} Parameter InputName)
    (continuation : Computation.{carrierLevel} Parameter (InputName ⊕ Unit))
    (inputEqual : ∀ name, continuation.inputDomains (.inl name) = first.inputDomains name)
    (resultEqual : continuation.inputDomains (.inr ()) = first.outputDomain)
    (compatible : ∀ sizes (arguments : first.Arguments sizes)
      (valid : first.precondition sizes arguments),
      continuation.precondition sizes (fun name => match name with
        | .inl original => (inputEqual original).symm ▸ arguments original
        | .inr _ => resultEqual.symm ▸ first.compute sizes ⟨arguments, valid⟩)) :
    Computation Parameter InputName where
  inputDomains := first.inputDomains
  outputDomain := continuation.outputDomain
  precondition := first.precondition
  compute sizes arguments := continuation.compute sizes
    ⟨(fun name => match name with
      | .inl original => (inputEqual original).symm ▸ arguments.val original
      | .inr _ => resultEqual.symm ▸ first.compute sizes arguments),
      compatible sizes arguments.val arguments.property⟩

/-- Feed one computation's result to a single-argument computation. The
compatibility proof is mathematical and does not refer to either machine. -/
def followedBy (first : Computation.{carrierLevel} Parameter InputName)
    (second : Computation.{carrierLevel} Parameter Unit)
    (domainEqual : second.inputDomains () = first.outputDomain)
    (compatible : ∀ sizes (arguments : first.Arguments sizes)
      (valid : first.precondition sizes arguments),
      second.precondition sizes (fun _ =>
        domainEqual.symm ▸ first.compute sizes ⟨arguments, valid⟩)) :
    Computation Parameter InputName where
  inputDomains := first.inputDomains
  outputDomain := second.outputDomain
  precondition := first.precondition
  compute sizes arguments := second.compute sizes
    ⟨(fun _ => domainEqual.symm ▸ first.compute sizes arguments),
      compatible sizes arguments.val arguments.property⟩

end Computation
end Polytime2
