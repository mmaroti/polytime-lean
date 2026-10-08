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

import Polytime.Domain

namespace Polytime

-- u: mathematical domain carriers; v: representation carriers.
universe u v

/-- Mathematical objects with a unique valid representation at each size assignment. -/
structure EncodedDomain (ctx : SizeContext) where
  Carrier : SizeAssignment ctx → Type u
  expression : DomainExpression.{v} ctx
  represent : (a : SizeAssignment ctx) → Carrier a → expression.Value a
  interpret : (a : SizeAssignment ctx) → expression.Value a → Option (Carrier a)
  interpret_represent : ∀ a x, interpret a (represent a x) = some x
  represent_interpret : ∀ a r x, interpret a r = some x → represent a x = r

namespace EncodedDomain

/-- A total mathematical presentation uses the existing equivalence structure. -/
def ofEquiv {ctx : SizeContext} (expression : DomainExpression.{v} ctx)
    (Carrier : SizeAssignment ctx → Type u)
    (presentation : ∀ assignment, Carrier assignment ≃ expression.Value assignment) : EncodedDomain ctx where
  Carrier := Carrier
  expression := expression
  represent := fun assignment => presentation assignment
  interpret := fun assignment value => some ((presentation assignment).symm value)
  interpret_represent := fun assignment value => by simp
  represent_interpret := fun assignment representation value hypothesis => by
    have equality := Option.some.inj hypothesis
    subst value
    simp

/-- Compose the mathematical presentation with the expression's canonical bit codec. -/
def codec (d : EncodedDomain ctx) (a : SizeAssignment ctx) :
    BitCodec (d.Carrier a) (d.expression.bitWidth a) where
  encode x := d.expression.encode a (d.represent a x)
  decode bits := (d.expression.decode a bits).bind (d.interpret a)
  decode_encode x := by
    rw [d.expression.decode_encode, Option.bind_some, d.interpret_represent]
  encode_decode bits x h := by
    cases hr : d.expression.decode a bits with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.bind_some] at h
      rw [d.represent_interpret a r x h]
      exact d.expression.encode_decode a bits r hr

end EncodedDomain

end Polytime
