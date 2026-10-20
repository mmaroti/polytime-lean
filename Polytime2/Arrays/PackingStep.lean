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

import Polytime2.Arrays.Packing
import Polytime2.Arrays.Operations
import Polytime2.Arrays.Fold
import Polytime2.Computation.Conditional
import Polytime2.Primitives.BitOperations

/-! # A certified stable-packing update

The accumulator stores the source cursor, the dense output cursor, and raw
output blocks. Selected elements are encoded only when copied; unused blocks
need no mathematical default value.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def packingState (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (EncodedDomain.binaryNaturals capacity).prod ((EncodedDomain.binaryNaturals capacity).prod
    ((EncodedDomain.bitVectors element.widthPolynomial).arrayOfLength length))

/-- The mathematical update is permitted while the source cursor is in range
and the output cursor has not overtaken it. -/
noncomputable def packingStep (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Unit ⊕ Bool) where
  inputDomains := Sum.elim (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    (fun choice => if choice then element else packingState element capacity length)
  outputDomain := packingState element capacity length
  precondition sizes arguments :=
    (arguments (.inr false)).1.val < MvPolynomial.eval sizes length ∧
    (arguments (.inr false)).2.1.val ≤ (arguments (.inr false)).1.val
  compute sizes arguments :=
    let current := arguments.val (.inr false)
    let selected : Bool := arguments.val (.inl ()) ⟨current.1.val, arguments.property.1⟩
    (StandardBinaryIncrement.next capacity sizes current.1,
      (if selected then StandardBinaryIncrement.next capacity sizes current.2.1 else current.2.1,
        if selected then Function.update current.2.2
          ⟨current.2.1.val, lt_of_le_of_lt arguments.property.2 arguments.property.1⟩
          (element.encode sizes (arguments.val (.inr true))) else current.2.2))

/-- One packing step uses only certified projections, array operations,
encoding, increment, conditionals, and tuple construction. -/
theorem packingStep_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (packingStep element capacity length).Realizable := by
  let computation := packingStep element capacity length
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  let counter := EncodedDomain.binaryNaturals capacity
  let raw := EncodedDomain.bitVectors element.widthPolynomial
  let array := raw.arrayOfLength length
  let state := packingState element capacity length
  let Arguments sizes := {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments}
  let source sizes (arguments : Arguments sizes) := (arguments.val (.inr false)).1
  let destination sizes (arguments : Arguments sizes) := (arguments.val (.inr false)).2.1
  let storage sizes (arguments : Arguments sizes) := (arguments.val (.inr false)).2.2
  let replacement sizes (arguments : Arguments sizes) := element.encode sizes (arguments.val (.inr true))
  let flag sizes (arguments : Arguments sizes) : Bool :=
    arguments.val (.inl ()) ⟨(source sizes arguments).val, arguments.property.1⟩
  have stateReady := Realizable.argument inputs (.inr false) allowed
  have sourceReady : (Computation.mk inputs counter allowed source).Realizable :=
    stateReady.followedBy (pairProjection_realizable counter (counter.prod array) false) rfl (by intros; trivial)
  have tailReady := stateReady.followedBy
    (pairProjection_realizable counter (counter.prod array) true) rfl (by intros; trivial)
  have destinationReady : (Computation.mk inputs counter allowed destination).Realizable :=
    tailReady.followedBy (pairProjection_realizable counter array false) rfl (by intros; trivial)
  have storageReady : (Computation.mk inputs array allowed storage).Realizable :=
    tailReady.followedBy (pairProjection_realizable counter array true) rfl (by intros; trivial)
  have replacementReady : (Computation.mk inputs raw allowed replacement).Realizable :=
    (Realizable.argument inputs (.inr true) allowed).followedBy
      (encode_realizable element) rfl (by intros; trivial)
  let lookupValues (choice : Bool) sizes (arguments : Arguments sizes) :
      ((Realizable.Internal.arrayLookupWithCapacity EncodedDomain.booleans capacity length).inputDomains choice).Carrier sizes :=
    match choice with
    | false => source sizes arguments
    | true => arguments.val (.inl ())
  have lookupValid sizes (arguments : Arguments sizes) :
      (Realizable.Internal.arrayLookupWithCapacity EncodedDomain.booleans capacity length).precondition sizes
        (fun choice => lookupValues choice sizes arguments) := arguments.property.1
  have lookupProducers choice :
      (Computation.mk inputs ((Realizable.Internal.arrayLookupWithCapacity EncodedDomain.booleans capacity length).inputDomains choice)
        allowed (lookupValues choice)).Realizable := by
    cases choice
    · exact sourceReady
    · exact Realizable.argument inputs (.inl ()) allowed
  have flagReady : (Computation.mk inputs EncodedDomain.booleans allowed flag).Realizable :=
    (Realizable.Internal.arrayLookupWithCapacity_realizable EncodedDomain.booleans capacity length).onResults inputs allowed
      lookupValues lookupValid lookupProducers
  let updateValues (name : Fin 3) sizes (arguments : Arguments sizes) :
      ((Realizable.Internal.arrayUpdateWithCapacity raw capacity length).inputDomains name).Carrier sizes :=
    match name with
    | 0 => destination sizes arguments
    | 1 => storage sizes arguments
    | 2 => replacement sizes arguments
  have updateValid sizes (arguments : Arguments sizes) :
      (Realizable.Internal.arrayUpdateWithCapacity raw capacity length).precondition sizes
        (fun name => updateValues name sizes arguments) :=
    lt_of_le_of_lt arguments.property.2 arguments.property.1
  have updateProducers name :
      (Computation.mk inputs ((Realizable.Internal.arrayUpdateWithCapacity raw capacity length).inputDomains name)
        allowed (updateValues name)).Realizable := by
    fin_cases name
    · exact destinationReady
    · exact storageReady
    · exact replacementReady
  let updated sizes (arguments : Arguments sizes) :=
    Function.update (storage sizes arguments)
      ⟨(destination sizes arguments).val, updateValid sizes arguments⟩ (replacement sizes arguments)
  have updateReady : (Computation.mk inputs array allowed updated).Realizable :=
    (Realizable.Internal.arrayUpdateWithCapacity_realizable raw capacity length).onResults inputs allowed
      updateValues updateValid updateProducers
  let sourceNext sizes (arguments : Arguments sizes) :=
    StandardBinaryIncrement.next capacity sizes (source sizes arguments)
  let destinationNext sizes (arguments : Arguments sizes) :=
    StandardBinaryIncrement.next capacity sizes (destination sizes arguments)
  have sourceNextReady : (Computation.mk inputs counter allowed sourceNext).Realizable :=
    (counterIncrement_realizable capacity).onResults inputs allowed (fun _ => source)
      (by intros; trivial) (fun _ => sourceReady)
  have destinationNextReady : (Computation.mk inputs counter allowed destinationNext).Realizable :=
    (counterIncrement_realizable capacity).onResults inputs allowed (fun _ => destination)
      (by intros; trivial) (fun _ => destinationReady)
  let finalDestination sizes (arguments : Arguments sizes) :=
    if flag sizes arguments then destinationNext sizes arguments else destination sizes arguments
  let finalStorage sizes (arguments : Arguments sizes) :=
    if flag sizes arguments then updated sizes arguments else storage sizes arguments
  have finalDestinationReady : (Computation.mk inputs counter allowed finalDestination).Realizable :=
    Realizable.conditional inputs counter allowed flag destinationNext destination
      flagReady destinationNextReady destinationReady
  have finalStorageReady : (Computation.mk inputs array allowed finalStorage).Realizable :=
    Realizable.conditional inputs array allowed flag updated storage flagReady updateReady storageReady
  have tailResult := Realizable.pairOutputs inputs counter array allowed
    finalDestination finalStorage finalDestinationReady finalStorageReady
  exact Realizable.pairOutputs inputs counter (counter.prod array) allowed sourceNext
    (fun sizes arguments => (finalDestination sizes arguments, finalStorage sizes arguments))
    sourceNextReady tailResult

/-- Total update for the fold compiler. The invariant ensures the guarded
branch is taken at each actual source position. -/
noncomputable def packingAdvance (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (current : (packingState element capacity length).Carrier sizes)
    (value : element.Carrier sizes) : (packingState element capacity length).Carrier sizes :=
  if valid : current.1.val < MvPolynomial.eval sizes length ∧ current.2.1.val ≤ current.1.val then
    (packingStep element capacity length).compute sizes
      ⟨(fun | .inl _ => flags | .inr false => current | .inr true => value), valid⟩
  else current

/-- The certified update is directly usable by the public array-fold rule. -/
theorem packingAdvance_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
      element (packingState element capacity length)
      (fun sizes _ current _ => current.1.val < MvPolynomial.eval sizes length ∧ current.2.1.val ≤ current.1.val)
      (fun sizes flags current value => packingAdvance element capacity length sizes (flags ()) current value)).Realizable := by
  apply (packingStep_realizable element capacity length).withSpecification
    (packingStep element capacity length).precondition _ (by intros; assumption)
  intro sizes arguments valid
  change (packingStep element capacity length).compute sizes ⟨arguments, valid⟩ =
    packingAdvance element capacity length sizes (arguments (.inl ())) (arguments (.inr false)) (arguments (.inr true))
  have permitted : (arguments (.inr false)).1.val < MvPolynomial.eval sizes length ∧
      (arguments (.inr false)).2.1.val ≤ (arguments (.inr false)).1.val := valid
  rw [packingAdvance, dite_eq_left permitted]
  congr 1
  apply Subtype.ext
  funext name
  rcases name with singleton | choice
  · cases singleton; rfl
  · cases choice <;> rfl

/-- Each permitted update advances the source once and the output at most once.
The source capacity is large enough to represent the final cursor as well. -/
theorem packingAdvance_cursors (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (current : (packingState element capacity length).Carrier sizes) (value : element.Carrier sizes)
    (processed : ℕ) (source : current.1.val = processed) (destination : current.2.1.val ≤ processed)
    (within : processed < MvPolynomial.eval sizes length)
    (fits : MvPolynomial.eval sizes length < 2 ^ sizes capacity) :
    (packingAdvance element capacity length sizes flags current value).1.val = processed + 1 ∧
    (packingAdvance element capacity length sizes flags current value).2.1.val ≤ processed + 1 := by
  have permitted : current.1.val < MvPolynomial.eval sizes length ∧ current.2.1.val ≤ current.1.val := by
    constructor <;> omega
  rw [packingAdvance, dite_eq_left permitted]
  dsimp only [packingStep]
  constructor
  · change (current.1.val + 1) % 2 ^ sizes capacity = processed + 1
    rw [source, Nat.mod_eq_of_lt (by omega)]
  · split
    · change (current.2.1.val + 1) % 2 ^ sizes capacity ≤ processed + 1
      exact (Nat.mod_le _ _).trans (by omega)
    · exact destination.trans (Nat.le_succ processed)

end Polytime2.Computation
