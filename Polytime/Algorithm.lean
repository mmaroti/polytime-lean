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

import Polytime.EncodedDomain

namespace Polytime

-- u: specialization objects; v: mathematical domain carriers; w: representation carriers.
universe u v w

/-- Specialization requirements and domains; execution is not yet specified. -/
structure Algorithm where
  Specialization : Type u
  acceptable : Specialization → Prop
  sizeContext : (S : Specialization) → acceptable S → SizeContext
  inputDomain : (S : Specialization) → (h : acceptable S) →
    EncodedDomain.{v, w} (sizeContext S h)
  outputDomain : (S : Specialization) → (h : acceptable S) →
    EncodedDomain.{v, w} (sizeContext S h)

end Polytime
