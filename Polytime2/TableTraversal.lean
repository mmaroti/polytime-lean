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

import Polytime2.StandardArrayMapContract

/-! # Finite-table traversal on binary arrays

The traversal uses encoded scalar domains, separate immutable arguments, and
an arbitrary initial output region. Runtime lengths do not enlarge its finite
controller.
-/

namespace Polytime2.TableTraversal

export StandardArrayMap (algorithm contract)

end Polytime2.TableTraversal
