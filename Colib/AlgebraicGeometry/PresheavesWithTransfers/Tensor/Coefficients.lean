/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic

/-! # Coefficient universe for transfer convolution -/

@[expose] public section

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- Transfer coefficients in the universe of the native representables. -/
abbrev TransferCoefficients (k : Type u) [Field k] := PresheafWithTransfers.{u + 1} k

end AlgebraicGeometry.PresheafWithTransfers
