/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Sheafified

/-!
# Suslin cancellation on effective-motive representatives

The actual Nisnevich singular comparison gives an isomorphism of the
effective representatives of the two original transfer presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The effective motive of a smooth scheme is identified with the
singular representative of the reduced torus contraction. -/
def effectiveMotiveTorusCancellationIso (Y : Cor k) :
    (effectiveMotive k).obj Y ≅
      (singularEffectiveMotiveFunctor k).obj (torusCancellationTarget k Y) := by
  let f := torusCancellationSheafCochainMap k Y
  let : QuasiIso f := torusCancellationSheafCochainMap_quasiIso k Y
  let e := asIso (DerivedCategory.Q.map f)
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)

end AlgebraicGeometry.MotivicHomotopy
