/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Finite morphisms from proper quasi-affine sources

Adapted from the same-named original module below `Motivic/Aglib`, blob
`2ea7e5da02b9061fcdf3e85697a8ea53a27f6fa9`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A proper quasi-affine scheme over an affine scheme is finite over it. -/
theorem isFinite_of_isProper_of_isQuasiAffine {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [X.IsQuasiAffine] [IsAffine Y] : IsFinite f := by
  have : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  have : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map f.appTop)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  have : IsAffine X := isAffine_of_isAffineHom X.toSpecΓ
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
