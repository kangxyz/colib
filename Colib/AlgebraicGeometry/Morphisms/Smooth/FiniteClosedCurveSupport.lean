/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.CodimensionOneDominance

public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import Colib.AlgebraicGeometry.Morphisms.Finite.ProperQuasiAffine

/-! # Finite closed supports in smooth relative curves

The generic point of a codimension-one closed support finite over the base
lies over an actual component generic point of the base.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/Divisors/CodimensionOneDominance.lean`
and `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Boundary/NeighborhoodComplement.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] specializationOrder

/- The finite-support dominance theorem and its closed-fibre ingredient are
re-exported from `CodimensionOneDominance`. Both use the same full finite
closed support, with no flatness assumption on that support. -/

end AlgebraicGeometry.Scheme
