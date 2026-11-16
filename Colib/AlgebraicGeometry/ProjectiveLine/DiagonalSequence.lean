/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-! # The ideal sequence of the relative projective-line diagonal

The sequence is built from the actual closed diagonal and its structure-sheaf
comorphism. It will be used with the two flat projections to compute the
projective bundle map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)

/-- The comorphism of the actual relative diagonal. -/
abbrev projectiveLineDiagonalComorphism :=
  _root_.SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom (pullback.diagonal π).toLRSHom.toShHom)

/-- The ideal, structure sheaf and closed direct image of the diagonal. -/
def projectiveLineDiagonalSequence :=
  ShortComplex.mk (kernel.ι (projectiveLineDiagonalComorphism X))
    (projectiveLineDiagonalComorphism X) (kernel.condition _)

/-- The relative diagonal has its actual short exact ideal sequence. -/
theorem projectiveLineDiagonalSequence_shortExact :
    (projectiveLineDiagonalSequence X).ShortExact := by
  let := isProper_projectiveSpaceOver 1 X
  exact Stacks.Cohomology.AmpleH1.shortExact_idealSheaf (pullback.diagonal π)

end AlgebraicGeometry.Scheme
