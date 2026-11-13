/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeForgetComparison

/-! Original supported finite negative comparison, Laurent representatives and forget square.
No positive stabilization or telescope comparison is assumed.
-/
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

example (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙
        AlgebraicGeometry.Scheme.Bass.supportedNegativeKFunctor i ≅
      boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  boundedAboveFlatCoefficientSupportedNegativeKComparison f i

#check boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone
#check boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app
#check boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone_forget
