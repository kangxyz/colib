/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionPrespectrum
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed

/-! # The original fine ambient coefficient seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- The actual ambient native coefficient prespectrum row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:151"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientPrespectrumFunctor (Q : Over (Spec R)) :
    Under R ⥤ LoopPrespectrum.{u + 1} :=
  boundedAboveFlatCoefficientSectionModelRow Q ⋙ prespectrumFunctor

/-- The unchanged ambient forward Laurent action on the native fine coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassSeed.lean:50"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientLaurentAction (Q : Over (Spec R)) :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSectionModelRow Q) where
  unit := boundedAboveFlatCoefficientSectionLaurentUnitIso Q
  naturality := boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient Q

/-- Construct the native fine ambient seed using that same prescribed Bass construction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassSeed.lean:63"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientBassSeed (Q : Over (Spec R)) :
    boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q) :=
  (boundedAboveFlatCoefficientAmbientLaurentAction Q).track.seed

end AlgebraicGeometry.Scheme.Modules
