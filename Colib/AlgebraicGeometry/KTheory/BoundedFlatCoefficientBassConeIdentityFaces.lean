/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassConeStep
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentUnitSquares
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# The original Laurent inclusion faces of the coefficient Bass unit

The actual cone map restricts to the original Laurent coefficient map. The geometric
Laurent unit track gives a homotopy on this inclusion, also after parameter looping.
These are identities on the inclusion face only, not identities of the whole cone or step.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:429-435` and
`BoundedFlat/CoefficientBassConeFaces.lean:42-50,82-90` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

/-- The literal Laurent inclusion commutes with the actual coefficient cone map. -/
lemma boundedAboveFlatCoefficientBassConeMap_inclusion :
    mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a) ≫
      boundedAboveFlatCoefficientBassConeMap P g =
      boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map g)) ≫
        mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P b) :=
  mappingConeSquareMap_inclusion (boundedAboveFlatCoefficientBassSquareComparison P a)
    (boundedAboveFlatCoefficientBassSquareComparison P b)
    (boundedAboveFlatCoefficientPolynomialSpanMap P g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map g)))
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g)

/-- The actual raw coefficient cone identity has a whole homotopy on its original Laurent face. -/
def boundedAboveFlatCoefficientBassConeIdentityInclusionHomotopy (a : Under R) :
    Homotopy
      (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a) ≫
        boundedAboveFlatCoefficientBassConeMap P (𝟙 a))
      (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a)) :=
  ((boundedAboveFlatCoefficientLaurentIdentityHomotopy P a).postcomp
    (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a))).cast
    (boundedAboveFlatCoefficientBassConeMap_inclusion P (𝟙 a)).symm (Category.id_comp _)

/-- Parameter looping keeps the identity comparison on the actual original Raw₁ Laurent face. -/
def boundedAboveFlatCoefficientBassStepIdentityInclusionHomotopy (a : Under R) :
    Homotopy
      (parameterLoopingMap
        (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a)) ≫
        boundedAboveFlatCoefficientBassStepMap P (𝟙 a))
      (parameterLoopingMap
        (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a))) :=
  (boundedAboveFlatCoefficientBassConeIdentityInclusionHomotopy P a).parameterLooping.cast
    (parameterLoopingFunctor.map_comp _ _) rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:429-435"
  "adaptation" "Literal original Laurent inclusion under coefficient change."]
  boundedAboveFlatCoefficientBassConeMap_inclusion

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassConeFaces.lean:42-90"
  "adaptation" "The actual Laurent unit track on the cone inclusion and its parameter looping."]
  boundedAboveFlatCoefficientBassConeIdentityInclusionHomotopy
  boundedAboveFlatCoefficientBassStepIdentityInclusionHomotopy

end AlgebraicGeometry.Scheme.Modules
