/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassConeIdentityFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientCompositionTracks
public import Colib.Topology.Prespectrum.ConeSquareMapComposition

/-!
# Literal Laurent faces of coefficient Bass composition

The direct and successive raw cone maps retain their original Laurent inclusion tracks.
Both complete null tracks are fixed; no geometric comparison square is assumed to exist.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Paste exactly the two original Bass comparison homotopies before taking any cone. -/
def boundedAboveFlatCoefficientBassCompositeComparison :=
  coneSquarePastedHomotopy
    (boundedAboveFlatCoefficientBassSquareComparison P a)
    (boundedAboveFlatCoefficientBassSquareComparison P b)
    (boundedAboveFlatCoefficientBassSquareComparison P c)
    (boundedAboveFlatCoefficientPolynomialSpanMap P u)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedAboveFlatCoefficientPolynomialSpanMap P v)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientBassComparisonHomotopy P u)
    (boundedAboveFlatCoefficientBassComparisonHomotopy P v)

/-- Original coefficient composition gives a whole comparison on the literal Laurent inclusion. -/
def boundedAboveFlatCoefficientBassConeCompositionInclusionHomotopy :
    Homotopy
      (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a) ≫
        boundedAboveFlatCoefficientBassConeMap P (u ≫ v))
      (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a) ≫
        (boundedAboveFlatCoefficientBassConeMap P u ≫
          boundedAboveFlatCoefficientBassConeMap P v)) :=
  ((boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v).postcomp
    (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P c))).cast
    (boundedAboveFlatCoefficientBassConeMap_inclusion P (u ≫ v)).symm (by
      symm
      calc
        _ = (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a) ≫
            boundedAboveFlatCoefficientBassConeMap P u) ≫
            boundedAboveFlatCoefficientBassConeMap P v :=
          (Category.assoc _ _ _).symm
        _ = (boundedAboveFlatPerfectPullbackPrespectrumMap
              (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
            mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P b)) ≫
            boundedAboveFlatCoefficientBassConeMap P v := by
          rw [boundedAboveFlatCoefficientBassConeMap_inclusion]
        _ = boundedAboveFlatPerfectPullbackPrespectrumMap
              (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
            (boundedAboveFlatPerfectPullbackPrespectrumMap
                (coefficientMap P ((laurentUnderFunctor R).map v)) ≫
              mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P c)) := by
          rw [Category.assoc, boundedAboveFlatCoefficientBassConeMap_inclusion]
        _ = _ := (Category.assoc _ _ _).symm)

/-- The original cone-face composition comparison loops without identifying any time parameters. -/
def boundedAboveFlatCoefficientBassStepCompositionInclusionHomotopy :
    Homotopy
      (parameterLoopingMap
        (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a)) ≫
        boundedAboveFlatCoefficientBassStepMap P (u ≫ v))
      (parameterLoopingMap
        (mappingConeInclusion (boundedAboveFlatCoefficientBassSquareComparison P a)) ≫
        (boundedAboveFlatCoefficientBassStepMap P u ≫
          boundedAboveFlatCoefficientBassStepMap P v)) :=
  (boundedAboveFlatCoefficientBassConeCompositionInclusionHomotopy P u v).parameterLooping.cast
    (parameterLoopingFunctor.map_comp _ _) (by
      change parameterLoopingFunctor.map (_ ≫ (_ ≫ _)) = _
      rw [Functor.map_comp, Functor.map_comp]
      rfl)

/-- The exact direct raw map's original full cone nullhomotopy. -/
def boundedAboveFlatCoefficientBassDirectConeNullTrack :=
  ((mappingConeHomotopy (boundedAboveFlatCoefficientBassSquareComparison P a)).postcomp
    (boundedAboveFlatCoefficientBassConeMap P (u ≫ v))).cast (Category.assoc _ _ _)
    (zeroHom_comp _)

/-- The actual composite raw map's original full cone nullhomotopy. -/
def boundedAboveFlatCoefficientBassCompositeConeNullTrack :=
  ((mappingConeHomotopy (boundedAboveFlatCoefficientBassSquareComparison P a)).postcomp
    (boundedAboveFlatCoefficientBassConeMap P u ≫
      boundedAboveFlatCoefficientBassConeMap P v)).cast
    (Category.assoc _ _ _) (zeroHom_comp _)

/-- This is precisely the remaining moving nullhomotopy square for the fixed pair of raw maps.
It is a type of required data, not a claim that these data have been constructed. -/
abbrev BoundedAboveFlatCoefficientBassCompositionNullSquare :=
  (boundedAboveFlatCoefficientBassDirectConeNullTrack P u v).Square
    (boundedAboveFlatCoefficientBassCompositeConeNullTrack P u v)
    (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
      (boundedAboveFlatCoefficientBassConeCompositionInclusionHomotopy P u v))
    (Topology.LoopPrespectrum.Homotopy.refl (zeroHom _ _))

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassConeFaces.lean:53-140"
  "adaptation" "Actual Laurent inclusion and both original cone-cylinder tracks."]
  boundedAboveFlatCoefficientBassConeCompositionInclusionHomotopy
  boundedAboveFlatCoefficientBassStepCompositionInclusionHomotopy
  boundedAboveFlatCoefficientBassDirectConeNullTrack
  boundedAboveFlatCoefficientBassCompositeConeNullTrack

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassConditionalLaws.lean:37-48"
  "adaptation" "The literal pasting of the two original comparison homotopies."]
  boundedAboveFlatCoefficientBassCompositeComparison

end AlgebraicGeometry.Scheme.Modules
