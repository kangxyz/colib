/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedUnits
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed

/-! # Actual auxiliary-supported coarse and fine-open Laurent seeds

The original C/F actions and seeds use the literal supported coefficient diagrams and the
same forward Laurent coordinate. This lower slice does not include the graded row or its
contraction; those require actual image-quotient grading and are separate mathematical input.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original ambient forward Laurent unit, with its proved coefficient naturality. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:46"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) where
  unit a := boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a
  naturality g := boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient Q T g

/-- The original restricted forward Laurent unit on the actual native fine open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:52"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) where
  unit a := boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The entire original ambient Laurent action track on the unchanged coefficient Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:58"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track.homotopy a

/-- The entire original restricted Laurent action track on the actual fine open Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:62"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a

/-- All four original ambient native corners with their original positive and inverse charts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:66"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- All four original fine open corners with the same coefficient charts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:70"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original ambient square comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:74"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original fine open square comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:78"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient source-leg cylinder; it is not a localization-null substitution. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:82"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The original fine open source-leg cylinder on its unchanged native square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:86"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient pointwise seed retains the prescribed scalar/null concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:90"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track.seedMap a

/-- The original fine open pointwise seed retains that same prescribed concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:94"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original ambient Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:98"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedOpenBassSeed :
    boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T) :=
  (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track.seed

/-- The constructed coefficient-natural original fine open Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:105"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenBassSeed :
    boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) :=
  (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed

end AlgebraicGeometry.Scheme.Modules
