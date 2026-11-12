/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed
/-! # Ordinary coarse and fine open coefficient Bass seeds

The first fourteen original declarations retain the actual forward Laurent actions,
whole source-null tracks and prescribed seed concatenation. The graded row is not included.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original ambient forward Laurent unit, with its proved coefficient naturality. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:36"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientOpenModelFunctor f) where
  unit a := boundedAboveFlatCoefficientSectionLaurentUnitIso Q a
  naturality g := boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient Q g

/-- The original restricted forward Laurent unit on the actual native fine open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:42"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientFullOpenModelFunctor f) where
  unit a := boundedAboveFlatCoefficientSectionLaurentUnitIso P a
  naturality g := boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient P g

/-- The entire original ambient Laurent action track on the unchanged coefficient Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:48"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a

/-- The entire original restricted Laurent action track on the actual fine open Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:52"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientFullOpenLaurentAction f).track.homotopy a

/-- All four original ambient native corners with their original positive and inverse charts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:56"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientOpenPrespectrumFunctor f) a

/-- All four original fine open corners with the same coefficient charts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:60"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original ambient square comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:64"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original fine open square comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:68"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The original ambient source-leg cylinder; it is not a localization-null substitution. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:72"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientOpenPrespectrumFunctor f) a

/-- The original fine open source-leg cylinder on its unchanged native square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:76"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The original ambient pointwise seed retains the prescribed scalar/null concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:80"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientOpenLaurentAction f).track.seedMap a

/-- The original fine open pointwise seed retains that same prescribed concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:84"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientFullOpenLaurentAction f).track.seedMap a

/-- The constructed coefficient-natural original ambient Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:88"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientOpenBassSeed :
    boundedAboveFlatCoefficientOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientOpenPrespectrumFunctor f) :=
  (boundedAboveFlatCoefficientOpenLaurentAction f).track.seed

/-- The constructed coefficient-natural original fine open Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassSeed.lean:95"
  "adaptation" "Original ordinary coarse and fine open Laurent action and whole Bass seed"]
def boundedAboveFlatCoefficientFullOpenBassSeed :
    boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f) :=
  (boundedAboveFlatCoefficientFullOpenLaurentAction f).track.seed

end AlgebraicGeometry.Scheme.Modules
