/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenGradingNaturality
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed

/-! # Original ordinary graded Laurent seed and whole compatibility

Only the assigned ordinary declarations are migrated. There is no auxiliary support T.
Actual original models, selected zero, scalar/null times and seed squares are preserved.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Opposite
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]



/-- The same actual open unit acts on the original graded Model; only weakness changes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:104"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientGradedOpenModelFunctor f) where
  unit a := boundedAboveFlatCoefficientSectionLaurentUnitIso P a
  naturality g := boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient P g

/-- The unchanged forward Laurent unit realized in the original graded coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:110"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).track.homotopy a

/-- The original graded native four-corner square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:114"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original graded comparison map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:118"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The original graded source-leg cylinder, with every time parameter unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:122"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The graded pointwise seed uses that original source-leg null and forward scalar action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:126"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).track.seedMap a

/-- The constructed coefficient-natural original graded Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassSeed.lean:130"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassSeed :
    boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).track.seed

end AlgebraicGeometry.Scheme.Modules
