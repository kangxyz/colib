/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
/-! # Ordinary restriction preserves the complete original Laurent seed

Only the first three original restriction statements are selected here.
The graded-row statements and final stable restriction are separate work.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
/-- The actual restriction preserves each original forward Laurent-unit component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenSeedCompatibility.lean:43"
  "adaptation" "Original actual ordinary restriction whole Laurent and seed square"]
theorem boundedAboveFlatCoefficientOpenRestriction_laurentUnit (a : Under R) :
    Preserves
      ((boundedAboveFlatCoefficientOpenRestrictionModelTransformation f).app
        ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((boundedAboveFlatCoefficientOpenLaurentAction f).unit a)
      ((boundedAboveFlatCoefficientFullOpenLaurentAction f).unit a) :=
  boundedAboveFlatCoefficientSectionLaurentUnitIso_restriction f a

/-- Original native restriction preserves every level and the same Laurent-action time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenSeedCompatibility.lean:52"
  "adaptation" "Original actual ordinary restriction whole Laurent and seed square"]
theorem boundedAboveFlatCoefficientOpenRestriction_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedAboveFlatCoefficientOpenLaurentHomotopy f a).level n (t, x)) =
      (boundedAboveFlatCoefficientFullOpenLaurentHomotopy f a).level n
        (t, ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map n
          x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientOpenLaurentAction f)
    (boundedAboveFlatCoefficientFullOpenLaurentAction f)
    (boundedAboveFlatCoefficientOpenRestrictionModelTransformation f)
    (boundedAboveFlatCoefficientOpenRestriction_laurentUnit f) a n t x

/-- The actual coefficient-natural original restriction preserves the entire original Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenSeedCompatibility.lean:66"
  "adaptation" "Original actual ordinary restriction whole Laurent and seed square"]
theorem boundedAboveFlatCoefficientOpenBassSeed_restriction :
    boundedAboveFlatCoefficientOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f) =
      boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientFullOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientOpenLaurentAction f).track
    (boundedAboveFlatCoefficientFullOpenLaurentAction f).track
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenRestriction_laurent_apply f)

end AlgebraicGeometry.Scheme.Modules
