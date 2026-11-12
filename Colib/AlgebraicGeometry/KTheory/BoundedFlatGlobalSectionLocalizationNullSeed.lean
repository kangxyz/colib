/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationFiniteNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedForgetSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenChangeSeed
/-! # The original complete finite null and independent Laurent/seed times -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The canonical zero-to-image null retains its original whole identity-action square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNullSeed.lean:26"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible ((supportedRowForget f).app a) ((openRowChangeWeak f).app a)
      ((globalSupportedOpenNull f).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((supportedRowForget f).app a) ((openRowChangeWeak f).app a)
    (globalZeroToOpen f a) (globalZeroToOpen_weak f a)

/-- Both original maps preserve the actual forward unit on their literal composite. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNullSeed.lean:34"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpen_unit (a : Under R) :
    Preserves (((supportedRowForget f).app ((laurentUnderFunctor R).obj a) ≫
      (openRowChangeWeak f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor)
      ((supportedLaurentAction f).unit a) ((openLaurentAction f).unit a) := by
  intro S
  exact (congrArg (((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor.map)
    (supportedRowForget_unit f a S)).trans
      (openRowChangeWeak_unit f a
        (((supportedRowForget f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor.obj S))

/-- Laurent-action time and original localization-null time remain independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNullSeed.lean:45"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenNull_laurentInterchange (a : Under R) :
    TrackInterchange ((globalSupportedOpenNull f).homotopy a)
      ((globalSupportedOpenNull f).homotopy ((laurentUnderFunctor R).obj a))
      ((supportedLaurentAction f).track.homotopy a)
      ((openLaurentAction f).track.homotopy a) :=
  modelDiagramNull_coefficientCompatible
    (r := supportedRowForget f) (q := openRowChangeWeak f)
    (globalSupportedOpenNull f) ((laurentUnderCoefficient R).app a)
    ((supportedLaurentAction f).unit a) ((openLaurentAction f).unit a)
    (globalSupportedOpenNull_unitCompatible f ((laurentUnderFunctor R).obj a) _ _
      (globalSupportedOpen_unit f a))

/-- Every actual global null time slice satisfies the unchanged seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNullSeed.lean:58"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenNullTimeSlice_seed (s : unitInterval) :
    (supportedLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (globalSupportedOpenNullTimeSlice f s) =
      globalSupportedOpenNullTimeSlice f s ≫ (openLaurentAction f).track.seed :=
  LaurentSeed.Track.seed_square _ _ _
    (fun a n t x => globalSupportedOpenNull_laurentInterchange f a n s t x)

/-- Finite null and tower-transition times preserve their exact independent coordinates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNullSeed.lean:67"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenFiniteNull_transition (i : ℕ) (a : Under R) (n : ℕ)
    (s : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
      (supportedRow f ⋙ prespectrumFunctor)).obj a).space n) :
    ((globalSupportedOpenFiniteNull f (i + 1)).homotopy a).level n
      (s, ((strictDiagramTransition (laurentUnderSquareFunctor R)
        (supportedLaurentAction f).track.seed i).app a).map n x) =
    ((strictDiagramTransition (laurentUnderSquareFunctor R)
      (openLaurentAction f).track.seed i).app a).map n
        (((globalSupportedOpenFiniteNull f i).homotopy a).level n (s, x)) :=
  strictDiagramIterateNull_transition (laurentUnderSquareFunctor R) (globalSupportedOpenNull f)
    (supportedLaurentAction f).track.seed (openLaurentAction f).track.seed
    (globalSupportedOpenNullTimeSlice_seed f) i a n s x

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

