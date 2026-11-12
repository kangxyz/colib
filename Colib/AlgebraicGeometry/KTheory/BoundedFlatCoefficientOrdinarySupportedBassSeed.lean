/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOrdinarySupportedUnits
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedCoarseNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassSeed
public import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction
/-! # Original ordinary supported Bass seed and whole-null compatibility

The unchanged ambient action and seed are reused. These eleven declarations preserve the
actual supported action and both maps, including independent scalar and null parameters.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

/-- The original forward supported Laurent action with its actual coefficient equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:44"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
def boundedAboveFlatCoefficientSupportedLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedModelFunctor f) where
  unit := boundedAboveFlatCoefficientSupportedLaurentUnitIso f
  naturality := boundedAboveFlatCoefficientSupportedLaurentUnitIso_coefficient f

/-- Construct the supported seed with the original square, source null and concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:56"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
def boundedAboveFlatCoefficientSupportedBassSeed :
    boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f) :=
  (boundedAboveFlatCoefficientSupportedLaurentAction f).track.seed

/-- Original support inclusion preserves the entire supported Laurent-action track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:70"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedForget_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n (t, x)) =
      ((boundedAboveFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n
        (t, ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a).map n
          x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientSupportedLaurentAction f)
    (boundedAboveFlatCoefficientAmbientLaurentAction Q)
    (boundedAboveFlatCoefficientSupportedForgetModelTransformation f)
    (fun a S ↦ by
      simpa only [boundedAboveFlatCoefficientSupportedLaurentAction,
        boundedAboveFlatCoefficientAmbientLaurentAction,
          boundedAboveFlatCoefficientSectionLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedForgetModelTransformation,
        boundedAboveFlatCoefficientSupportedForgetModelMap,
        boundedAboveFlatCoefficientSupportedModelFunctor, boundedAboveFlatCoefficientSupportedModel,
        Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map] using
          boundedAboveFlatCoefficientSupportedUnitIso_hom f
            ((laurentUnderFunctor R).obj a) (laurentCoordinate a.right) S) a n t x

/-- The actual supported inclusion preserves the unchanged complete Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:93"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedBassSeed_forget :
    boundedAboveFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) =
      boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientAmbientBassSeed Q :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedLaurentAction f).track
    (boundedAboveFlatCoefficientAmbientLaurentAction Q).track
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedAboveFlatCoefficientSupportedForget_laurent_apply f)

/-- Identity change of weakness keeps the original ambient Laurent-action time unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:105"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientAmbientOpen_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q).obj a).space n) :
    ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedAboveFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n (t, x)) =
      ((boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a).level n
        (t, ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientAmbientLaurentAction Q)
    (boundedAboveFlatCoefficientOpenLaurentAction f)
    (boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f) (fun _ _ ↦ rfl) a n t x

/-- Original ambient change of weakness preserves its entire Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:118"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientAmbientBassSeed_open :
    boundedAboveFlatCoefficientAmbientBassSeed Q ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f) =
      boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientAmbientLaurentAction Q).track
    (boundedAboveFlatCoefficientOpenLaurentAction f).track
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedAboveFlatCoefficientAmbientOpen_laurent_apply f)

/-- The same reversed zero-to-inclusion null has genuine whole identity-action compatibility. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:130"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedOpenNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedAboveFlatCoefficientSupportedForgetModelTransformation f).app a)
      ((boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f).app a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedAboveFlatCoefficientSupportedForgetModelTransformation f).app a)
    ((boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f).app a)
    (boundedAboveFlatCoefficientSupportedZeroToOpen f a)
    (boundedAboveFlatCoefficientSupportedZeroToOpen_weak f a)

/-- Actual original support inclusion and weakness change preserve every coefficient unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:142"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedOpenNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedAboveFlatCoefficientSupportedModelFunctor f).obj a)
      (T := (boundedAboveFlatCoefficientOpenModelFunctor f).obj a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      (boundedAboveFlatCoefficientSupportedUnitIso f a r)
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a) (boundedAboveFlatCoefficientUnit (op Q,
        a) r)) :=
  boundedAboveFlatCoefficientSupportedOpenNull_unitCompatible f a _ _
    (fun S ↦ boundedAboveFlatCoefficientSupportedUnitIso_hom f a r S)

/-- Laurent scalar and supported localization-null times remain independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:154"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedOpenNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a)
      ((boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedAboveFlatCoefficientSupportedForgetModelTransformation f)
    (q := boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f) ((laurentUnderCoefficient R).app a)
    ((boundedAboveFlatCoefficientSupportedLaurentAction f).unit a)
    ((boundedAboveFlatCoefficientOpenLaurentAction f).unit a)
    (by
      simpa only [boundedAboveFlatCoefficientSupportedLaurentAction,
        boundedAboveFlatCoefficientOpenLaurentAction,
          boundedAboveFlatCoefficientSectionLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedLaurentUnitIso] using
          boundedAboveFlatCoefficientSupportedOpenNull_unitInterchange f
            ((laurentUnderFunctor R).obj a) (laurentCoordinate a.right))

/-- Each time of the same whole supported null gives its original coefficient transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:175"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
def boundedAboveFlatCoefficientSupportedOpenNullTimeSlice (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⟶
      boundedAboveFlatCoefficientOpenPrespectrumFunctor f :=
  diagramHomotopyAt
    (η := boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f ≫
      boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f)
      (boundedAboveFlatCoefficientOpenPrespectrumFunctor f))
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f).naturality s

/-- Every original localization-null time satisfies the actual unchanged strict seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassSeed.lean:187"
  "adaptation" "Original supported Bass seed and independent scalar/null-time compatibility"]
theorem boundedAboveFlatCoefficientSupportedOpenNullTimeSlice_seed (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s) =
      boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s ≫
        boundedAboveFlatCoefficientOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedLaurentAction f).track
    (boundedAboveFlatCoefficientOpenLaurentAction f).track
    (boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s)
    (fun a n t x ↦ boundedAboveFlatCoefficientSupportedOpenNull_laurentInterchange f a n s t x)

end AlgebraicGeometry.Scheme.Modules
