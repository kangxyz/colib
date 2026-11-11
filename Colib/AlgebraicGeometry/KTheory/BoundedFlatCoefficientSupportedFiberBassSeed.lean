/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientFiberUnits
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberLocalizationModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassSeed
public import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction

/-!
# Original auxiliary intersection-support and ambient Bass seeds

The actual forward Laurent unit restricts through the original union-support
fiber and its literal inclusion into auxiliary ambient support. Original
coefficient and unit equations construct both seeds. Identity weakness change
preserves the same ambient unit, and the canonical native whole support null
interchanges with the original units at independent scalar and null times.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

/-- The original actual fiber action with its proved coefficient equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:44"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFiberLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) where
  unit := boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T
  naturality := boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso_coefficient f T

/-- The same ambient forward unit before changing to coarse relative-open weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:50"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedAmbientLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) where
  unit := boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T
  naturality := boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient Q T

/-- The original intersection-support Bass seed uses the actual square and source null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:56"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFiberBassSeed :
    boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T) :=
  (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed

/-- The original fine supported ambient Bass seed, with the same scalar/null concatenation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:63"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedAmbientBassSeed :
    boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T) :=
  (boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track.seed

/-- The literal support inclusion preserves every original Laurent-action time and level. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:70"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedFiberForget_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
      (((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n (t,
        x)) =
    ((boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track.homotopy a).level n
      (t, ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
        a).map n x)
        :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T)
    (boundedAboveFlatCoefficientSupportedAmbientLaurentAction T)
    (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (fun a ↦ by
      change Preserves (boundedAboveFlatCoefficientSupportedFiberForget f T
        ((laurentUnderFunctor R).obj a))
        (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T a)
        (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      simpa only [boundedAboveFlatCoefficientSupportedFiberLaurentAction,
        boundedAboveFlatCoefficientSupportedAmbientLaurentAction,
        boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedAboveFlatCoefficientSupportSectionUnitIso,
          boundedAboveFlatCoefficientSectionLaurentUnitIso]
        using supportedFiberForget_unit_preserves f T ((laurentUnderFunctor R).obj a)
          (laurentCoordinate a.right)) a n t x

/-- Actual intersection-support inclusion preserves its unchanged whole Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedFiberBassSeed.lean:96"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedFiberBassSeed_forget :
    boundedAboveFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) =
    boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedAmbientBassSeed T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberForget_laurent_apply f T)

omit [IsOpenImmersion f.left] in
private theorem supportedAmbientOpen_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T).obj a).space
      n) :
    ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
      (((boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track.homotopy a).level n (t,
        x)) =
    (boundedAboveFlatCoefficientSupportedOpenLaurentHomotopy f T a).level n
      (t, ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app
        a).map n x)
        :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientSupportedAmbientLaurentAction T)
    (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T)
    (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T) (fun _ _ ↦ rfl) a
      n t x

omit [IsOpenImmersion f.left] in
/-- Original supported ambient change of weakness preserves the same whole Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassSeed.lean:123"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedAmbientBassSeed_open :
    boundedAboveFlatCoefficientSupportedAmbientBassSeed T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T) =
    boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track
    (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (supportedAmbientOpen_laurent_apply f T)

private theorem supportedFiberOpenNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app a)
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T a)
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen_weak f T a)

private theorem supportedFiberOpenNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).obj a)
      (T := (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T).obj a)
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
        r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso (boundedAboveFlatCoefficientSupportOpen Q
        T a).ι r) :=
  supportedFiberOpenNull_unitCompatible f T a _ _
    (supportedFiberForget_unit_preserves f T a r)

private theorem supportedFiberOpenNull_laurentInterchange (a : Under R) :
    TrackInterchange ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
        ((laurentUnderFunctor R).obj a))
      ((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a)
      (boundedAboveFlatCoefficientSupportedOpenLaurentHomotopy f T a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (q := boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T) ((laurentUnderCoefficient
      R).app a)
    ((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).unit a)
    ((boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).unit a)
    (by
      simpa only [boundedAboveFlatCoefficientSupportedFiberLaurentAction,
        boundedAboveFlatCoefficientSupportedOpenLaurentAction,
        boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedAboveFlatCoefficientSupportSectionUnitIso,
          boundedAboveFlatCoefficientSectionLaurentUnitIso]
        using supportedFiberOpenNull_unitInterchange f T ((laurentUnderFunctor R).obj a)
          (laurentCoordinate a.right))

/-- Every original support localization-null time gives its actual coefficient transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassSeed.lean:179"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  diagramHomotopyAt
    (η := boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T)
      (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T))
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).naturality s

/-- Every time of this same original whole support null satisfies the actual seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassSeed.lean:191"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice_seed (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice f T s) =
    boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice f T s ≫
      boundedAboveFlatCoefficientSupportedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice f T s)
    (fun a n t x ↦ supportedFiberOpenNull_laurentInterchange f T a n s t x)

end AlgebraicGeometry.Scheme.Modules

