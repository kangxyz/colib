/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationModelCoherence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationPerfect
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationSourceTransport
public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformationIso
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumUnitHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopySourceTransport
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedTransformationLevels
public import Colib.Topology.Prespectrum.HomotopyNamedDoubleCastLevels

/-!
# The native affine identity coefficient route contracts to its actual reflexive track

The route is the existing identity coefficient comparison followed by the precomposed
normalized geometric unit track. Only its strict source and target witnesses are cast.
The native unit equation and the original composition triangle contract this whole route
relative to both endpoints and the entire point line. The comparison, original track,
and structure times remain independent, including at the original based-loop level.

The geometric source remains `Spec.map (𝟙 R)`. Its explicit `Spec.map_id` transport changes
no level track. Postcomposition with the actual perfect inclusion does not assert any
higher coherence for termwise perfect pullback.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v

namespace AlgebraicGeometry.Scheme.Modules

local notation "A" => boundedAboveFlatAffineSectionModelMap
local notation "E" => boundedAboveFlatAffineEvaluationModelMap
local notation "P" => boundedAboveFlatAffinePullbackModelMap
local notation "coefficientTrack" => boundedAboveFlatAffineEvaluationCoefficientHomotopy
local notation "unitTrack" => boundedAboveFlatAffinePullbackIdHomotopy
local notation "ε" => boundedAboveFlatAffineEvaluationPrespectrumMap

/-- The original target is literally the prespectrum of its actual AsSmall model. -/
private theorem unitOriginalPrespectrum_eq_model
    {C : Type u} [Category.{v} C] (W : Structure C) :
    originalPrespectrum W = prespectrum (asSmallCategory W) := rfl

private theorem nativeUnitTransformation_weq
    (V W : WideSubcategory preservesZero.{u}) (F G : V ⟶ W)
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) [IsIso η] (s : V.obj.Obj) :
    W.obj.waldhausen.weq (η.app s) :=
  W.obj.waldhausen.weq_iso (η.app s) (inferInstanceAs (IsIso (η.app s)))

private def affineEvaluationUnitEta (R : CommRingCat.{u}) :
    (A (𝟙 R) ≫ E R).hom.toFunctor ⟶ (E R ≫ P (𝟙 R)).hom.toFunctor :=
  (boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom

private theorem affineEvaluationUnitEta_weq (R : CommRingCat.{u})
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationUnitEta R).app s) := by
  have : IsIso (affineEvaluationUnitEta R) := by
    unfold affineEvaluationUnitEta
    infer_instance
  exact nativeUnitTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (A (𝟙 R) ≫ E R) (E R ≫ P (𝟙 R)) (affineEvaluationUnitEta R) s

private def affineEvaluationUnitTheta (R : CommRingCat.{u}) :
    (E R ≫ P (𝟙 R)).hom.toFunctor ⟶ (E R).hom.toFunctor :=
  modelWhiskerLeftId (E R) (boundedAboveFlatAffinePullbackModelIdIso R).hom

private theorem affineEvaluationUnitTheta_weq (R : CommRingCat.{u})
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationUnitTheta R).app s) := by
  have : IsIso (affineEvaluationUnitTheta R) := by
    unfold affineEvaluationUnitTheta
    infer_instance
  exact nativeUnitTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (E R ≫ P (𝟙 R)) (E R) (affineEvaluationUnitTheta R) s

private theorem affineEvaluationUnitDelta_weq (R : CommRingCat.{u})
    (s : (asSmallCategory
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.waldhausen.weq
      ((boundedAboveFlatAffinePullbackModelIdIso R).hom.app s) :=
  nativeUnitTransformation_weq
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (P (𝟙 R)) (𝟙 _) (boundedAboveFlatAffinePullbackModelIdIso R).hom s

/-- The actual native unit route before changing its source-object presentation. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationUnitModelHomotopy (R : CommRingCat.{u}) :
    Homotopy (prespectrumMap (E R)) (prespectrumMap (E R)) :=
  prespectrumTransformationUnitHomotopy
    (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R)) («E» := E R)
    (boundedAboveFlatAffineEvaluationModelIdSource R)
    (affineEvaluationUnitEta R) (affineEvaluationUnitTheta R)
    (affineEvaluationUnitEta_weq R) (affineEvaluationUnitTheta_weq R)

/-- The proved actual model equation contracts the native unit route, with no extra premise. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationUnitModelRelHomotopy (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineEvaluationUnitModelHomotopy R).RelHomotopy
      (Topology.LoopPrespectrum.Homotopy.refl (prespectrumMap (E R))) :=
  prespectrumTransformationUnitRelHomotopy
    (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R)) («E» := E R)
    (boundedAboveFlatAffineEvaluationModelIdSource R)
    (affineEvaluationUnitEta R) (affineEvaluationUnitTheta R)
    (affineEvaluationUnitEta_weq R) (affineEvaluationUnitTheta_weq R)
    (boundedAboveFlatAffineEvaluationModelIso_id_hom R)

/-- The actual coefficient unit route, retaining both original tracks and endpoint casts. -/
def boundedAboveFlatAffineEvaluationUnitHomotopy (R : CommRingCat.{u}) :
    Homotopy (ε R) (ε R) :=
  ((coefficientTrack (𝟙 R)).trans (Homotopy.precomp (ε R) (unitTrack R))).cast
    (by rw [boundedAboveFlatAffineSectionPrespectrumFunctor_map_id, Category.id_comp])
    (Category.comp_id _)

/-- The actual geometric identity source changes only by the original `Spec.map_id` equality. -/
theorem boundedAboveFlatAffinePullbackIdHomotopy_source_eq (R : CommRingCat.{u}) :
    boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map (𝟙 R)) =
      boundedAboveFlatPerfectPullbackPrespectrumMap (𝟙 (Spec R)) :=
  congrArg (fun h : Spec R ⟶ Spec R => boundedAboveFlatPerfectPullbackPrespectrumMap h)
    (Spec.map_id R)

/-- Transport the geometric source to the actual identity scheme map, preserving the same track. -/
def boundedAboveFlatAffinePullbackSpecIdHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (𝟙 (Spec R)))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))) :=
  (unitTrack R).cast (boundedAboveFlatAffinePullbackIdHomotopy_source_eq R) rfl

/-- The `Spec.map_id` endpoint cast retains every entire original unit level. -/
theorem boundedAboveFlatAffinePullbackSpecIdHomotopy_level (R : CommRingCat.{u}) (n : ℕ) :
    (boundedAboveFlatAffinePullbackSpecIdHomotopy R).level n = (unitTrack R).level n := rfl

/-- The actual unit eta name denotes the original identity-coefficient isomorphism. -/
private theorem affineEvaluationUnitEta_eq (R : CommRingCat.{u}) :
    affineEvaluationUnitEta R = (boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom := by
  rfl

/-- The actual unit theta name denotes the original native right-unit whisker. -/
private theorem affineEvaluationUnitTheta_eq (R : CommRingCat.{u}) :
    affineEvaluationUnitTheta R =
      modelWhiskerLeftId (E R) (boundedAboveFlatAffinePullbackModelIdIso R).hom := by
  rfl

/-- The named eta certificate compares complete levels with arbitrary honest weak witnesses. -/
private theorem affineEvaluationUnitEta_constructor_level (R : CommRingCat.{u})
    (hη : ∀ x,
      (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.waldhausen.weq
          ((boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom.app x)) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
      (boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom hη).level n =
        (prespectrumTransformationHomotopy
          (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
          (affineEvaluationUnitEta R) (affineEvaluationUnitEta_weq R)).level n := by
  exact prespectrumTransformationHomotopy_level_eq_of_eq
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
    (boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom (affineEvaluationUnitEta R)
    hη (affineEvaluationUnitEta_weq R) (affineEvaluationUnitEta_eq R).symm n

/-- The first whole actual subtrack agrees with the named native unit eta. -/
private theorem affineEvaluationUnitEta_level_heq (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((coefficientTrack (𝟙 R)).level n)
      ((prespectrumTransformationHomotopy
        (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
        (affineEvaluationUnitEta R) (affineEvaluationUnitEta_weq R)).level n) := by
  exact (boundedAboveFlatAffineEvaluationCoefficientHomotopy_level_heq (𝟙 R) n).trans
    (heq_of_eq (affineEvaluationUnitEta_constructor_level R
      (fun x => (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.weq_iso _
        (by
          change IsIso ((boundedAboveFlatAffineEvaluationModelIso (𝟙 R)).hom.app x)
          infer_instance)) n))

/-- The named theta certificate compares only the actual two names and their weak witnesses. -/
private theorem affineEvaluationUnitTheta_constructor_level (R : CommRingCat.{u})
    (hθ : ∀ x,
      (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.waldhausen.weq
          ((modelWhiskerLeftId (E R)
            (boundedAboveFlatAffinePullbackModelIdIso R).hom).app x)) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
      (modelWhiskerLeftId (E R) (boundedAboveFlatAffinePullbackModelIdIso R).hom) hθ).level n =
        (prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
          (affineEvaluationUnitTheta R) (affineEvaluationUnitTheta_weq R)).level n := by
  exact prespectrumTransformationHomotopy_level_eq_of_eq
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (F := E R ≫ P (𝟙 R)) (G := E R)
    (modelWhiskerLeftId (E R) (boundedAboveFlatAffinePullbackModelIdIso R).hom)
    (affineEvaluationUnitTheta R) hθ (affineEvaluationUnitTheta_weq R)
    (affineEvaluationUnitTheta_eq R).symm n

/-- Native right-unit whiskering is the actual named theta on every complete level. -/
private theorem affineEvaluationUnitTheta_native_level (R : CommRingCat.{u}) (n : ℕ) :
    (Homotopy.precomp (prespectrumMap (E R))
      (prespectrumTransformationHomotopy
        (F := P (𝟙 R))
        (G := 𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))
        (boundedAboveFlatAffinePullbackModelIdIso R).hom
        (affineEvaluationUnitDelta_weq R))).level n =
      (prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
        (affineEvaluationUnitTheta R) (affineEvaluationUnitTheta_weq R)).level n := by
  exact (prespectrumModelWhiskerLeftIdHomotopy_level (E R)
    (boundedAboveFlatAffinePullbackModelIdIso R).hom (affineEvaluationUnitDelta_weq R) n).symm.trans
      (affineEvaluationUnitTheta_constructor_level R
        (fun x => affineEvaluationUnitDelta_weq R ((E R).hom.toFunctor.obj x)) n)

/-- The original Spec.map(id) unit track retains its complete native transformation level. -/
private theorem affineEvaluationUnitDelta_level_heq (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((unitTrack R).level n)
      ((prespectrumTransformationHomotopy
        (F := P (𝟙 R))
        (G := 𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))
        (boundedAboveFlatAffinePullbackModelIdIso R).hom
        (affineEvaluationUnitDelta_weq R)).level n) := by
  unfold boundedAboveFlatAffinePullbackIdHomotopy
  exact heq_of_eq (Homotopy.cast_level _ _ _ n)

/-- The original evaluation precomposition boundary, before named theta identification. -/
private theorem affineEvaluationUnitTheta_precomp_level_heq
    (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((Homotopy.precomp (ε R) (unitTrack R)).level n)
      ((Homotopy.precomp (prespectrumMap (E R))
        (prespectrumTransformationHomotopy
          (F := P (𝟙 R))
          (G := 𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))
          (boundedAboveFlatAffinePullbackModelIdIso R).hom
          (affineEvaluationUnitDelta_weq R))).level n) := by
  exact Homotopy.precomp_level_congr_objects
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (unitOriginalPrespectrum_eq_model
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (unitOriginalPrespectrum_eq_model
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (ε R) (prespectrumMap (E R)) (boundedAboveFlatAffineEvaluationPrespectrumMap_heq R)
    (unitTrack R)
    (prespectrumTransformationHomotopy
      (F := P (𝟙 R))
      (G := 𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))
      (boundedAboveFlatAffinePullbackModelIdIso R).hom (affineEvaluationUnitDelta_weq R)) n
    (affineEvaluationUnitDelta_level_heq R n)

/-- The second whole actual subtrack agrees with the named native unit theta. -/
private theorem affineEvaluationUnitTheta_level_heq (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((Homotopy.precomp (ε R) (unitTrack R)).level n)
      ((prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
        (affineEvaluationUnitTheta R) (affineEvaluationUnitTheta_weq R)).level n) := by
  exact (affineEvaluationUnitTheta_precomp_level_heq R n).trans
    (heq_of_eq (affineEvaluationUnitTheta_native_level R n))

/-- The original outer source cast uses strict section identity and left identity. -/
private theorem affineEvaluationUnitSource_eq (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (𝟙 R) ≫ ε R = ε R := by
  rw [boundedAboveFlatAffineSectionPrespectrumFunctor_map_id, Category.id_comp]

/-- The original outer target cast is actual evaluation composed with the actual identity. -/
private theorem affineEvaluationUnitTarget_eq (R : CommRingCat.{u}) :
    ε R ≫ 𝟙 (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)) = ε R := by
  exact Category.comp_id _

/-- The unchanged original route retains its honest source and target casts. -/
private theorem affineEvaluationUnitHomotopy_eq (R : CommRingCat.{u}) :
    boundedAboveFlatAffineEvaluationUnitHomotopy R =
      ((coefficientTrack (𝟙 R)).trans (Homotopy.precomp (ε R) (unitTrack R))).cast
        (affineEvaluationUnitSource_eq R) (affineEvaluationUnitTarget_eq R) := by
  rfl

/-- The unchanged native route retains the actual ModelIdSource cast and target rfl. -/
private theorem affineEvaluationUnitModelHomotopy_eq (R : CommRingCat.{u}) :
    boundedAboveFlatAffineEvaluationUnitModelHomotopy R =
      ((prespectrumTransformationHomotopy
        (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
        (affineEvaluationUnitEta R) (affineEvaluationUnitEta_weq R)).trans
          (prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
            (affineEvaluationUnitTheta R) (affineEvaluationUnitTheta_weq R))).cast
              (congrArg prespectrumMap (boundedAboveFlatAffineEvaluationModelIdSource R))
              rfl := by
  rfl

/-- Every complete original unit level is the native route, retaining both cast presentations. -/
theorem boundedAboveFlatAffineEvaluationUnitHomotopy_level_heq
    (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationUnitHomotopy R).level n)
      ((boundedAboveFlatAffineEvaluationUnitModelHomotopy R).level n) := by
  exact Homotopy.trans_casts_level_congr_objects_of_eq
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (unitOriginalPrespectrum_eq_model
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationUnitHomotopy R)
    (coefficientTrack (𝟙 R)) (Homotopy.precomp (ε R) (unitTrack R))
    (affineEvaluationUnitSource_eq R) (affineEvaluationUnitTarget_eq R)
    (boundedAboveFlatAffineEvaluationUnitModelHomotopy R)
    (prespectrumTransformationHomotopy
      (F := A (𝟙 R) ≫ E R) (G := E R ≫ P (𝟙 R))
      (affineEvaluationUnitEta R) (affineEvaluationUnitEta_weq R))
    (prespectrumTransformationHomotopy (F := E R ≫ P (𝟙 R)) (G := E R)
      (affineEvaluationUnitTheta R) (affineEvaluationUnitTheta_weq R))
    (congrArg prespectrumMap (boundedAboveFlatAffineEvaluationModelIdSource R)) rfl
    (affineEvaluationUnitHomotopy_eq R) (affineEvaluationUnitModelHomotopy_eq R) n
    (affineEvaluationUnitEta_level_heq R n) (affineEvaluationUnitTheta_level_heq R n)

/-- The actual reflexive evaluation track retains its native complete level. -/
private theorem affineEvaluationUnitRefl_level_heq (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((Topology.LoopPrespectrum.Homotopy.refl (ε R)).level n)
      ((Topology.LoopPrespectrum.Homotopy.refl (prespectrumMap (E R))).level n) := by
  exact Homotopy.refl_level_congr_objects
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (unitOriginalPrespectrum_eq_model
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (ε R) (prespectrumMap (E R)) (boundedAboveFlatAffineEvaluationPrespectrumMap_heq R) n

/-- The full native identity coefficient route contracts to actual reflexive evaluation. -/
@[colib_tag "COL-0381", no_expose,
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumNaturality.lean:75-91"
    "ingredient" "Identity specialization of the original coefficient comparison; \
      relative contraction additionally follows from the native unit equation and
        identity cylinder"]
def boundedAboveFlatAffineEvaluationUnitRelHomotopy (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineEvaluationUnitHomotopy R).RelHomotopy
      (Topology.LoopPrespectrum.Homotopy.refl (ε R)) :=
  Homotopy.RelHomotopy.ofObjectLevels (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (unitOriginalPrespectrum_eq_model
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (boundedAboveFlatAffineEvaluationUnitModelRelHomotopy R)
    (boundedAboveFlatAffineEvaluationUnitHomotopy R) (Topology.LoopPrespectrum.Homotopy.refl (ε R))
    (boundedAboveFlatAffineEvaluationUnitHomotopy_level_heq R)
    (affineEvaluationUnitRefl_level_heq R)

/-- Comparison time zero is the complete actual unit route. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_at_zero
    (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationUnitHomotopy R).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n).apply_zero (s, x)

/-- Comparison time one is the actual reflexive evaluation map at every track time. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_at_one
    (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (1, (s, x)) = (ε R).map n x :=
  ((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n).apply_one (s, x)

/-- The original source endpoint stays fixed for every comparison time. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_source
    (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (0, x)) = (ε R).map n x :=
  (((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n).eq_fst r (Or.inl rfl)).trans
    ((boundedAboveFlatAffineEvaluationUnitHomotopy R).at_zero n x)

/-- The original target endpoint stays fixed for every comparison time. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_target
    (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (1, x)) = (ε R).map n x :=
  (((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n).eq_fst r
    (Or.inr (Or.inl rfl))).trans ((boundedAboveFlatAffineEvaluationUnitHomotopy R).at_one n x)

/-- The entire original point line stays fixed in both homotopy coordinates. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_point
    (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).point n :=
  (((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n).eq_fst r
    (Or.inr (Or.inr rfl))).trans ((boundedAboveFlatAffineEvaluationUnitHomotopy R).at_point n s)

/-- Comparison, original track, and structure coordinates remain independent, including zero. -/
theorem boundedAboveFlatAffineEvaluationUnitRelHomotopy_comm
    (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).comm n r s x t

/-- Actual perfect inclusion postcomposes the unit contraction without any flatness assumption. -/
def boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy (R : CommRingCat.{u}) :
    ((boundedAboveFlatAffineEvaluationUnitHomotopy R).postcomp
      (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace)).RelHomotopy
      ((Topology.LoopPrespectrum.Homotopy.refl (ε R)).postcomp
        (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace)) :=
  (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).postcomp
    (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec R).toRingedSpace)

/-- The actual perfect-target unit comparison retains the independent structure coordinate. -/
theorem boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy_comm
    (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy R).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec R).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy R).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy R).comm n r s x t

end AlgebraicGeometry.Scheme.Modules
