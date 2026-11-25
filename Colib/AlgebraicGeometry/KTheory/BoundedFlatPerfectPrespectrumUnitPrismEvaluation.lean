/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitPrismNodes
public import Colib.KTheory.Waldhausen.Iterated.UnitPrismOriginalPastingLift

/-!
# Genuine geometric lifts of the split pullback unit prisms

The four primitive faces separately evaluate the actual geometric and normalization half-tracks.
Their original five-piece parameter lifts both the postwhiskering and prewhiskering comparisons,
without replacing their native scalar action or time parameterization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CategoryTheory.Waldhausen.IteratedS.UnitPrismOriginalPastingLift
open Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

local notation "WC" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "PB" => boundedAboveFlatPerfectPullback
local notation "PE" => boundedAboveFlatPerfectPullback_isExact
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

namespace UnitTrackPostcompSimplex

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ)

/-- The unchanged geometric component G of the original postcomposition UnitTrack. -/
def geometricTrack := exactOriginalPrespectrumIsoHomotopy
  (WC Z) (WC X)
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (boundedAboveFlatPerfectPullbackCompIso f g)

/-- The unchanged binary normalization component N of the original UnitTrack. -/
def normalizationTrack := exactOriginalPrespectrumMapCompHomotopy
  (WC Z) (WC Y)
  (WC X) (PE g)
  (PE f)

/-- The unchanged source unit component A. -/
def sourceUnitTrack := boundedAboveFlatPerfectUnitHomotopy (f ≫ g)
  (Units.map f.appTop.hom.toMonoidHom r)

/-- The unchanged normalized middle unit component B. -/
def middleUnitTrack := exactOriginalPrespectrumIsoHomotopy
  (WC Z) (WC X)
  ((PE g).comp (PE f))
  ((PE g).comp (PE f))
  (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r) (PB f))

/-- The unchanged actual postwhiskered final unit component D. -/
def finalUnitTrack := (boundedAboveFlatPerfectUnitHomotopy g r).postcomp
  (K f)

/-- The exact original geometric pasting JG, with its original equality certificate. -/
def geometricPasting := exactOriginalPrespectrumPastingHomotopy
  (WC Z) (WC X)
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (boundedAboveFlatPerfectPullbackCompIso f g).hom
  (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r) (PB f)).hom
  (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
  (boundedAboveFlatPerfectPullbackCompIso f g).hom
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (boundedAboveFlatPerfectPullbackUnitIso_comp f g r)

/-- The exact original normalization pasting JN, including its full native level transport. -/
def normalizationPasting := exactNormalizationLeftTrackPasting
  (PE g) (PE g)
  (PE f) (boundedAboveFlatPerfectPullbackUnitIso g r).hom
  (fun _ ↦ (WC Y).weq_iso _ inferInstance)

private theorem geometric_first_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricFirst =
      ModelSimplex.triangle
        (F := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (G := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (H := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            ((PE g).comp (PE f))
            (boundedAboveFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            ((PE g).comp (PE f))
            ((PE g).comp (PE f))
            (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r)
              (PB f)).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          ((PE g).comp (PE f))
          (boundedAboveFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          ((PE g).comp (PE f))
          ((PE g).comp (PE f))
          (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r)
            (PB f)).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BoundedFlatPerfectBinarySimplex.first, middleUnit, middleUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BoundedFlatPerfectBinarySimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_first
    (BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
    (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
    (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r))

private theorem geometric_second_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricSecond =
      ModelSimplex.triangle
        (F := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (G := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (H := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            (PE (f ≫ g))
            (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g)
              (Units.map f.appTop.hom.toMonoidHom r)).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            ((PE g).comp (PE f))
            (boundedAboveFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          (PE (f ≫ g))
          (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g)
            (Units.map f.appTop.hom.toMonoidHom r)).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          ((PE g).comp (PE f))
          (boundedAboveFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BoundedFlatPerfectBinarySimplex.first, sourceUnit, sourceUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BoundedFlatPerfectBinarySimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_second
    (BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
    (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
    (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r) (small_geometric_unit f g r))

/-- The original geometric first triangle has its whole normalized small-model lift. -/
theorem geometric_first_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricFirst)
    (exactOriginalPrespectrumCompositionHomotopy
      (WC Z) (WC X)
      (PE (f ≫ g))
      ((PE g).comp (PE f))
      ((PE g).comp (PE f))
      (boundedAboveFlatPerfectPullbackCompIso f g).hom
      (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r) (PB f)).hom
      (fun _ ↦ (WC X).weq_iso _ inferInstance)
      (fun _ ↦ (WC X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r) (PB f)).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricFirst
    (geometric_first_normalized_face f g r)

/-- The original geometric second triangle keeps the actual source-unit normalization. -/
theorem geometric_second_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricSecond)
    (exactOriginalPrespectrumCompositionHomotopy
      (WC Z) (WC X)
      (PE (f ≫ g))
      (PE (f ≫ g))
      ((PE g).comp (PE f))
      (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
      (boundedAboveFlatPerfectPullbackCompIso f g).hom
      (fun _ ↦ (WC X).weq_iso _ inferInstance)
      (fun _ ↦ (WC X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricSecond
    (geometric_second_normalized_face f g r)

/-- Both geometric halves recover the original equality-transported pasting at every point. -/
theorem geometricPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.geometric (geometricPasting f g r) :=
  exact_pasting_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r) (PB f)).hom
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (boundedAboveFlatPerfectPullbackUnitIso_comp f g r) (simplex f g r)
    (geometric_first_lift f g r) (geometric_second_lift f g r)

private theorem normalizationPasting_original_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (exactNormalizationLeftPasting (PE g)
        (PE g) (PE f)
        (boundedAboveFlatPerfectPullbackUnitIso g r).hom
        (fun _ ↦ (WC Y).weq_iso _ inferInstance)) := by
  apply normalization_original_lift
  · exact UnitPrismNodes.normalization_first _ _ _ _ _ _ _ _
      (small_normalization_unit f g r)
  · exact UnitPrismNodes.normalization_second _ _ _ _ _ _ _ _

/-- Both individually ordered normalization triangles recover the original entire JN.
The original ofLevels endpoint transport changes neither of its independent coordinates. -/
theorem normalizationPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (normalizationPasting f g r) :=
  normalization_left_track_lift (PE g)
    (PE g) (PE f)
    (boundedAboveFlatPerfectPullbackUnitIso g r).hom
    (fun _ ↦ (WC Y).weq_iso _ inferInstance)
    (simplex f g r) (normalizationPasting_original_lift f g r)

/-- The chosen postcomposition UnitTrack itself has the exact five-piece common-simplex lift.
All original associators, both original pastings and every relative time are retained. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/UnitTrackPostcompSimplex.lean"
  "adaptation" "Actual unit prism evaluation, including all original time cuts"]
theorem native_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.parameter
      (boundedAboveFlatPerfectUnitTrackPostcomp f g r) :=
  UnitPrismParameters.parameter_lift (simplex f g r)
    (geometricTrack f g) (normalizationTrack f g) (sourceUnitTrack f g r)
    (middleUnitTrack f g r) (finalUnitTrack f g r)
    (geometricPasting f g r) (normalizationPasting f g r)
    (geometricPasting_lift f g r) (normalizationPasting_lift f g r)

end UnitTrackPostcompSimplex

namespace UnitTrackPrecompSimplex

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ)

/-- The unchanged geometric component G of the original precomposition UnitTrack. -/
def geometricTrack := exactOriginalPrespectrumIsoHomotopy
  (WC Z) (WC X)
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (boundedAboveFlatPerfectPullbackCompIso f g)

/-- The unchanged binary normalization component N of the original UnitTrack. -/
def normalizationTrack := exactOriginalPrespectrumMapCompHomotopy
  (WC Z) (WC Y)
  (WC X) (PE g)
  (PE f)

/-- The unchanged source unit component A. -/
def sourceUnitTrack := boundedAboveFlatPerfectUnitHomotopy (f ≫ g) r

/-- The unchanged normalized middle unit component B. -/
def middleUnitTrack := exactOriginalPrespectrumIsoHomotopy
  (WC Z) (WC X)
  ((PE g).comp (PE f))
  ((PE g).comp (PE f))
  (isoWhiskerLeft (PB g) (boundedAboveFlatPerfectPullbackUnitIso f r))

/-- The unchanged actual prewhiskered final unit component D. -/
def finalUnitTrack := Homotopy.precomp (K g)
  (boundedAboveFlatPerfectUnitHomotopy f r)

/-- The exact original geometric pasting JG, with its original equality certificate. -/
def geometricPasting := exactOriginalPrespectrumPastingHomotopy
  (WC Z) (WC X)
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (PE (f ≫ g))
  ((PE g).comp (PE f))
  (boundedAboveFlatPerfectPullbackCompIso f g).hom
  (isoWhiskerLeft (PB g) (boundedAboveFlatPerfectPullbackUnitIso f r)).hom
  (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom
  (boundedAboveFlatPerfectPullbackCompIso f g).hom
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (fun _ ↦ (WC X).weq_iso _ inferInstance)
  (boundedAboveFlatPerfectPullbackUnitIso_comp_target f g r)

/-- The exact original normalization pasting JN, including its full native level transport. -/
def normalizationPasting := exactNormalizationRightTrackPasting
  (PE g) (PE f)
  (PE f) (boundedAboveFlatPerfectPullbackUnitIso f r).hom
  (fun _ ↦ (WC X).weq_iso _ inferInstance)

private theorem geometric_first_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricFirst =
      ModelSimplex.triangle
        (F := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (G := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (H := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            ((PE g).comp (PE f))
            (boundedAboveFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            ((PE g).comp (PE f))
            ((PE g).comp (PE f))
            (isoWhiskerLeft (PB g)
              (boundedAboveFlatPerfectPullbackUnitIso f r)).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          ((PE g).comp (PE f))
          (boundedAboveFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          ((PE g).comp (PE f))
          ((PE g).comp (PE f))
          (isoWhiskerLeft (PB g)
            (boundedAboveFlatPerfectPullbackUnitIso f r)).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BoundedFlatPerfectBinarySimplex.first, middleUnit, middleUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BoundedFlatPerfectBinarySimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_first
    (BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
    (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
    (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r))

private theorem geometric_second_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricSecond =
      ModelSimplex.triangle
        (F := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (G := BoundedFlatPerfectBinarySimplex.sourceMap f g)
        (H := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            (PE (f ≫ g))
            (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (PE (f ≫ g))
            ((PE g).comp (PE f))
            (boundedAboveFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          (PE (f ≫ g))
          (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (PE (f ≫ g))
          ((PE g).comp (PE f))
          (boundedAboveFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (WC X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BoundedFlatPerfectBinarySimplex.first, sourceUnit, sourceUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BoundedFlatPerfectBinarySimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_second
    (BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
    (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
    (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r) (small_geometric_unit f g r))

/-- The original geometric first triangle has its whole normalized small-model lift. -/
theorem geometric_first_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricFirst)
    (exactOriginalPrespectrumCompositionHomotopy
      (WC Z) (WC X)
      (PE (f ≫ g))
      ((PE g).comp (PE f))
      ((PE g).comp (PE f))
      (boundedAboveFlatPerfectPullbackCompIso f g).hom
      (isoWhiskerLeft (PB g) (boundedAboveFlatPerfectPullbackUnitIso f r)).hom
      (fun _ ↦ (WC X).weq_iso _ inferInstance)
      (fun _ ↦ (WC X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerLeft (PB g) (boundedAboveFlatPerfectPullbackUnitIso f r)).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricFirst
    (geometric_first_normalized_face f g r)

/-- The original geometric second triangle keeps the actual source-unit normalization. -/
theorem geometric_second_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricSecond)
    (exactOriginalPrespectrumCompositionHomotopy
      (WC Z) (WC X)
      (PE (f ≫ g))
      (PE (f ≫ g))
      ((PE g).comp (PE f))
      (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom
      (boundedAboveFlatPerfectPullbackCompIso f g).hom
      (fun _ ↦ (WC X).weq_iso _ inferInstance)
      (fun _ ↦ (WC X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricSecond
    (geometric_second_normalized_face f g r)

/-- Both geometric halves recover the original equality-transported pasting at every point. -/
theorem geometricPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.geometric (geometricPasting f g r) :=
  exact_pasting_lift
    (WC Z) (WC X)
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (PE (f ≫ g))
    ((PE g).comp (PE f))
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerLeft (PB g) (boundedAboveFlatPerfectPullbackUnitIso f r)).hom
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom
    (boundedAboveFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (boundedAboveFlatPerfectPullbackUnitIso_comp_target f g r) (simplex f g r)
    (geometric_first_lift f g r) (geometric_second_lift f g r)

private theorem normalizationPasting_original_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (exactNormalizationRightPasting (PE g)
        (PE f) (PE f)
        (boundedAboveFlatPerfectPullbackUnitIso f r).hom
        (fun _ ↦ (WC X).weq_iso _ inferInstance)) := by
  apply normalization_original_lift
  · exact UnitPrismNodes.normalization_first _ _ _ _ _ _ _ _
      (small_normalization_unit f g r)
  · exact UnitPrismNodes.normalization_second _ _ _ _ _ _ _ _

/-- Both individually ordered normalization triangles recover the original entire JN.
The original ofLevels endpoint transport changes neither of its independent coordinates. -/
theorem normalizationPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (normalizationPasting f g r) :=
  normalization_right_track_lift (PE g)
    (PE f) (PE f)
    (boundedAboveFlatPerfectPullbackUnitIso f r).hom
    (fun _ ↦ (WC X).weq_iso _ inferInstance)
    (simplex f g r) (normalizationPasting_original_lift f g r)

/-- The chosen precomposition UnitTrack itself has the exact five-piece common-simplex lift.
All original associators, both original pastings and every relative time are retained. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/UnitTrackPrecompSimplex.lean"
  "adaptation" "Actual unit prism evaluation, including all original time cuts"]
theorem native_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.parameter
      (boundedAboveFlatPerfectUnitTrackPrecomp f g r) :=
  UnitPrismParameters.parameter_lift (simplex f g r)
    (geometricTrack f g) (normalizationTrack f g) (sourceUnitTrack f g r)
    (middleUnitTrack f g r) (finalUnitTrack f g r)
    (geometricPasting f g r) (normalizationPasting f g r)
    (geometricPasting_lift f g r) (normalizationPasting_lift f g r)

end UnitTrackPrecompSimplex

end AlgebraicGeometry.Scheme.Modules
