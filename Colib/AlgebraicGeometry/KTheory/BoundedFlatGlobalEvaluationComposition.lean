/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationCompositionSplit
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumTransformationTransport
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! # The original geometric composition comparison for global evaluation -/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

private theorem first_route_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (J : A ⥤ B) (K : B ⥤ C) (L : A ⥤ C) (P : C ⥤ E)
    (M : B ⥤ D) (N : D ⥤ E) (h : L = J ⋙ K) (η : K ⋙ P ≅ M ⋙ N) :
    HEq ((eqToIso (congrArg (fun S => S ⋙ P) h) ≪≫
      Functor.associator J K P ≪≫ isoWhiskerLeft J η ≪≫
      (Functor.associator J M N).symm).hom) (whiskerLeft J η.hom) := by
  subst h
  apply heq_of_eq
  ext x
  simp

/-- Strict source transport retains every point of the original precomposed evaluation. -/
theorem evaluationCompositionFirstHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)) (W := asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
      (F := boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op ≫ evaluationModel (op X))
      (G := (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫
      evaluationRawMap f)
      (evaluationCompositionFirstIso f g).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      inferInstance)).level n =
      (Homotopy.precomp (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map g.op))
        (evaluationComparison f)).level n := by
  have hF : boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op ≫ evaluationModel (op X) =
      boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
        (boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (op X)) :=
    (congrArg (fun S => S ≫ evaluationModel (op X))
      (boundedAboveFlatGlobalSectionModelFunctor.map_comp g.op f.op)).trans (Category.assoc _ _ _)
  have hG := Category.assoc (boundedAboveFlatGlobalSectionModelFunctor.map g.op) (evaluationModel
      (op Y)) (evaluationRawMap f)
  trans (prespectrumTransformationHomotopy
    (F := boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
      (boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (op X)))
    (G := boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ (evaluationModel (op Y) ≫
      evaluationRawMap f))
    (whiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (evaluationComparisonIso f).hom)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      inferInstance)).level n
  · refine prespectrumTransformationHomotopy_level_eq_of_heq hF hG _ _ _ _ ?_ n
    exact first_route_heq (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor (evaluationModel (op
      X)).hom.toFunctor
      (evaluationModel (op Y)).hom.toFunctor (evaluationRawMap f).hom.toFunctor
      (congrArg (fun S => S.hom.toFunctor)
        (boundedAboveFlatGlobalSectionModelFunctor.map_comp g.op f.op)) (evaluationComparisonIso f)
  · exact prespectrumTransformationHomotopy_precomp_level
      (F := boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (op X))
      (G := evaluationModel (op Y) ≫ evaluationRawMap f) (evaluationComparisonIso f).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op) n

/-- The second Model track retains the actual raw postcomposition of original evaluation. -/
theorem evaluationCompositionSecondHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)) (W := asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
      (F := (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫
      evaluationRawMap f)
      (G := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
      (evaluationCompositionSecondIso f g).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      inferInstance)).level n =
      ((evaluationComparison g).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level
        n :=
  prespectrumTransformationHomotopy_postcomp_level
    (F := boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y))
    (G := evaluationModel (op Z) ≫ evaluationRawMap g) (evaluationComparisonIso g).hom
    (fun _ => (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).asSmall.weq_iso _ inferInstance)
    (evaluationRawMap f) n

private theorem target_route_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (J : A ⥤ B) (F : B ⥤ D) (G : B ⥤ C) (H : C ⥤ D) (η : F ≅ G ⋙ H) :
    HEq ((isoWhiskerLeft J η ≪≫ (Functor.associator J G H).symm).hom)
      (whiskerLeft J η.hom) := by
  apply heq_of_eq
  ext x
  simp

/-- The target Model track is original evaluation followed by total geometric composition. -/
theorem evaluationCompositionTargetHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)) (W := asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
      (F := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
      (G := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
      (evaluationCompositionTargetIso f g).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      inferInstance)).level n =
      (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
        (evaluationRawCompHomotopy f g)).level n := by
  trans (prespectrumTransformationHomotopy
    (F := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
    (G := evaluationModel (op Z) ≫ (evaluationRawMap g ≫ evaluationRawMap f))
    (whiskerLeft (evaluationModel (op Z)).hom.toFunctor (evaluationRawCompIso f g).hom)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      inferInstance)).level n
  · refine prespectrumTransformationHomotopy_level_eq_of_heq rfl (Category.assoc _ _ _) _ _ _ _ ?_ n
    exact target_route_heq (evaluationModel (op Z)).hom.toFunctor
      (evaluationRawMap (f ≫ g)).hom.toFunctor
      (evaluationRawMap g).hom.toFunctor (evaluationRawMap f).hom.toFunctor
      (evaluationRawCompIso f g)
  · rw [prespectrumTransformationHomotopy_precomp_level
      (F := evaluationRawMap (f ≫ g)) (G := evaluationRawMap g ≫ evaluationRawMap f)
      (evaluationRawCompIso f g).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
      (evaluationModel (op Z))]
    rfl

/-- Original evaluation followed by total normalized geometric composition. -/
def evaluationCompositionTotalRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op) ≫ prespectrumMap
      (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((evaluationComparison (f ≫ g)).trans
    (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (evaluationRawCompHomotopy f g))).cast rfl (Category.assoc _ _ _).symm

/-- Original evaluation followed by the unchanged two-part geometric composition track. -/
def evaluationCompositionSplitRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op) ≫ prespectrumMap
      (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((evaluationComparison (f ≫ g)).trans
    (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g))).cast rfl
        (Category.assoc _ _ _).symm

/-- The other route retains both unchanged evaluation tracks and their original whiskering. -/
def evaluationCompositionWhiskeredRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op) ≫ prespectrumMap
      (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((Homotopy.precomp (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map g.op))
      (evaluationComparison f)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun S => S ≫ prespectrumMap (evaluationModel (op X)))
        (((boundedAboveFlatGlobalSectionModelFunctor ⋙ prespectrumFunctor).map_comp
          g.op f.op).symm)))
    (Category.assoc _ _ _).symm).trans
      ((evaluationComparison g).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap f))

/-- The actual Model comparison has exactly the two original total and whiskered routes. -/
def evaluationCompositionTotalWhiskered {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionTotalRoute f g).RelHomotopy
      (evaluationCompositionWhiskeredRoute f g) := by
  apply (evaluationModelCompositionRelHomotopy f g).ofLevels _ _
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (evaluationCompositionTargetHomotopy_level f g n).symm
  · intro n
    apply Homotopy.trans_level_congr
    · exact (evaluationCompositionFirstHomotopy_level f g n).symm
    · exact (evaluationCompositionSecondHomotopy_level f g n).symm

/-- The genuine normalization triangle restores the existing split geometric target track. -/
def evaluationCompositionTotalSplit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionTotalRoute f g).RelHomotopy
      (evaluationCompositionSplitRoute f g) :=
  ((Homotopy.RelHomotopy.refl (evaluationComparison (f ≫ g))).hcomp
    (Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (evaluationRawCompTotalSplit f g))).cast rfl (Category.assoc _ _ _).symm

/-- The whole original global evaluation composition relation, with no supplied filler. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationComposition.lean"
  "adaptation" "The original split pullback track and both chosen global evaluation edges"]
def evaluationCompositionRelHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionSplitRoute f g).RelHomotopy
      (evaluationCompositionWhiskeredRoute f g) :=
  (evaluationCompositionTotalSplit f g).symm.trans (evaluationCompositionTotalWhiskered f g)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
