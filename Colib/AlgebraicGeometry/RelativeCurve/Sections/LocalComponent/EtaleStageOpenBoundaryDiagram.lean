/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenDiagram
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleBoundaryDiagram

/-! # The fixed full boundary on the actual restarted component diagram

A fixed boundary `d : Z ⟶ U` is pulled back on exactly the same `Over i` index
as the component model. No reduction of `Z` or extension to the whole curve is used.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
attribute [local instance] IsCofiltered.isConnected

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)

/-- The fixed original boundary pulled back along the same stage transitions. -/
def etaleStageOpenBoundaryDiagram : Over i ⥤ Scheme.{u} :=
  Over.post (etaleCurveDiagram X s p) ⋙ Over.pullback (d ≫ U.ι) ⋙ Over.forget Z

/-- The literal boundary-to-component natural transformation on the shared index. -/
def etaleStageOpenBoundaryMap : etaleStageOpenBoundaryDiagram X s p i U d ⟶
    etaleStageOpenDiagram X s p i U where
  app a := etaleBoundaryBaseChangeMap ((etaleCurveDiagram X s p).map a.hom) U.ι d
  naturality a b v := by
    change pullback.lift _ _ _ ≫ etaleBoundaryBaseChangeMap _ U.ι d =
      etaleBoundaryBaseChangeMap _ U.ι d ≫ pullback.lift _ _ _
    apply pullback.hom_ext
    · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]

/-- Each stage retains the entire fixed boundary by actual Cartesian base change. -/
theorem etaleStageOpenBoundaryMap_isPullback (a : Over i) :
    IsPullback ((etaleStageOpenBoundaryMap X s p i U d).app a)
      (pullback.snd ((etaleCurveDiagram X s p).map a.hom) (d ≫ U.ι))
      (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι) d :=
  etaleBoundaryBaseChangeMap_isPullback _ U.ι d

instance etaleStageOpenBoundaryMap_isClosedImmersion [IsClosedImmersion d] (a : Over i) :
    IsClosedImmersion ((etaleStageOpenBoundaryMap X s p i U d).app a) :=
  inferInstanceAs (IsClosedImmersion (etaleBoundaryBaseChangeMap _ U.ι d))

instance etaleStageOpenBoundaryDiagram_map_isAffineHom {a b : Over i} (v : a ⟶ b) :
    IsAffineHom ((etaleStageOpenBoundaryDiagram X s p i U d).map v) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) (d ≫ U.ι)
    ((Over.post (etaleCurveDiagram X s p)).map v) (by
      change IsAffineHom ((etaleCurveDiagram X s p).map v.left)
      infer_instance)

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left)

/-- The original over-post cone, pulled back along the fixed entire boundary. -/
def etaleStageOpenBoundaryCone : Cone (etaleStageOpenBoundaryDiagram X s p i U d) :=
  (Over.forget Z).mapCone
    ((Over.pullback (d ≫ U.ι)).mapCone ((etaleCurveCone X B hX s p).overPost i))

/-- The entire fixed boundary cone is limiting by actual pullback preservation. -/
def etaleStageOpenBoundaryConeIsLimit : IsLimit (etaleStageOpenBoundaryCone X s p i U d B hX) :=
  isLimitOfPreserves (Over.forget Z)
    (isLimitOfPreserves (Over.pullback (d ≫ U.ι))
      ((etaleCurveConeIsLimit X B hX s p).overPost i))

/-- The exact original cone-vertex boundary map for the restarted component model. -/
def etaleStageOpenBoundaryLimitMap : (etaleStageOpenBoundaryCone X s p i U d B hX).pt ⟶
    (etaleStageOpenCone X s p i U B hX).pt :=
  etaleBoundaryBaseChangeMap ((etaleCurveCone X B hX s p).π.app i) U.ι d

/-- The full-boundary cone and component cone commute at each shared stage. -/
theorem etaleStageOpenBoundaryCone_square (a : Over i) :
    (etaleStageOpenBoundaryCone X s p i U d B hX).π.app a ≫
      (etaleStageOpenBoundaryMap X s p i U d).app a =
    etaleStageOpenBoundaryLimitMap X s p i U d B hX ≫
      (etaleStageOpenCone X s p i U B hX).π.app a := by
  change pullback.lift _ _ _ ≫ etaleBoundaryBaseChangeMap _ U.ι d =
    etaleBoundaryBaseChangeMap _ U.ι d ≫ pullback.lift _ _ _
  apply pullback.hom_ext
  · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- The original boundary is retained at the actual strict-local component vertex. -/
theorem etaleStageOpenBoundaryLimitMap_isPullback :
    IsPullback (etaleStageOpenBoundaryLimitMap X s p i U d B hX)
      (pullback.snd ((etaleCurveCone X B hX s p).π.app i) (d ≫ U.ι))
      (pullback.snd ((etaleCurveCone X B hX s p).π.app i) U.ι) d :=
  etaleBoundaryBaseChangeMap_isPullback _ U.ι d

instance etaleStageOpenBoundaryLimitMap_isClosedImmersion [IsClosedImmersion d] :
    IsClosedImmersion (etaleStageOpenBoundaryLimitMap X s p i U d B hX) :=
  inferInstanceAs (IsClosedImmersion (etaleBoundaryBaseChangeMap _ U.ι d))

/-- The actual limit-to-stage square of full boundaries is Cartesian over the
actual limit-to-stage component map, not merely commutative. -/
theorem etaleStageOpenBoundaryCone_isPullback (a : Over i) :
    IsPullback ((etaleStageOpenBoundaryCone X s p i U d B hX).π.app a)
      (etaleStageOpenBoundaryLimitMap X s p i U d B hX)
      ((etaleStageOpenBoundaryMap X s p i U d).app a)
      ((etaleStageOpenCone X s p i U B hX).π.app a) := by
  refine IsPullback.of_right ?_
    (etaleStageOpenBoundaryCone_square X s p i U d B hX a)
    (etaleStageOpenBoundaryMap_isPullback X s p i U d a).flip
  change IsPullback (pullback.lift _ _ _ ≫ pullback.snd _ _)
    (etaleBoundaryBaseChangeMap _ U.ι d) d
    (pullback.lift _ _ _ ≫ pullback.snd _ _)
  simp only [pullback.lift_snd]
  exact (etaleBoundaryBaseChangeMap_isPullback _ U.ι d).flip

end AlgebraicGeometry.Scheme.SmoothSite
