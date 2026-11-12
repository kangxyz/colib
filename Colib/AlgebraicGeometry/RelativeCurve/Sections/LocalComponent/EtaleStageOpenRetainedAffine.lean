/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetained

/-! # Affineness of every actual retained stage

The affine fixed retained open pulls back along the existing affine transition to give the
literal retained stage object. This supplies affineness before the two final restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

instance etaleStageOpenRetained_stage_isAffine
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ U.toScheme) (a : Over i) :
    IsAffine ((etaleStageOpenBoundaryDiagram X s p i U j).obj a) := by
  change IsAffine (pullback ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι))
  exact isAffine_of_isAffineHom
    (pullback.snd ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι))

end AlgebraicGeometry.Scheme.SmoothSite
