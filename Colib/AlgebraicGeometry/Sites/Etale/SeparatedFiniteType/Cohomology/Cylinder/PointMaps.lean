/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointDiagrams
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1ProjectionIso
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-! # Original projection and zero-section maps on actual pointed puncture diagrams

The index is exactly the point-neighborhood category used by ordinaryPointCohomologyDiagram.
No global dimension drop on a finite-stage puncture is asserted.
-/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/PointDiagrams.lean`, blob
`dd2775346278c19a5a32ed24c081c7cf0f451835`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.
Only the projection, zero-section and two compatibility equations are extracted; the frozen
original pointed diagrams are imported unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- Projection pullback is the literal original projection on every neighborhood. -/
def pointedProjection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    G.op ⋙ P ⟶ pointedCylinderValues R Φ P G where
  app V := A1.projectionPullback R P (G.obj V.unop)
  naturality _ _ f := A1.projectionPullback_naturality R P (G.map f.unop)

/-- Zero-section restriction is the literal original section on every neighborhood. -/
def pointedZeroSection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    pointedCylinderValues R Φ P G ⟶ G.op ⋙ P where
  app V := A1.sectionPullback R P (G.obj V.unop) 0
  naturality V W f := by
    change P.map (SmoothSite.Contraction.affineLineCylinder.map (G.map f.unop)).op ≫
      P.map (SmoothSite.Contraction.nativeAffineSection R (G.obj W.unop) 0).op =
        P.map (SmoothSite.Contraction.nativeAffineSection R (G.obj V.unop) 0).op ≫
          P.map (G.map f.unop).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      SmoothSite.Contraction.nativeAffineSection_naturality]

/-- The original zero section is a retraction of the original projection on the whole diagram. -/
theorem pointedProjection_zeroSection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    pointedProjection R Φ P G ≫ pointedZeroSection R Φ P G = 𝟙 _ := by
  apply NatTrans.ext
  funext V
  exact A1.projectionPullback_sectionPullback R P (G.obj V.unop) 0

/-- Actual zero-section restriction commutes with actual puncture restriction. -/
theorem pointedCylinderRestriction_zeroSection :
    pointedCylinderRestriction R j Φ P ≫ pointedZeroSection R Φ P (pointedPuncture R j Φ) =
      pointedZeroSection R Φ P (pointedBase R Φ) ≫ pointedRestriction R j Φ P := by
  apply NatTrans.ext
  funext V
  change P.map (SmoothSite.Contraction.affineLineCylinder.map
      ((pointedPunctureInclusion R j Φ).app V.unop)).op ≫
    P.map (SmoothSite.Contraction.nativeAffineSection R ((pointedPuncture R j Φ).obj V.unop) 0).op =
      P.map (SmoothSite.Contraction.nativeAffineSection R ((pointedBase R Φ).obj V.unop) 0).op ≫
        P.map ((pointedPunctureInclusion R j Φ).app V.unop).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    SmoothSite.Contraction.nativeAffineSection_naturality]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
