/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ProjectionGeometry
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Sheaf
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact


/-! # The actual projection morphism on zero-section boundary sheaves

This constructs a morphism using cokernels, genuine adjunction units and literal
commuting product squares. It does not assert a smooth inverse-image coefficient
isomorphism or invertibility of the contraction boundary.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/Projection.lean`, blob
`b0edcf34c4cca830a02ce6287009ce546d620e20`.
All maps are the actual cokernel maps, inverse-image adjunction mates and literal native cylinder
projection. No invertibility assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "X₁" => Functor.obj SmoothSite.Contraction.affineLineCylinder X
local notation "Tₐ" => SmoothSite.additiveGroupObject (Spec (CommRingCat.of k))
local notation "π" => NatTrans.app (SmoothSite.Contraction.projection Tₐ) X
local notation "p" => SmoothSite.Contraction.affineLineCylinder.map π
local notation "q" => SmoothSite.Contraction.torusCylinder.map π
local notation "j₀" => NatTrans.app SmoothSite.Contraction.openInclusion X
local notation "j₁" => NatTrans.app SmoothSite.Contraction.openInclusion X₁
local notation "i₀" => SmoothSite.Contraction.nativeAffineSection (CommRingCat.of k) X 0
local notation "i₁" => SmoothSite.Contraction.nativeAffineSection (CommRingCat.of k) X₁ 0

/-- The direct images of the actual punctured product square commute. -/
def contractionPunctureProjectionDirectImageIso :
    directImage (q).left ⋙ directImage (j₀).left ≅
      directImage (j₁).left ⋙ directImage (p).left := by
  let : (baseChange (q).left).IsContinuous
      (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X).left)
      (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X₁).left) :=
    baseChange_isContinuous (q).left
  have := Functor.isContinuous_comp (baseChange (j₀).left) (baseChange (q).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X).left)
    (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X₁).left)
  let : (baseChange (p).left).IsContinuous
      (nisnevichTopology (X₁).left)
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X₁).left) :=
    baseChange_isContinuous (S := (X₁).left)
      (T := (SmoothSite.Contraction.affineLineCylinder.obj X₁).left) (p).left
  have := Functor.isContinuous_comp (baseChange (p).left) (baseChange (j₁).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X₁).left)
    (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (contractionPunctureProjectionBaseChangeIso X).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.Contraction.torusCylinder.obj X₁).left)

/-- The direct images of the actual zero-section product square commute. -/
def contractionZeroProjectionDirectImageIso :
    directImage (i₁).left ⋙ directImage (p).left ≅
      directImage (π).left ⋙ directImage (i₀).left := by
  let : (baseChange (p).left).IsContinuous
      (nisnevichTopology (X₁).left)
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X₁).left) :=
    baseChange_isContinuous (S := (X₁).left)
      (T := (SmoothSite.Contraction.affineLineCylinder.obj X₁).left) (p).left
  have := Functor.isContinuous_comp (baseChange (p).left) (baseChange (i₁).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X₁).left)
    (nisnevichTopology (X₁).left)
  let : (baseChange (π).left).IsContinuous
      (nisnevichTopology X.left) (nisnevichTopology (X₁).left) :=
    baseChange_isContinuous (S := X.left) (T := (X₁).left) (π).left
  have := Functor.isContinuous_comp (baseChange (i₀).left) (baseChange (π).left)
    (nisnevichTopology (X₁).left) (nisnevichTopology X.left) (nisnevichTopology (X₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (contractionZeroProjectionBaseChangeIso X).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology (X₁).left) (nisnevichTopology (X₁).left)

variable (F : SheafWithTransfers.{u + 1} k)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F

/-- Original punctured sections pull back along the literal projection square. -/
def contractionPuncturedProjectionMap :
    (directImage (j₀).left).obj
      ((restrict (SmoothSite.Contraction.torusCylinder.obj X) AddCommGrpCat).obj G) ⟶
      (directImage (p).left).obj
        ((directImage (j₁).left).obj
          ((restrict (SmoothSite.Contraction.torusCylinder.obj X₁) AddCommGrpCat).obj G)) :=
  (directImage (j₀).left).map (restrictionToDirectImage G q) ≫
    (contractionPunctureProjectionDirectImageIso X).hom.app
      ((restrict (SmoothSite.Contraction.torusCylinder.obj X₁) AddCommGrpCat).obj G)

/-- The punctured projection preserves the original ambient restriction relation. -/
theorem contractionPuncturedProjectionMap_restriction :
    restrictionToDirectImage G j₀ ≫ contractionPuncturedProjectionMap X F =
      restrictionToDirectImage G p ≫
        (directImage (p).left).map (restrictionToDirectImage G j₁) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext E
  change (G).obj.map ((restrictionProjection j₀).app E.unop).op ≫
      ((G).obj.map ((restrictionProjection q).app ((baseChange (j₀).left).obj E.unop)).op ≫
        (G).obj.map ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X₁)).map
          ((contractionPunctureProjectionBaseChangeIso X).hom.app E.unop)).op) =
    (G).obj.map ((restrictionProjection p).app E.unop).op ≫
      (G).obj.map ((restrictionProjection j₁).app ((baseChange (p).left).obj E.unop)).op
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change ((contractionPunctureProjectionBaseChangeIso X).hom.app E.unop).left ≫
      pullback.fst (pullback.snd E.unop.hom (j₀).left) (q).left ≫
      pullback.fst E.unop.hom (j₀).left =
    pullback.fst (pullback.snd E.unop.hom (p).left) (j₁).left ≫
      pullback.fst E.unop.hom (p).left
  exact contractionPunctureProjectionBaseChangeIso_fst X E.unop

/-- The original ambient sheaf cokernel maps to the direct image of the product
ambient cokernel. No preservation of cokernels by direct image is assumed. -/
def contractionAmbientProjectionMap :
    boundaryAmbientCokernel G j₀ ⟶ (directImage (p).left).obj (boundaryAmbientCokernel G j₁) :=
  cokernel.desc (restrictionToDirectImage G j₀)
    (contractionPuncturedProjectionMap X F ≫
      (directImage (p).left).map (cokernel.π (restrictionToDirectImage G j₁))) (by
        rw [← Category.assoc, contractionPuncturedProjectionMap_restriction, Category.assoc,
          ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

/-- The ambient map retains the actual original punctured quotient projection. -/
@[reassoc (attr := simp)]
theorem contractionAmbientProjectionMap_π :
    cokernel.π (restrictionToDirectImage G j₀) ≫ contractionAmbientProjectionMap X F =
      contractionPuncturedProjectionMap X F ≫
        (directImage (p).left).map (cokernel.π (restrictionToDirectImage G j₁)) :=
  cokernel.π_desc _ _ _

/-- The genuine projection morphism of zero-section boundary sheaves, defined as
the mate of ambient pullback followed by the actual closed inverse-image unit. -/
def contractionBoundaryProjection :
    zeroSectionBoundary X F ⟶ (directImage (π).left).obj (zeroSectionBoundary X₁ F) :=
  ((imageAdjunction (i₀).left).homEquiv _ _).symm
    (contractionAmbientProjectionMap X F ≫
      (directImage (p).left).map
        ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
      (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F))

/-- The adjoint equation records the unchanged ambient map and inverse-image units. -/
theorem contractionBoundaryProjection_unit :
    (imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀) ≫
        (directImage (i₀).left).map (contractionBoundaryProjection X F) =
      contractionAmbientProjectionMap X F ≫
        (directImage (p).left).map
          ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
        (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F) := by
  change (imageAdjunction (i₀).left).homEquiv _ _ (contractionBoundaryProjection X F) = _
  exact Equiv.apply_symm_apply _ _

/-- The actual projection sends every original punctured-section generator to
its literal product pullback followed by the target quotient and closed unit. -/
theorem contractionBoundaryProjection_generator :
    cokernel.π (restrictionToDirectImage G j₀) ≫
        (imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀) ≫
        (directImage (i₀).left).map (contractionBoundaryProjection X F) =
      contractionPuncturedProjectionMap X F ≫
        (directImage (p).left).map
          (cokernel.π (restrictionToDirectImage G j₁) ≫
            (imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
        (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F) := by
  rw [contractionBoundaryProjection_unit, ← Category.assoc,
    contractionAmbientProjectionMap_π]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
