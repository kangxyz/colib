/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Colib.Util.References
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-!
# The canonical ordinary-to-transfer section source

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Cohomology/Ext/OrdinarySource.lean`, blob
`3299b08d82e4b2c4634406d1fdaa9958a3c0bc71`.
The native Stacks free Yoneda sheaf represents ordinary sections; the existing
signed transfer representable is unchanged. These comparisons use the actual
sheafified identity cycle, not an unspecified isomorphism.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE
universe u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k]

/-- The corresponding ordinary Hom equivalence retains the original section source. -/
def ordinaryTransferHomEquiv (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) :
    ((transferRepresentable k).obj (Cor.mk X) ⟶ F) ≃+
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).obj X ⟶
        (toSheaf k).obj F) :=
  (transferSectionsEquiv k (Cor.mk X) F).trans
    (sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F)).symm

/-- The ordinary source maps to the underlying sheaf of the actual transfer source. -/
def ordinaryToTransferSource (X : SmoothSite (Spec (.of k))) :
    ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).obj X) ⟶
        (toSheaf k).obj ((transferRepresentable k).obj (Cor.mk X)) :=
  ordinaryTransferHomEquiv k X _ (𝟙 _)

/-- Evaluation of the Hom equivalence is the original transfer section. -/
theorem ordinaryTransferHomEquiv_sections (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F)
        (ordinaryTransferHomEquiv k X F f) = transferSectionsEquiv k (Cor.mk X) F f :=
  (sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F)).apply_symm_apply _

/-- The Hom equivalence is exactly precomposition with the specified source map
following the genuine forgetful functor, not a different abstract bijection. -/
theorem ordinaryTransferHomEquiv_apply (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    ordinaryTransferHomEquiv k X F f = ordinaryToTransferSource k X ≫ (toSheaf k).map f := by
  apply (sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F)).injective
  have h := sectionsEquiv_naturality X
    (ordinaryToTransferSource k X) ((toSheaf k).map f)
  change (sectionsAddEquiv.{u + 1} X ((toSheaf k).obj F))
      (ordinaryToTransferSource k X ≫ (toSheaf k).map f) = _ at h
  rw [ordinaryTransferHomEquiv_sections, h]
  change transferSectionsEquiv k (Cor.mk X) F f =
    f.hom.hom.app (op (Cor.mk X))
      (sectionsAddEquiv.{u + 1} X
        ((toSheaf k).obj ((transferRepresentable k).obj (Cor.mk X)))
          (ordinaryTransferHomEquiv k X _ (𝟙 _)))
  rw [ordinaryTransferHomEquiv_sections]
  simpa only [Category.id_comp] using
    transferSectionsEquiv_comp k (Cor.mk X) (𝟙 _) f

/-- The specified source map commutes with every actual smooth-site graph restriction. -/
theorem ordinaryToTransferSource_naturality
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (freeYoneda.{u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))).map f ≫
        ordinaryToTransferSource k Y =
      ordinaryToTransferSource k X ≫
        (toSheaf k).map ((transferRepresentable k).map ((Cor.graphFunctor k).map f)) := by
  let R := (transferRepresentable k).obj (Cor.mk Y)
  apply (sectionsAddEquiv.{u + 1} X ((toSheaf k).obj R)).injective
  change sectionsEquiv X _ (_ ≫ _) = _
  rw [sectionsEquiv_naturality_left]
  let a : Cor.mk X ⟶ Cor.mk Y := (Cor.graphFunctor k).map f
  let r : (transferRepresentable k).obj (Cor.mk X) ⟶ R :=
    (transferRepresentable k).map a
  rw [← ordinaryTransferHomEquiv_apply k X R r,
    ordinaryTransferHomEquiv_sections]
  change PresheafWithTransfers.transfer R.obj ((Cor.graphFunctor k).map f)
      (sectionsAddEquiv.{u + 1} Y ((toSheaf k).obj R)
          (ordinaryTransferHomEquiv k Y R (𝟙 R))) = _
  rw [ordinaryTransferHomEquiv_sections]
  have h := (transferSectionsEquiv_naturality_left k R a (𝟙 R)).symm
  change PresheafWithTransfers.transfer R.obj a
      (transferSectionsEquiv k (Cor.mk Y) R (𝟙 R)) =
    transferSectionsEquiv k (Cor.mk X) R (r ≫ 𝟙 R) at h
  rw [Category.comp_id] at h
  exact h

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Cohomology/Ext/OrdinarySource.lean:111-207"
  "adaptation" "Canonical ordinary source map with actual section and graph naturality"]
  ordinaryTransferHomEquiv ordinaryToTransferSource
  ordinaryTransferHomEquiv_apply ordinaryToTransferSource_naturality

end AlgebraicGeometry.SheafWithTransfers

