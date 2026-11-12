/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Ordinary small-basis and smooth étale adjunction

Restriction is literal precomposition with the actual inclusion of separated
finite-type étale neighborhoods. Extension is its native continuous-site left
adjoint. No rigidity or assertion that the counit is an isomorphism is made.

Adapted from the ordinary adjunction portion of the Motivic source checkpoint
of 2026-10-21, `Sites/Etale/SeparatedFiniteType/Etale/ExtensionExact.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- Literal restriction to the actual separated finite-type étale basis. -/
def etaleRestrict :
    Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology X.left) AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (etaleTopology X.left) (SmoothSite.etaleTopology B)

/-- The native continuous-site left adjoint, not a replacement extension functor. -/
def etaleExtend :
    Sheaf (etaleTopology X.left) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafPullback AddCommGrpCat.{u + 1}
    (etaleTopology X.left) (SmoothSite.etaleTopology B)

/-- The actual canonical continuous-site adjunction. -/
def etaleExtendRestrictAdjunction : etaleExtend X ⊣ etaleRestrict X :=
  (toSmoothSite X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (etaleTopology X.left) (SmoothSite.etaleTopology B)

instance etaleRestrict_isRightAdjoint : (etaleRestrict X).IsRightAdjoint :=
  (etaleExtendRestrictAdjunction X).isRightAdjoint

instance etaleRestrict_isLeftAdjoint : (etaleRestrict X).IsLeftAdjoint :=
  ((toSmoothSite X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (etaleTopology X.left) (SmoothSite.etaleTopology B)).isLeftAdjoint

instance etaleRestrict_preservesFiniteLimits : PreservesFiniteLimits (etaleRestrict X) :=
  inferInstance

instance etaleRestrict_preservesFiniteColimits : PreservesFiniteColimits (etaleRestrict X) :=
  inferInstance

instance etaleRestrict_additive : (etaleRestrict X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual coefficient presheaf is retained under restriction. -/
@[simp]
theorem etaleRestrict_obj_obj
    (F : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) :
    ((etaleRestrict X).obj F).obj = (toSmoothSite X).op ⋙ F.obj := rfl

/-- Coefficient morphisms are the original natural transformations after precomposition. -/
@[simp]
theorem etaleRestrict_map_hom
    {F G : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((etaleRestrict X).map f).hom = Functor.whiskerLeft (toSmoothSite X).op f.hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed unit first uses the Kan unit and then the map to sheafification. -/
theorem etaleConstructedAdjunction_unit_app_hom
    (F : Sheaf (etaleTopology X.left) AddCommGrpCat.{u + 1}) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (toSmoothSite X) AddCommGrpCat.{u + 1}
      (etaleTopology X.left) (SmoothSite.etaleTopology B)).unit.app F).hom =
        (toSmoothSite X).op.lanUnit.app F.obj ≫
          Functor.whiskerLeft (toSmoothSite X).op
            (toSheafify (SmoothSite.etaleTopology B)
              ((toSmoothSite X).op.lan.obj F.obj)) := by
  change (sheafToPresheaf _ _).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (toSmoothSite X) AddCommGrpCat.{u + 1}
      (etaleTopology X.left) (SmoothSite.etaleTopology B)).unit.app F) = _
  simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom, NatTrans.id_app]
  simp only [Adjunction.comp_unit_app,
    Functor.lanAdjunction_unit, sheafificationAdjunction_unit_app]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed counit is sheafification of the Kan counit followed by the sheaf counit. -/
theorem etaleConstructedAdjunction_counit_app_hom
    (F : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (toSmoothSite X) AddCommGrpCat.{u + 1}
      (etaleTopology X.left) (SmoothSite.etaleTopology B)).counit.app F).hom =
        sheafifyMap (SmoothSite.etaleTopology B)
          (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj) ≫
            sheafifyLift (SmoothSite.etaleTopology B) (𝟙 F.obj) F.property := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).comp
      (sheafificationAdjunction (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}))
    (fullyFaithfulSheafToPresheaf (etaleTopology X.left) AddCommGrpCat.{u + 1})
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback (toSmoothSite X)
      AddCommGrpCat.{u + 1} (etaleTopology X.left) (SmoothSite.etaleTopology B))
    (R := etaleRestrict X) (Iso.refl _) (Iso.refl _) F
  change (_ : _ ⟶ F) = _ at h
  have h' := congrArg (fun f ↦ f.hom) h
  simp only [etaleRestrict, Functor.sheafPullbackConstruction.sheafPullback, Functor.comp_obj,
    ObjectProperty.ι_obj, Functor.id_obj, Functor.id_map, Iso.refl_inv, NatTrans.id_app,
    Functor.whiskeringLeft_obj_obj, Functor.comp_map, Adjunction.comp_counit_app,
    Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, Category.comp_id] at h'
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h'
  simpa [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Functor.sheafPullbackConstruction.sheafPullback] using h'

/-- Canonical identification with left Kan extension followed by actual sheafification. -/
def etaleExtendConstructionIso :
    etaleExtend X ≅ sheafToPresheaf (etaleTopology X.left) AddCommGrpCat.{u + 1} ⋙
      (toSmoothSite X).op.lan ⋙
        presheafToSheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

/-- This identification preserves the canonical unit, rather than only extension objects. -/
@[reassoc]
theorem etaleExtendConstructionIso_unit_app
    (F : Sheaf (etaleTopology X.left) AddCommGrpCat.{u + 1}) :
    (etaleExtendRestrictAdjunction X).unit.app F ≫
      (etaleRestrict X).map ((etaleExtendConstructionIso X).hom.app F) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (toSmoothSite X) AddCommGrpCat.{u + 1}
          (etaleTopology X.left) (SmoothSite.etaleTopology B)).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The chosen counit corresponds to the actual Kan-extension/sheafification counit. -/
@[reassoc]
theorem etaleExtendConstructionIso_counit_app
    (F : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) :
    (etaleExtendConstructionIso X).hom.app ((etaleRestrict X).obj F) ≫
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (toSmoothSite X) AddCommGrpCat.{u + 1}
        (etaleTopology X.left) (SmoothSite.etaleTopology B)).counit.app F =
          (etaleExtendRestrictAdjunction X).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

/-- Restriction valued in sheaves on the full small étale site, including non-qc objects. -/
def fullSmallEtaleRestrict :
    Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleRestrict X ⋙ (sheafEquivSmallEtale X).functor

/-- Extension from the full small site uses the literal restriction equivalence first. -/
def fullSmallEtaleExtend :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1} :=
  (sheafEquivSmallEtale X).inverse ⋙ etaleExtend X

/-- The full-small/smooth adjunction, with the actual equivalence inserted in its direction. -/
@[colib_tag "COL-1061"]
def fullSmallEtaleAdjunction : fullSmallEtaleExtend X ⊣ fullSmallEtaleRestrict X :=
  (sheafEquivSmallEtale X).symm.toAdjunction.comp (etaleExtendRestrictAdjunction X)

/-- The full-small unit is the composite of the equivalence unit and the basis unit. -/
theorem fullSmallEtaleAdjunction_unit_app
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleAdjunction X).unit.app F =
      (sheafEquivSmallEtale X).symm.toAdjunction.unit.app F ≫
        (sheafEquivSmallEtale X).functor.map
          ((etaleExtendRestrictAdjunction X).unit.app
            ((sheafEquivSmallEtale X).inverse.obj F)) :=
  Adjunction.comp_unit_app _ _ F

/-- The canonical full-small counit uses the equivalence counit, then the basis counit. -/
theorem fullSmallEtaleAdjunction_counit_app
    (F : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleAdjunction X).counit.app F =
      (etaleExtend X).map ((sheafEquivSmallEtale X).symm.toAdjunction.counit.app
        ((etaleRestrict X).obj F)) ≫ (etaleExtendRestrictAdjunction X).counit.app F :=
  Adjunction.comp_counit_app _ _ F

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
