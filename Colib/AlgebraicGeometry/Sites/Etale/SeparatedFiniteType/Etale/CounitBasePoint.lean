/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.BasePointComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitNeighborhoods
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPullbackNaturality
public import Colib.CategoryTheory.Sites.Point.ComapGerms

/-!
# The canonical counit is the original structural neighborhood pullback

The source comparison is the native base-point comparison, including its actual
adjunction mates and the original dense-basis equivalence. The counit is compared
with the structural map on original marked affine neighborhoods.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S : Scheme.{u}} [IsAffine S]
  (Y : SmoothSite S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ Y.left)

local instance : IsAffine (SmoothSite.base S).left := inferInstanceAs (IsAffine S)

local instance : InitiallySmall.{u + 1} (SmoothSite.EtaleNeighborhood Y ξ) :=
  SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ

local instance : InitiallySmall.{u + 1}
    (toSmoothSite (SmoothSite.base S) ⋙
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber).Elements :=
  initiallySmall_of_essentiallySmall _

local instance :
    (toSmallEtale S).IsDenseSubsite (etaleTopology S) S.smallEtaleTopology :=
  toSmallEtale_isDenseSubsite (SmoothSite.base S)

/-- The lifted native source comparison evaluates the original comapped germ. -/
@[reassoc]
theorem comapGerm_fullSmallEtaleExtendBaseSheafFiberIso_hom
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : EtaleSeparatedFiniteType S)
    (x : (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber.obj
      ((toSmoothSite (SmoothSite.base S)).obj U)) :
    (smoothNeighborhoodComapPoint Y ξ).toPresheafFiber U x
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G).obj ≫
      ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiberComapIso
        (toSmoothSite (SmoothSite.base S))
          (toSmoothSite_etale_coverPreserving (SmoothSite.base S))
            AddCommGrpCat.{u + 1}).hom.app
              ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G) ≫
      (fullSmallEtaleExtendBaseSheafFiberIso Y ξ).hom.app G =
    (baseGeometricPoint Y ξ).toPresheafFiber ((toSmallEtale S).obj U)
      ((etaleNeighborhoodBaseFiberIso Y ξ).hom.app U x) G.obj := by
  simp only [fullSmallEtaleExtendBaseSheafFiberIso, etaleExtendBaseSheafFiberIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Iso.symm_hom, Category.id_comp, Category.assoc]
  erw [Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc]
  change (smoothNeighborhoodComapPoint Y ξ).toPresheafFiber U x _ ≫
    (smoothNeighborhoodBasePointIso Y ξ).inv.presheafFiber.app _ ≫ _ = _
  simp only [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_assoc]
  simp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_map,
    GrothendieckTopology.Point.toPresheafFiber_naturality,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  have ht := ((toSmallEtale S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (etaleTopology S) S.smallEtaleTopology).right_triangle_components G
  have h := congrArg (fun q ↦ q.hom.app (op U)) ht
  have hc := toSmallEtalePullbackEquivIso_counit_app (S := S) G
  rw [← hc] at h
  change
    (((toSmallEtale S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (etaleTopology S) S.smallEtaleTopology).unit.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G)).hom.app (op U) ≫
      ((toSmallEtalePullbackEquivIso (S := S)).hom.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G)).hom.app
          (op ((toSmallEtale S).obj U)) ≫
      ((sheafEquivSmallEtale (SmoothSite.base S)).counitIso.hom.app G).hom.app
        (op ((toSmallEtale S).obj U)) = 𝟙 _ at h
  rw [← Category.assoc] at h
  rw [← Category.assoc, ← Category.assoc]
  erw [h, Category.id_comp]
  rfl

/-- The source comparison sends the actual extension-unit germ to its native base germ. -/
@[reassoc]
theorem unit_germ_fullSmallEtaleExtendBaseSheafFiberIso_hom
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : EtaleSeparatedFiniteType S)
    (x : (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber.obj
      ((toSmoothSite (SmoothSite.base S)).obj U)) :
    ((etaleExtendRestrictAdjunction (SmoothSite.base S)).unit.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G)).hom.app (op U) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).toPresheafFiber
        ((toSmoothSite (SmoothSite.base S)).obj U) x
          ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj ≫
      (fullSmallEtaleExtendBaseSheafFiberIso Y ξ).hom.app G =
    (baseGeometricPoint Y ξ).toPresheafFiber ((toSmallEtale S).obj U)
      ((etaleNeighborhoodBaseFiberIso Y ξ).hom.app U x) G.obj := by
  erw [← GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_assoc]
  exact comapGerm_fullSmallEtaleExtendBaseSheafFiberIso_hom Y ξ G U x

/-- The inverse native base-stalk comparison has its original scheme-map representative,
including the actual extension unit. -/
@[reassoc]
theorem nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber ((toSmallEtale S).obj U)
        (etaleNeighborhoodMapLift Y ξ U A f) G.obj ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app G =
    ((etaleExtendRestrictAdjunction (SmoothSite.base S)).unit.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G)).hom.app (op U) ≫
      ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj.map f.op ≫
        SmoothSite.toEtaleNeighborhoodValue Y ξ A
          ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj := by
  apply (cancel_mono ((fullSmallEtaleExtendBaseSheafFiberIso Y ξ).hom.app G)).mp
  simp only [fullSmallEtaleExtendNativeBaseSheafFiberIso, Iso.trans_inv,
    NatTrans.comp_app, Iso.symm_inv, NatIso.ofComponents_hom_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [← SmoothSite.toPresheafFiber_fiberMk_assoc,
    unit_germ_fullSmallEtaleExtendBaseSheafFiberIso_hom,
    toPresheafFiber_nativeBaseGeometricStalkIso_hom]
  congr 1
  exact (etaleNeighborhoodGermToLift_fiberMk Y ξ U A f).symm

/-- The basis unit followed by the actual full-small counit is the inverse dense-basis unit. -/
@[reassoc]
theorem etaleUnit_fullSmallCounit
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (etaleExtendRestrictAdjunction (SmoothSite.base S)).unit.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj
          ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F)) ≫
      (etaleRestrict (SmoothSite.base S)).map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F) =
    ((sheafEquivSmallEtale (SmoothSite.base S)).unitIso.app
      ((etaleRestrict (SmoothSite.base S)).obj F)).inv := by
  rw [fullSmallEtaleAdjunction_counit_app, Functor.map_comp]
  erw [← (etaleExtendRestrictAdjunction (SmoothSite.base S)).unit.naturality_assoc]
  erw [(etaleExtendRestrictAdjunction (SmoothSite.base S)).right_triangle_components,
    Category.comp_id]
  rfl

/-- With the actual native base-stalk source comparison, the canonical counit sends each
original marked representative to its original presheaf restriction. -/
@[reassoc]
theorem nativeBaseGerm_fullSmallEtale_counit
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})
    (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (((sheafEquivSmallEtale (SmoothSite.base S)).unitIso.app
        ((etaleRestrict (SmoothSite.base S)).obj F)).hom.hom.app (op U)) ≫
      (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber ((toSmallEtale S).obj U)
        (etaleNeighborhoodMapLift Y ξ U A f)
          ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F).obj ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom =
    F.obj.map f.op ≫ SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj := by
  erw [nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_assoc]
  rw [SmoothSite.toEtaleNeighborhoodValue_naturality]
  rw [← Category.assoc (((fullSmallEtaleExtend (SmoothSite.base S)).obj
    ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F)).obj.map f.op),
    NatTrans.naturality]
  have h := congrArg (fun q ↦ q.hom.app (op U)) (etaleUnit_fullSmallCounit (S := S) F)
  change _ ≫ _ = _ at h
  simp only [Category.assoc]
  erw [reassoc_of% h]
  rw [← Category.assoc]
  simp only [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- Under the actual native base-stalk source comparison, the canonical full-small counit
is precisely the original structural pullback of marked affine neighborhood values. -/
@[colib_tag "COL-1108", reassoc,
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/CategoryTheory/Sites/Point/Comap.lean:63-73"
    "ingredient" "Native comapped-point fiber comparison; counit-map assembly is proved here",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/CategoryTheory/Adjunction/Mates.lean:306-310"
    "ingredient" "The native inverse mate preserves the actual adjunction unit"]
theorem fullSmallEtale_counit_eq_structuralNeighborhoodPullback
    [IsAffine Y.left] (p : Y ⟶ SmoothSite.base S)
    (h : ξ ≫ p.left = ξ ≫ Y.hom)
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleRestrictNeighborhoodIso (SmoothSite.base S) (ξ ≫ Y.hom) F).hom ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom =
    SmoothSite.etaleNeighborhoodValuePullback p h F.obj := by
  apply (SmoothSite.etaleNeighborhoodValueIsColimit (SmoothSite.base S)
    (ξ ≫ Y.hom) F.obj).hom_ext
  intro B
  change SmoothSite.toEtaleNeighborhoodValue (SmoothSite.base S) (ξ ≫ Y.hom)
    B.unop F.obj ≫ _ = SmoothSite.toEtaleNeighborhoodValue (SmoothSite.base S)
      (ξ ≫ Y.hom) B.unop F.obj ≫ _
  rw [toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom_assoc]
  let U := (affineEtaleToSeparatedFiniteType (SmoothSite.base S)).obj B.unop.obj
  let A := SmoothSite.etaleNeighborhoodPullback p h B.unop
  let f := SmoothSite.etaleNeighborhoodPullbackHom p h B.unop
  have hm : etaleNeighborhoodMapLift Y ξ U A f = B.unop.val := by
    apply Over.OverMorphism.ext
    exact SmoothSite.etaleNeighborhoodPullbackMark_hom p h B.unop
  have hg := nativeBaseGerm_fullSmallEtale_counit Y ξ F U A f
  rw [hm] at hg
  exact hg.trans (SmoothSite.toEtaleNeighborhoodValue_pullback p h F.obj B.unop).symm

/-- At an affine marked smooth object, counit invertibility is exactly invertibility of
COL-1093's original structural pullback, with the already proved native source comparison. -/
@[colib_tag "COL-1108"]
theorem isIso_fullSmallEtale_counit_iff_structuralNeighborhoodPullback
    [IsAffine Y.left] (p : Y ⟶ SmoothSite.base S)
    (h : ξ ≫ p.left = ξ ≫ Y.hom)
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom) ↔
    IsIso (SmoothSite.etaleNeighborhoodValuePullback p h F.obj) := by
  rw [← fullSmallEtale_counit_eq_structuralNeighborhoodPullback Y ξ p h F,
    isIso_comp_left_iff, isIso_comp_left_iff]

/-- The same canonical counit is the restriction of the original presheaf itself after
removing its actual sheafification units at the two original marked neighborhood values. -/
@[colib_tag "COL-1108", reassoc]
theorem fullSmallEtale_counit_sheafification_eq_structuralNeighborhoodPullback
    [IsAffine Y.left] (p : Y ⟶ SmoothSite.base S)
    (h : ξ ≫ p.left = ξ ≫ Y.hom)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}).obj P
    (SmoothSite.etaleNeighborhoodSheafificationIso (SmoothSite.base S) (ξ ≫ Y.hom) P).hom ≫
      (fullSmallEtaleRestrictNeighborhoodIso (SmoothSite.base S) (ξ ≫ Y.hom) F).hom ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom ≫
      (SmoothSite.etaleNeighborhoodSheafificationIso Y ξ P).inv =
    SmoothSite.etaleNeighborhoodValuePullback p h P := by
  dsimp only
  erw [fullSmallEtale_counit_eq_structuralNeighborhoodPullback_assoc]
  rw [SmoothSite.etaleNeighborhoodSheafificationIso_hom_pullback_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The genuine canonical counit criterion uses the original presheaf restriction, not
an assumption of rigidity or an independently supplied isomorphism of its sheafification. -/
@[colib_tag "COL-1108"]
theorem isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
    [IsAffine Y.left] (p : Y ⟶ SmoothSite.base S)
    (h : ξ ≫ p.left = ξ ≫ Y.hom)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}).obj P
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom) ↔
    IsIso (SmoothSite.etaleNeighborhoodValuePullback p h P) := by
  dsimp only
  rw [← fullSmallEtale_counit_sheafification_eq_structuralNeighborhoodPullback Y ξ p h P,
    isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- Original affine marked base germs jointly determine every morphism from the native stalk. -/
theorem nativeBaseStalk_hom_ext
    (β : Spec (.of Ω) ⟶ S) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    {M : AddCommGrpCat.{u + 1}}
    {a b : (pointSmallEtale β).sheafFiber.obj G ⟶ M}
    (h : ∀ B : SmoothSite.EtaleNeighborhood (SmoothSite.base S) β,
      (pointSmallEtale β).toPresheafFiber
        ((AffineEtale.Spec S).obj B.obj) B.val G.obj ≫ a =
      (pointSmallEtale β).toPresheafFiber
        ((AffineEtale.Spec S).obj B.obj) B.val G.obj ≫ b) : a = b := by
  have hc := (Functor.Final.isColimitWhiskerEquiv
    (affineNeighborhoodToSmallPoint (SmoothSite.base S) β).op
      ((pointSmallEtale β).presheafFiberCocone G.obj)).2
        ((pointSmallEtale β).isColimitPresheafFiberCocone G.obj)
  apply hc.hom_ext
  intro B
  exact h B.unop

omit [IsAffine S] in
/-- Equality of the base markings transports the very same native small-site germ. -/
@[reassoc]
theorem nativeBaseGerm_transport
    {α β : Spec (.of Ω) ⟶ S} (h : α = β)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : S.Etale)
    (a : (pointSmallEtale α).fiber.obj U) (b : (pointSmallEtale β).fiber.obj U)
    (hab : a.left = b.left) :
    (pointSmallEtale α).toPresheafFiber U a G.obj ≫
      eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj G) h) =
    (pointSmallEtale β).toPresheafFiber U b G.obj := by
  subst β
  have he : a = b := Over.OverMorphism.ext hab
  subst b
  simp

/-- The actual native source comparison is contravariantly natural under every original
marked morphism between affine smooth objects, in particular an original relative Frobenius. -/
@[colib_tag "COL-1108", reassoc]
theorem fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_marked_naturality
    [IsAffine Y.left] {X : SmoothSite S} [IsAffine X.left]
    (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left) (h : ζ ≫ f.left = ξ)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app G ≫
      SmoothSite.etaleNeighborhoodValuePullback f h
        ((fullSmallEtaleExtend (SmoothSite.base S)).obj G).obj =
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj G)
        (SmoothSite.markedSmooth_baseMarking_eq Y ξ f ζ h).symm) ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso X ζ).inv.app G := by
  apply nativeBaseStalk_hom_ext (S := S) (ξ ≫ Y.hom) G
  intro B
  let p : Y ⟶ SmoothSite.base S := SmoothSite.homMk Y.hom (by
    change Y.hom ≫ 𝟙 S = Y.hom
    exact Category.comp_id _)
  let U := (affineEtaleToSeparatedFiniteType (SmoothSite.base S)).obj B.obj
  let A := SmoothSite.etaleNeighborhoodPullback p (show ξ ≫ p.left = ξ ≫ Y.hom from rfl) B
  let g := SmoothSite.etaleNeighborhoodPullbackHom p
    (show ξ ≫ p.left = ξ ≫ Y.hom from rfl) B
  let A' := SmoothSite.etaleNeighborhoodPullback f h A
  let q := SmoothSite.etaleNeighborhoodPullbackHom f h A
  have hg : etaleNeighborhoodMapLift Y ξ U A g = B.val := by
    apply Over.OverMorphism.ext
    exact SmoothSite.etaleNeighborhoodPullbackMark_hom p rfl B
  have hq : B.val.left = (etaleNeighborhoodMapLift X ζ U A' (q ≫ g)).left := by
    change B.val.left = SmoothSite.etaleNeighborhoodMark X ζ A' ≫ (q.left ≫ g.left)
    rw [← Category.assoc, SmoothSite.etaleNeighborhoodPullbackMark_hom]
    exact (congrArg (fun z ↦ z.left) hg).symm
  have ht := nativeBaseGerm_transport
    (SmoothSite.markedSmooth_baseMarking_eq Y ξ f ζ h).symm G ((toSmallEtale S).obj U)
      B.val (etaleNeighborhoodMapLift X ζ U A' (q ≫ g)) hq
  erw [reassoc_of% ht]
  rw [← hg]
  erw [nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_assoc,
    nativeBaseGerm_fullSmallEtaleExtendNativeBaseSheafFiberIso_inv]
  rw [SmoothSite.toEtaleNeighborhoodValue_pullback]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rfl

/-- The actual canonical counit, normalized by the native base-stalk source comparison,
commutes with original marked affine smooth morphisms. The base-stalk arrow only transports
the proved equality of composite markings, and the target arrow is COL-1093's original pullback. -/
@[colib_tag "COL-1108", reassoc]
theorem fullSmallEtale_counit_nativeBase_marked_naturality
    [IsAffine Y.left] {X : SmoothSite S} [IsAffine X.left]
    (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left) (h : ζ ≫ f.left = ξ)
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleExtendNativeBaseSheafFiberIso Y ξ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom ≫
      SmoothSite.etaleNeighborhoodValuePullback f h F.obj =
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F))
        (SmoothSite.markedSmooth_baseMarking_eq Y ξ f ζ h).symm) ≫
      (fullSmallEtaleExtendNativeBaseSheafFiberIso X ζ).inv.app
        ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) ≫
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} X ζ).presheafFiber.map
        ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom := by
  have hn := SmoothSite.etaleNeighborhoodValuePullback_naturality f h
    ((fullSmallEtaleAdjunction (SmoothSite.base S)).counit.app F).hom
  erw [hn]
  exact fullSmallEtaleExtendNativeBaseSheafFiberIso_inv_marked_naturality_assoc Y ξ f ζ h
    ((fullSmallEtaleRestrict (SmoothSite.base S)).obj F) _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
