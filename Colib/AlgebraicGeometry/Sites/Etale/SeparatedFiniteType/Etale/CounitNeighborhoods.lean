/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Adjunction
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ClosedPoints

/-!
# The canonical small/smooth counit on actual neighborhood values

The full-small/smooth counit is compared with the unsheafified Kan counit,
retaining the specified adjunction and the actual sheafification unit. Its
representatives are the original presheaf restriction maps along actual scheme
morphisms. The neighborhood value at a marking of `Y` is also identified with
the native small-site stalk of the actual restriction to `Y`, including both
the representative maps and naturality in coefficients.

The native small point in this comparison is on `Y`, not on the base `S`.
The further identification of the source with a stalk over the base, and the
rigidity assertion for homotopy-invariant torsion presheaves with transfers,
are not supplied here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S : Scheme.{u}} [IsAffine S] (X Y : SmoothSite S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ Y.left)

/-- The original presheaf left Kan extension of the literal restriction. -/
abbrev etaleRestrictLan (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :=
  (toSmoothSite X).op.lan.obj ((toSmoothSite X).op ⋙ F.obj)

/-- The canonical extension fiber, expressed using the actual sheafification unit. -/
def etaleExtendNeighborhoodIso
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y ξ ((etaleExtend X).obj ((etaleRestrict X).obj F)).obj ≅
      SmoothSite.etaleNeighborhoodValue Y ξ (etaleRestrictLan X F) :=
  (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.mapIso
    ((sheafToPresheaf _ _).mapIso ((etaleExtendConstructionIso X).app
      ((etaleRestrict X).obj F))) ≪≫
    (SmoothSite.etaleNeighborhoodSheafificationIso Y ξ (etaleRestrictLan X F)).symm

/-- The full-small extension fiber includes the actual dense-basis equivalence counit. -/
def fullSmallEtaleExtendNeighborhoodIso
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y ξ
        ((fullSmallEtaleExtend X).obj ((fullSmallEtaleRestrict X).obj F)).obj ≅
      SmoothSite.etaleNeighborhoodValue Y ξ (etaleRestrictLan X F) :=
  (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.mapIso
    ((sheafToPresheaf _ _).mapIso ((etaleExtend X).mapIso
      ((sheafEquivSmallEtale X).unitIso.symm.app ((etaleRestrict X).obj F)))) ≪≫
    etaleExtendNeighborhoodIso X Y ξ F

/-- Before sheafification the constructed counit is exactly the original Kan counit. -/
@[reassoc]
theorem toSheafify_etaleConstructedAdjunction_counit
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    toSheafify (SmoothSite.etaleTopology S) (etaleRestrictLan X F) ≫
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (toSmoothSite X) AddCommGrpCat.{u + 1}
        (etaleTopology X.left) (SmoothSite.etaleTopology S)).counit.app F).hom =
      ((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj := by
  rw [etaleConstructedAdjunction_counit_app_hom]
  simp only [sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
  exact Category.comp_id _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves the chosen basis counit, not merely its source and target. -/
@[reassoc]
theorem etaleExtendNeighborhoodIso_hom_counit
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (etaleExtendNeighborhoodIso X Y ξ F).hom ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj) =
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((etaleExtendRestrictAdjunction X).counit.app F).hom := by
  rw [← etaleExtendConstructionIso_counit_app X F]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  dsimp only [etaleExtendNeighborhoodIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc]
  congr 1
  apply (cancel_epi (SmoothSite.etaleNeighborhoodSheafificationIso Y ξ
    (etaleRestrictLan X F)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  change _ = (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
    (toSheafify _ _) ≫ _
  rw [← Functor.map_comp, toSheafify_etaleConstructedAdjunction_counit]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full-small canonical counit has exactly the same original restriction map on fibers. -/
@[colib_tag "COL-1099", reassoc]
theorem fullSmallEtaleExtendNeighborhoodIso_hom_counit
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (fullSmallEtaleExtendNeighborhoodIso X Y ξ F).hom ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj) =
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
        ((fullSmallEtaleAdjunction X).counit.app F).hom := by
  rw [fullSmallEtaleAdjunction_counit_app]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  dsimp only [fullSmallEtaleExtendNeighborhoodIso, Iso.trans_hom]
  rw [Category.assoc, etaleExtendNeighborhoodIso_hom_counit]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On an original map from an affine neighborhood into an actual small-basis object,
the unsheafified counit is precisely the presheaf's restriction along that map. -/
@[reassoc]
theorem etaleRestrictLan_counit_representative
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})
    (A : SmoothSite.EtaleNeighborhood Y ξ) (U : EtaleSeparatedFiniteType X.left)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶ (toSmoothSite X).obj U) :
    ((toSmoothSite X).op.lanUnit.app ((toSmoothSite X).op ⋙ F.obj)).app (op U) ≫
        (etaleRestrictLan X F).map f.op ≫
        SmoothSite.toEtaleNeighborhoodValue Y ξ A (etaleRestrictLan X F) ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj) =
      F.obj.map f.op ≫ SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj := by
  rw [SmoothSite.toEtaleNeighborhoodValue_naturality]
  rw [← Category.assoc ((etaleRestrictLan X F).map f.op),
    NatTrans.naturality, ← Category.assoc,
    ← Category.assoc]
  erw [(toSmoothSite X).op.lanUnit_app_app_lanAdjunction_counit_app_app F.obj (op U)]
  simp only [Category.id_comp]
  rfl

/-- Only the explicit original Kan restriction map remains after removing the two canonical
isomorphisms; no rigidity or isomorphism of that map is assumed. -/
theorem isIso_fullSmallEtale_counit_neighborhood_iff
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction X).counit.app F).hom) ↔
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj)) := by
  rw [← fullSmallEtaleExtendNeighborhoodIso_hom_counit]
  exact isIso_comp_left_iff _ _

/-- Over a Jacobson affine base the canonical counit is tested only at the native closed
residue-geometric markings, on the explicit original restriction maps above. -/
@[colib_tag "COL-1099"]
theorem isIso_fullSmallEtale_counit_iff_closedNeighborhood_restriction
    [JacobsonSpace S] (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((fullSmallEtaleAdjunction X).counit.app F) ↔
      ∀ (Y : SmoothSite S) (y : Y.left), IsClosed ({y} : Set Y.left) →
        IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y
          (GeometricPoint.ofPoint Y.left y).hom).presheafFiber.map
            (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj)) := by
  rw [SmoothSite.isIso_iff_closedResidueGeometricNeighborhoodValue]
  exact forall_congr' fun Y ↦ forall_congr' fun y ↦
    imp_congr_right fun _ ↦ isIso_fullSmallEtale_counit_neighborhood_iff X Y _ F

/-- The actual affine marked neighborhoods included into the native small-site point's
category of elements. -/
abbrev affineNeighborhoodToSmallPoint :
    SmoothSite.EtaleNeighborhood Y ξ ⥤ (pointSmallEtale ξ).fiber.Elements :=
  Functor.Elements.precomp (AffineEtale.Spec Y.left) (pointSmallEtale ξ).fiber

private def affineNeighborhoodToSmallPointFullyFaithful :
    (affineNeighborhoodToSmallPoint Y ξ).FullyFaithful where
  preimage f := Functor.Elements.homMk ((AffineEtale.Spec Y.left).preimage f.hom) (by
    change (pointSmallEtale ξ).fiber.map
      ((AffineEtale.Spec Y.left).map ((AffineEtale.Spec Y.left).preimage f.hom)) _ = _
    rw [Functor.map_preimage]
    exact f.map_val)
  map_preimage f := by
    apply Functor.Elements.hom_ext
    exact (AffineEtale.Spec Y.left).map_preimage f.hom
  preimage_map f := Functor.Elements.hom_ext (Functor.preimage_map f.hom)

/-- Affine marked neighborhoods are initial in the native full small-site point.
The refinement retains both the scheme map and the chosen geometric marking. -/
instance affineNeighborhoodToSmallPoint_initial :
    (affineNeighborhoodToSmallPoint Y ξ).Initial := by
  let h := affineNeighborhoodToSmallPointFullyFaithful Y ξ
  let : (affineNeighborhoodToSmallPoint Y ξ).Full := h.full
  let : (affineNeighborhoodToSmallPoint Y ξ).Faithful := h.faithful
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro A
  let : Etale A.obj.hom := A.obj.prop
  obtain ⟨B, g, hg, hm⟩ := SmoothSite.exists_etaleNeighborhood_refinement Y ξ
    A.obj.hom A.val.left (Over.w A.val)
  refine ⟨B, ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk g hg) ?_⟩⟩
  exact Over.OverMorphism.ext hm

/-- The dense-basis unit identifies the original neighborhood diagram with the literal
restriction of the actual full-small coefficient sheaf. -/
def fullSmallEtaleRestrictNeighborhoodDiagramIso
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    (SmoothSite.etaleNeighborhoodToSmooth Y ξ).op ⋙ F.obj ≅
      (affineNeighborhoodToSmallPoint Y ξ).op ⋙
        (Functor.Elements.π (pointSmallEtale ξ).fiber).op ⋙
          ((fullSmallEtaleRestrict Y).obj F).obj :=
  NatIso.ofComponents (fun A ↦
    (((sheafToPresheaf (etaleTopology Y.left) AddCommGrpCat.{u + 1}).mapIso
      ((sheafEquivSmallEtale Y).unitIso.app ((etaleRestrict Y).obj F))).app
        (op ((affineEtaleToSeparatedFiniteType Y).obj A.unop.obj)))) (by
        intro A B f
        exact (((sheafEquivSmallEtale Y).unitIso.app ((etaleRestrict Y).obj F)).hom.hom.naturality
          (((affineEtaleToSeparatedFiniteType Y).map f.unop.hom).op)))

/-- The original smooth neighborhood value is the native full-small stalk of the actual
restriction sheaf. In particular `ξ` can be the native algebraic closure of a residue point. -/
@[colib_tag "COL-1099", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:60-91"
  "ingredient" "Native full-small geometric point, with its original marked lifts"]
def fullSmallEtaleRestrictNeighborhoodIso
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    SmoothSite.etaleNeighborhoodValue Y ξ F.obj ≅
      (pointSmallEtale ξ).sheafFiber.obj ((fullSmallEtaleRestrict Y).obj F) := by
  let := SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ
  exact (SmoothSite.etaleNeighborhoodColimitIso Y ξ F.obj).symm ≪≫
    HasColimit.isoOfNatIso (fullSmallEtaleRestrictNeighborhoodDiagramIso Y ξ F) ≪≫
      Functor.Final.colimitIso (affineNeighborhoodToSmallPoint Y ξ).op
        ((Functor.Elements.π (pointSmallEtale ξ).fiber).op ⋙
          ((fullSmallEtaleRestrict Y).obj F).obj)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison sends an original affine representative to the native small-site germ,
using precisely the unit of the existing dense-basis equivalence. -/
@[reassoc]
theorem toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})
    (A : SmoothSite.EtaleNeighborhood Y ξ) :
    SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj ≫
        (fullSmallEtaleRestrictNeighborhoodIso Y ξ F).hom =
      (((sheafEquivSmallEtale Y).unitIso.app ((etaleRestrict Y).obj F)).hom.hom.app
        (op ((affineEtaleToSeparatedFiniteType Y).obj A.obj))) ≫
        (pointSmallEtale ξ).toPresheafFiber ((AffineEtale.Spec Y.left).obj A.obj) A.val
          ((fullSmallEtaleRestrict Y).obj F).obj := by
  let := SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ
  rw [← SmoothSite.colimit_ι_etaleNeighborhoodColimitIso_hom Y ξ F.obj A]
  simp only [fullSmallEtaleRestrictNeighborhoodIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, HasColimit.ι_isoOfNatIso_hom_assoc,
    Functor.Final.ι_colimitIso_hom]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native small-site stalk comparison retains the actual coefficient morphisms. -/
@[reassoc]
theorem fullSmallEtaleRestrictNeighborhoodIso_naturality
    {F G : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map f.hom ≫
        (fullSmallEtaleRestrictNeighborhoodIso Y ξ G).hom =
      (fullSmallEtaleRestrictNeighborhoodIso Y ξ F).hom ≫
        (pointSmallEtale ξ).sheafFiber.map ((fullSmallEtaleRestrict Y).map f) := by
  apply (SmoothSite.etaleNeighborhoodValueIsColimit Y ξ F.obj).hom_ext
  intro A
  change SmoothSite.toEtaleNeighborhoodValue Y ξ A.unop F.obj ≫ _ =
    SmoothSite.toEtaleNeighborhoodValue Y ξ A.unop F.obj ≫ _
  rw [SmoothSite.toEtaleNeighborhoodValue_naturality_assoc,
    toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom,
    toEtaleNeighborhoodValue_fullSmallEtaleRestrictNeighborhoodIso_hom_assoc]
  change _ = (_ ≫ _) ≫ (pointSmallEtale ξ).presheafFiber.map _
  rw [Category.assoc, GrothendieckTopology.Point.toPresheafFiber_naturality,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact congrArg (fun k ↦ k.hom.app
    (op ((affineEtaleToSeparatedFiniteType Y).obj A.unop.obj)))
    ((sheafEquivSmallEtale Y).unitIso.hom.naturality ((etaleRestrict Y).map f))

/-- On every actual affine-neighborhood representative the canonical full-small counit
is the original restriction map, after its specified source comparison. -/
@[colib_tag "COL-1099", reassoc, colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Functor/KanExtension/Adjunction.lean:173-180"
  "ingredient" "The actual Kan counit composed with its unit is the identity on restriction"]
theorem fullSmallEtale_counit_representative
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})
    (A : SmoothSite.EtaleNeighborhood Y ξ) (U : EtaleSeparatedFiniteType X.left)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶ (toSmoothSite X).obj U) :
    ((toSmoothSite X).op.lanUnit.app ((toSmoothSite X).op ⋙ F.obj)).app (op U) ≫
        (etaleRestrictLan X F).map f.op ≫
        SmoothSite.toEtaleNeighborhoodValue Y ξ A (etaleRestrictLan X F) ≫
        (fullSmallEtaleExtendNeighborhoodIso X Y ξ F).inv ≫
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
          ((fullSmallEtaleAdjunction X).counit.app F).hom =
      F.obj.map f.op ≫ SmoothSite.toEtaleNeighborhoodValue Y ξ A F.obj := by
  rw [← fullSmallEtaleExtendNeighborhoodIso_hom_counit, Iso.inv_hom_id_assoc]
  exact etaleRestrictLan_counit_representative X Y ξ F A U f

/-- At the native small-site geometric point, the canonical counit restricted to `Y`
is invertible exactly when the original neighborhood restriction map is invertible. -/
@[colib_tag "COL-1099"]
theorem isIso_fullSmallEtale_counit_smallStalk_iff
    (F : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((pointSmallEtale ξ).sheafFiber.map
      ((fullSmallEtaleRestrict Y).map ((fullSmallEtaleAdjunction X).counit.app F))) ↔
    IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map
      (((toSmoothSite X).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app F.obj)) := by
  rw [← isIso_fullSmallEtale_counit_neighborhood_iff X Y ξ F]
  let f := (fullSmallEtaleAdjunction X).counit.app F
  have h := fullSmallEtaleRestrictNeighborhoodIso_naturality Y ξ f
  dsimp only [Functor.id_obj] at h
  constructor
  · intro hf
    have : IsIso ((fullSmallEtaleRestrictNeighborhoodIso Y ξ _).hom ≫
        (pointSmallEtale ξ).sheafFiber.map ((fullSmallEtaleRestrict Y).map f)) :=
      inferInstance
    rw [← h] at this
    exact (isIso_comp_right_iff _ _).mp this
  · intro hf
    have : IsIso ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).presheafFiber.map f.hom ≫
        (fullSmallEtaleRestrictNeighborhoodIso Y ξ F).hom) := inferInstance
    rw [h] at this
    exact (isIso_comp_left_iff _ _).mp this

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
