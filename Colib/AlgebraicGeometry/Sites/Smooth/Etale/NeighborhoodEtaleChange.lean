/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodBaseChange

/-!
# Étale changes of marked affine neighborhoods

For an étale morphism respecting the field-valued markings, the original contravariant
pullback on neighborhood values is an isomorphism. Its inverse composes the actual affine
neighborhoods with the given étale morphism. The structural map from the presheaf value on
the base is unchanged by this comparison. No rigidity or continuity statement is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {X Y : SmoothSite S}
  {Ω : Type u} [Field Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}

/-- Compose the actual affine neighborhood with an étale morphism of marked objects. -/
def etaleNeighborhoodComp (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    (A : EtaleNeighborhood X ξ) : EtaleNeighborhood Y η :=
  let : Etale A.obj.hom := A.obj.prop
  (etaleNeighborhoodFiber Y η).elementsMk
    (AffineEtale.mk (A.obj.hom ≫ f.left))
    (Over.homMk (etaleNeighborhoodMark X ξ A) (by
      change etaleNeighborhoodMark X ξ A ≫
        ((etaleNeighborhoodHom X ξ A).left ≫ f.left) = η
      rw [← Category.assoc, etaleNeighborhoodMark_hom, h]))

/-- Composition changes only the base presentation, not the underlying marked scheme. -/
def etaleNeighborhoodCompIso (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    (A : EtaleNeighborhood X ξ) :
    (etaleNeighborhoodToSmooth X ξ).obj A ≅
      (etaleNeighborhoodToSmooth Y η).obj (etaleNeighborhoodComp f h A) where
  hom := homMk (𝟙 _) (by
    change (𝟙 _) ≫ (((etaleNeighborhoodHom X ξ A).left ≫ f.left) ≫ Y.hom) =
      (etaleNeighborhoodHom X ξ A).left ≫ X.hom
    rw [Category.id_comp, Category.assoc, MorphismProperty.Over.w f])
  inv := homMk (𝟙 _) (by
    change (𝟙 _) ≫ ((etaleNeighborhoodHom X ξ A).left ≫ X.hom) =
      ((etaleNeighborhoodHom X ξ A).left ≫ f.left) ≫ Y.hom
    rw [Category.id_comp, Category.assoc, MorphismProperty.Over.w f])
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 (Spec A.obj.left.unop)) ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 (Spec A.obj.left.unop)) ≫ 𝟙 _ = 𝟙 _
    simp

@[reassoc (attr := simp)]
theorem etaleNeighborhoodCompIso_hom_hom (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (A : EtaleNeighborhood X ξ) :
    (etaleNeighborhoodCompIso f h A).hom.left ≫
        (etaleNeighborhoodHom Y η (etaleNeighborhoodComp f h A)).left =
      (etaleNeighborhoodHom X ξ A).left ≫ f.left :=
  Category.id_comp _

@[reassoc (attr := simp)]
theorem etaleNeighborhoodCompIso_mark_hom (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodMark X ξ A ≫ (etaleNeighborhoodCompIso f h A).hom.left =
      etaleNeighborhoodMark Y η (etaleNeighborhoodComp f h A) :=
  Category.comp_id _

/-- Composition of neighborhoods preserves every original neighborhood morphism. -/
def etaleNeighborhoodCompMap (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    {A B : EtaleNeighborhood X ξ} (g : A ⟶ B) :
    etaleNeighborhoodComp f h A ⟶ etaleNeighborhoodComp f h B :=
  etaleNeighborhoodHomMk Y η ((etaleNeighborhoodToSmooth X ξ).map g).left
    (by
      change ((etaleNeighborhoodToSmooth X ξ).map g).left ≫
        ((etaleNeighborhoodHom X ξ B).left ≫ f.left) =
          (etaleNeighborhoodHom X ξ A).left ≫ f.left
      rw [← Category.assoc, etaleNeighborhoodMap_hom])
    (etaleNeighborhoodMark_map X ξ g)

@[reassoc (attr := simp)]
theorem etaleNeighborhoodCompMap_iso_inv (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) {A B : EtaleNeighborhood X ξ} (g : A ⟶ B) :
    (etaleNeighborhoodToSmooth Y η).map (etaleNeighborhoodCompMap f h g) ≫
        (etaleNeighborhoodCompIso f h B).inv =
      (etaleNeighborhoodCompIso f h A).inv ≫ (etaleNeighborhoodToSmooth X ξ).map g := by
  apply MorphismProperty.Over.Hom.ext
  change ((etaleNeighborhoodToSmooth Y η).map (etaleNeighborhoodCompMap f h g)).left ≫
      (𝟙 (Spec B.obj.left.unop)) =
        (𝟙 (Spec A.obj.left.unop)) ≫ ((etaleNeighborhoodToSmooth X ξ).map g).left
  exact (Category.comp_id _).trans
    ((etaleNeighborhoodHomMk_map_left Y η _ _ _).trans (Category.id_comp _).symm)

variable [IsSepClosed Ω]

/-- The inverse cocone uses exactly the original affine scheme with its composed structure map. -/
def etaleNeighborhoodCompCocone (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Cocone ((etaleNeighborhoodToSmooth X ξ).op ⋙ F) where
  pt := etaleNeighborhoodValue Y η F
  ι :=
    { app := fun A ↦ F.map (etaleNeighborhoodCompIso f h A.unop).inv.op ≫
        toEtaleNeighborhoodValue Y η (etaleNeighborhoodComp f h A.unop) F
      naturality := by
        intro A B g
        dsimp
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp, ← op_comp,
          ← etaleNeighborhoodCompMap_iso_inv, op_comp, F.map_comp, Category.assoc,
          toEtaleNeighborhoodValue_w] }

/-- The covariant inverse to étale pullback, obtained by composing original neighborhoods. -/
def etaleNeighborhoodValueComp (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValue X ξ F ⟶ etaleNeighborhoodValue Y η F :=
  (etaleNeighborhoodValueIsColimit X ξ F).desc (etaleNeighborhoodCompCocone f h F)

@[reassoc (attr := simp)]
theorem toEtaleNeighborhoodValue_comp (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : EtaleNeighborhood X ξ) :
    toEtaleNeighborhoodValue X ξ A F ≫ etaleNeighborhoodValueComp f h F =
      F.map (etaleNeighborhoodCompIso f h A).inv.op ≫
        toEtaleNeighborhoodValue Y η (etaleNeighborhoodComp f h A) F :=
  (etaleNeighborhoodValueIsColimit X ξ F).fac (etaleNeighborhoodCompCocone f h F) (op A)

variable [IsAffine X.left] [IsAffine Y.left]

/-- Composing a neighborhood and pulling it back restores its original representative. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodValueComp_pullback (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValueComp f h F ≫ etaleNeighborhoodValuePullback f h F = 𝟙 _ := by
  apply (etaleNeighborhoodValueIsColimit X ξ F).hom_ext
  intro A
  change toEtaleNeighborhoodValue X ξ A.unop F ≫ _ =
    toEtaleNeighborhoodValue X ξ A.unop F ≫ 𝟙 _
  rw [toEtaleNeighborhoodValue_comp_assoc,
    toEtaleNeighborhoodValue_pullback_of_compatible f h F A.unop
      (etaleNeighborhoodComp f h A.unop) (etaleNeighborhoodCompIso f h A.unop).hom
      (etaleNeighborhoodCompIso_hom_hom f h A.unop)
      (etaleNeighborhoodCompIso_mark_hom f h A.unop)]
  simp only [← Category.assoc, ← F.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
    F.map_id, Category.id_comp, Category.comp_id]

/-- The actual projection is a morphism from the composed pullback neighborhood to the original. -/
def etaleNeighborhoodCompPullbackHom (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η) :
    etaleNeighborhoodComp f h (etaleNeighborhoodPullback f h B) ⟶ B :=
  etaleNeighborhoodHomMk Y η (etaleNeighborhoodPullbackHom f h B).left
    (etaleNeighborhoodPullbackHom_hom f h B) (etaleNeighborhoodPullbackMark_hom f h B)

omit [IsSepClosed Ω] in
@[reassoc]
theorem etaleNeighborhoodCompPullbackHom_map (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (B : EtaleNeighborhood Y η) :
    (etaleNeighborhoodToSmooth Y η).map (etaleNeighborhoodCompPullbackHom f h B) =
      (etaleNeighborhoodCompIso f h (etaleNeighborhoodPullback f h B)).inv ≫
        etaleNeighborhoodPullbackHom f h B := by
  apply MorphismProperty.Over.Hom.ext
  exact (etaleNeighborhoodHomMk_map_left Y η _ _ _).trans (Category.id_comp _).symm

/-- Pulling back and composing restores each original neighborhood representative. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodValuePullback_valueComp (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValuePullback f h F ≫ etaleNeighborhoodValueComp f h F = 𝟙 _ := by
  apply (etaleNeighborhoodValueIsColimit Y η F).hom_ext
  intro B
  change toEtaleNeighborhoodValue Y η B.unop F ≫ _ =
    toEtaleNeighborhoodValue Y η B.unop F ≫ 𝟙 _
  rw [toEtaleNeighborhoodValue_pullback_assoc, toEtaleNeighborhoodValue_comp,
    ← Category.assoc, ← F.map_comp, ← op_comp,
    ← etaleNeighborhoodCompPullbackHom_map, toEtaleNeighborhoodValue_w, Category.comp_id]

/-- The canonical étale change has exactly the original contravariant pullback as its hom. -/
@[colib_tag "COL-1102", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/Point/OfIsCofiltered.lean:176-187"
  "ingredient" "Actual cofiltered neighborhood presheaf-fibre colimit; the marked pullback and \
    etale-change maps are constructed here."]
def etaleNeighborhoodValueEtaleIso (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValue Y η F ≅ etaleNeighborhoodValue X ξ F where
  hom := etaleNeighborhoodValuePullback f h F
  inv := etaleNeighborhoodValueComp f h F
  hom_inv_id := etaleNeighborhoodValuePullback_valueComp f h F
  inv_hom_id := etaleNeighborhoodValueComp_pullback f h F

/-- The canonical affine presentation of the marked object itself. -/
def etaleNeighborhoodSelf (X : SmoothSite S) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) : EtaleNeighborhood X ξ :=
  (etaleNeighborhoodFiber X ξ).elementsMk (AffineEtale.mk X.left.isoSpec.inv)
    (Over.homMk (ξ ≫ X.left.isoSpec.hom) (by
      change (ξ ≫ X.left.isoSpec.hom) ≫ X.left.isoSpec.inv = ξ
      simp))

/-- Every original neighborhood maps to the canonical affine presentation of the base object. -/
def etaleNeighborhoodToSelf (A : EtaleNeighborhood X ξ) :
    A ⟶ etaleNeighborhoodSelf X ξ :=
  etaleNeighborhoodHomMk X ξ
    ((etaleNeighborhoodHom X ξ A).left ≫ X.left.isoSpec.hom)
    (by change (_ ≫ X.left.isoSpec.hom) ≫ X.left.isoSpec.inv = _; simp)
    (by
      change etaleNeighborhoodMark X ξ A ≫
        ((etaleNeighborhoodHom X ξ A).left ≫ X.left.isoSpec.hom) = ξ ≫ X.left.isoSpec.hom
      rw [← Category.assoc, etaleNeighborhoodMark_hom])

omit [IsSepClosed Ω] [IsAffine Y.left] in
@[reassoc (attr := simp)]
theorem etaleNeighborhoodToSelf_hom (A : EtaleNeighborhood X ξ) :
    (etaleNeighborhoodToSmooth X ξ).map (etaleNeighborhoodToSelf A) ≫
        etaleNeighborhoodHom X ξ (etaleNeighborhoodSelf X ξ) =
      etaleNeighborhoodHom X ξ A := by
  apply MorphismProperty.Over.Hom.ext
  exact etaleNeighborhoodMap_hom X ξ (etaleNeighborhoodToSelf A)

/-- Evaluation into the original neighborhood value from the actual affine smooth object. -/
def toEtaleNeighborhoodValueFromObject (X : SmoothSite S) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op X) ⟶ etaleNeighborhoodValue X ξ F :=
  F.map (etaleNeighborhoodHom X ξ (etaleNeighborhoodSelf X ξ)).op ≫
    toEtaleNeighborhoodValue X ξ (etaleNeighborhoodSelf X ξ) F

omit [IsAffine Y.left] in
/-- Evaluation can be computed on every original neighborhood using its actual structure map. -/
theorem toEtaleNeighborhoodValueFromObject_eq
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A : EtaleNeighborhood X ξ) :
    toEtaleNeighborhoodValueFromObject X ξ F =
      F.map (etaleNeighborhoodHom X ξ A).op ≫ toEtaleNeighborhoodValue X ξ A F := by
  unfold toEtaleNeighborhoodValueFromObject
  rw [← toEtaleNeighborhoodValue_w X ξ (etaleNeighborhoodToSelf A), ← Category.assoc,
    ← F.map_comp, ← op_comp, etaleNeighborhoodToSelf_hom]

/-- Evaluation commutes with the original contravariant neighborhood pullback. -/
@[colib_tag "COL-1102", reassoc]
theorem toEtaleNeighborhoodValueFromObject_pullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    toEtaleNeighborhoodValueFromObject Y η F ≫ etaleNeighborhoodValuePullback f h F =
      F.map f.op ≫ toEtaleNeighborhoodValueFromObject X ξ F := by
  let B := etaleNeighborhoodSelf Y η
  let A := etaleNeighborhoodPullback f h B
  have hg : etaleNeighborhoodPullbackHom f h B ≫ etaleNeighborhoodHom Y η B =
      etaleNeighborhoodHom X ξ A ≫ f := by
    apply MorphismProperty.Over.Hom.ext
    exact etaleNeighborhoodPullbackHom_hom f h B
  rw [toEtaleNeighborhoodValueFromObject_eq F B,
    toEtaleNeighborhoodValueFromObject_eq F A, Category.assoc,
    toEtaleNeighborhoodValue_pullback, ← Category.assoc, ← F.map_comp, ← op_comp,
    hg, op_comp, F.map_comp, Category.assoc]

/-- The original presheaf value on the base maps to the original marked neighborhood value. -/
@[colib_tag "COL-1102"]
def etaleNeighborhoodBaseValueMap (X : SmoothSite S) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op (base S)) ⟶ etaleNeighborhoodValue X ξ F :=
  F.map (homMk X.hom (by change X.hom ≫ 𝟙 S = X.hom; simp) : X ⟶ base S).op ≫
    toEtaleNeighborhoodValueFromObject X ξ F

omit [IsAffine Y.left] in
/-- The structural map is represented by the original neighborhood's map to the base. -/
theorem etaleNeighborhoodBaseValueMap_eq
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodBaseValueMap X ξ F =
      F.map (homMk ((etaleNeighborhoodToSmooth X ξ).obj A).hom
        (by change _ ≫ 𝟙 S = _; simp) :
          (etaleNeighborhoodToSmooth X ξ).obj A ⟶ base S).op ≫
        toEtaleNeighborhoodValue X ξ A F := by
  unfold etaleNeighborhoodBaseValueMap
  rw [toEtaleNeighborhoodValueFromObject_eq F A, ← Category.assoc,
    ← F.map_comp, ← op_comp]
  rfl

/-- Changing the marked affine chart preserves the map from the same presheaf value on the base. -/
@[colib_tag "COL-1102", reassoc (attr := simp)]
theorem etaleNeighborhoodBaseValueMap_pullback (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodBaseValueMap Y η F ≫ etaleNeighborhoodValuePullback f h F =
      etaleNeighborhoodBaseValueMap X ξ F := by
  unfold etaleNeighborhoodBaseValueMap
  rw [Category.assoc, toEtaleNeighborhoodValueFromObject_pullback,
    ← Category.assoc, ← F.map_comp, ← op_comp]
  congr 2
  apply congrArg Quiver.Hom.op
  apply MorphismProperty.Over.Hom.ext
  exact MorphismProperty.Over.w f

/-- The chart isomorphism preserves the structural map from the original base value. -/
@[colib_tag "COL-1102", reassoc (attr := simp)]
theorem etaleNeighborhoodBaseValueMap_etaleIso_hom (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodBaseValueMap Y η F ≫ (etaleNeighborhoodValueEtaleIso f h F).hom =
      etaleNeighborhoodBaseValueMap X ξ F :=
  etaleNeighborhoodBaseValueMap_pullback f h F

/-- The explicit inverse also preserves the same structural map from the base value. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodBaseValueMap_etaleIso_inv (f : X ⟶ Y) [Etale f.left]
    (h : ξ ≫ f.left = η) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodBaseValueMap X ξ F ≫ (etaleNeighborhoodValueEtaleIso f h F).inv =
      etaleNeighborhoodBaseValueMap Y η F := by
  rw [← etaleNeighborhoodBaseValueMap_etaleIso_hom f h F,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.SmoothSite
