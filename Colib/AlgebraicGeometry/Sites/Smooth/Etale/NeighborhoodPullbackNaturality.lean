/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodBaseChange

/-!
# Original germs and naturality of neighborhood pullback

The actual pullback on marked affine neighborhood values commutes with the
original presheaf morphisms and sheafification units. Original scheme-map
representatives and compatible composite base markings are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {X Y : SmoothSite S} [IsAffine X.left] [IsAffine Y.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original structural pullback commutes with each original presheaf coefficient map. -/
@[reassoc]
theorem etaleNeighborhoodValuePullback_naturality
    (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    {F G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    (etaleNeighborhoodPoint.{u, u + 1} Y η).presheafFiber.map a ≫
      etaleNeighborhoodValuePullback f h G =
    etaleNeighborhoodValuePullback f h F ≫
      (etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map a := by
  apply (etaleNeighborhoodValueIsColimit Y η F).hom_ext
  intro B
  change toEtaleNeighborhoodValue Y η B.unop F ≫ _ =
    toEtaleNeighborhoodValue Y η B.unop F ≫ _
  rw [toEtaleNeighborhoodValue_naturality_assoc, toEtaleNeighborhoodValue_pullback,
    toEtaleNeighborhoodValue_pullback_assoc, toEtaleNeighborhoodValue_naturality]
  rw [← Category.assoc, ← Category.assoc, a.naturality]

/-- The actual sheafification unit commutes with the original marked structural pullback. -/
@[reassoc]
theorem etaleNeighborhoodSheafificationIso_hom_pullback
    (f : X ⟶ Y) (h : ξ ≫ f.left = η)
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleNeighborhoodSheafificationIso Y η P).hom ≫
      etaleNeighborhoodValuePullback f h (sheafify (etaleTopology S) P) =
    etaleNeighborhoodValuePullback f h P ≫
      (etaleNeighborhoodSheafificationIso X ξ P).hom :=
  etaleNeighborhoodValuePullback_naturality f h (toSheafify (etaleTopology S) P)

variable (Y) (η)

local instance : InitiallySmall.{u + 1} (EtaleNeighborhood Y η) :=
  etaleNeighborhoodInitiallySmall.{u, u + 1} Y η

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [IsAffine Y.left] in
/-- A smooth-neighborhood point germ represented by an actual scheme map is its original
restriction followed by the original neighborhood germ. -/
@[reassoc]
theorem toPresheafFiber_fiberMk
    (H : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A : SmoothSite.EtaleNeighborhood Y η) (Z : SmoothSite S)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y η).obj A ⟶ Z) :
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y η).toPresheafFiber Z
      (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f) H =
    H.map f.op ≫ SmoothSite.toEtaleNeighborhoodValue Y η A H := by
  change _ = H.map f.op ≫
    (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y η).toPresheafFiber _
      (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} (𝟙 _)) H
  rw [GrothendieckTopology.Point.toPresheafFiber_w]
  congr 1
  exact (GrothendieckTopology.Point.ofIsCofiltered.fiber_map_fiberMk.{u + 1}
    (SmoothSite.etaleNeighborhoodToSmooth Y η) (𝟙 _) f).trans (by rw [Category.id_comp]) |>.symm



omit [QuasiSeparatedSpace S] [IsAffine Y.left] [IsSepClosed Ω] in
/-- A morphism of the original marked smooth schemes preserves the composite base marking. -/
theorem markedSmooth_baseMarking_eq
    {X : SmoothSite S} (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X.left)
    (h : ζ ≫ f.left = η) : ζ ≫ X.hom = η ≫ Y.hom := by
  rw [← MorphismProperty.Over.w f, ← Category.assoc, h]


end AlgebraicGeometry.Scheme.SmoothSite
