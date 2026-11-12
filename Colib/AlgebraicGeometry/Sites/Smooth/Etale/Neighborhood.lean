/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.FinallySmall

import Mathlib.CategoryTheory.Functor.TypeValuedFlat

/-!
# Affine étale neighborhoods of a field-valued point

The category of elements of the native affine étale lifting functor gives
actual affine neighborhoods of an arbitrary field-valued marking. It is
cofiltered and initially small. Over a quasi-separated base its forgetful
diagram takes values in the original smooth site, with the same scheme maps.

Adapted from Colib's smooth Nisnevich neighborhood construction, replacing
the residue-field arrow by an arbitrary field-valued arrow. The affine
refinement argument follows Mathlib's `pointSmallEtale`. No separable
closedness or étale point assertion is needed in this file.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (X : SmoothSite S) {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left)

/-- The functor of actual lifts of the field-valued arrow on the affine étale site. -/
abbrev etaleNeighborhoodFiber : X.left.AffineEtale ⥤ Type u :=
  AffineEtale.Spec X.left ⋙ Etale.forget X.left ⋙
    coyoneda.obj (op (Over.mk (ξ)))

/-- The category of affine étale neighborhoods of a field-valued point of a smooth object. -/
abbrev EtaleNeighborhood := (etaleNeighborhoodFiber X ξ).Elements

private abbrev fullEtaleNeighborhoodFiber : X.left.Etale ⥤ Type u :=
  Etale.forget X.left ⋙ coyoneda.obj (op (Over.mk (ξ)))

private abbrev affineNeighborhoodInclusion :
    EtaleNeighborhood X ξ ⥤ (fullEtaleNeighborhoodFiber X ξ).Elements :=
  Functor.Elements.precomp (AffineEtale.Spec X.left) (fullEtaleNeighborhoodFiber X ξ)

private def affineNeighborhoodInclusionFullyFaithful :
    (affineNeighborhoodInclusion X ξ).FullyFaithful where
  preimage f := Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage f.hom) (by
    change (fullEtaleNeighborhoodFiber X ξ).map
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom)) _ = _
    rw [Functor.map_preimage]
    exact f.map_val)
  map_preimage f := by
    apply Functor.Elements.hom_ext
    change (AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom) = f.hom
    exact (AffineEtale.Spec X.left).map_preimage f.hom
  preimage_map f := Functor.Elements.hom_ext (Functor.preimage_map f.hom)

private def affineNeighborhoodMk {R : CommRingCat.{u}} (f : Spec R ⟶ X.left) [Etale f]
    (l : Spec (.of Ω) ⟶ Spec R)
    (hl : l ≫ f = ξ) :
    EtaleNeighborhood X ξ :=
  (etaleNeighborhoodFiber X ξ).elementsMk (AffineEtale.mk f) (Over.homMk l hl)

private theorem exists_affine_residueLift {K : Type u} [Field K] {Y : Scheme.{u}}
    (l : Spec (.of K) ⟶ Y) :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ Y) (_ : IsOpenImmersion j)
      (l' : Spec (.of K) ⟶ Spec R), l' ≫ j = l := by
  obtain ⟨R, j, hj, hx, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := l default) (U := ⊤) (by simp)
  let : IsOpenImmersion j := hj
  have h : Set.range l ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    simpa only [Subsingleton.elim a default] using hx
  exact ⟨R, j, hj, IsOpenImmersion.lift j l h, IsOpenImmersion.lift_fac j l h⟩

private theorem exists_affineNeighborhood (A : (fullEtaleNeighborhoodFiber X ξ).Elements) :
    ∃ B : EtaleNeighborhood X ξ, Nonempty ((affineNeighborhoodInclusion X ξ).obj B ⟶ A) := by
  let f := A.obj.hom
  let : Etale f := A.obj.prop
  let l : Spec (.of Ω) ⟶ A.obj.left := A.val.left
  have hl : l ≫ f = ξ := Over.w A.val
  obtain ⟨R, j, hj, l', hl'⟩ := exists_affine_residueLift l
  let : IsOpenImmersion j := hj
  let B := affineNeighborhoodMk X ξ (j ≫ f) l' (by rw [← Category.assoc, hl', hl])
  refine ⟨B, ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk j rfl) ?_⟩⟩
  exact Over.OverMorphism.ext hl'

instance : IsCofiltered (EtaleNeighborhood X ξ) := by
  let F := affineNeighborhoodInclusion X ξ
  let h := affineNeighborhoodInclusionFullyFaithful X ξ
  let : F.Full := h.full
  let : F.Faithful := h.faithful
  let : IsCofiltered (fullEtaleNeighborhoodFiber X ξ).Elements :=
    Functor.isCofiltered_elements _
  exact IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F
    (exists_affineNeighborhood X ξ)

instance : InitiallySmall.{u} (EtaleNeighborhood X ξ) :=
  initiallySmall_of_essentiallySmall _

/-- The same neighborhoods have a small initial model in a larger universe. -/
theorem etaleNeighborhoodInitiallySmall :
    InitiallySmall.{max u w} (EtaleNeighborhood X ξ) := by
  let N := EtaleNeighborhood X ξ
  let E : InitialModel.{u} N ≌ AsSmall.{w} (InitialModel.{u} N) := AsSmall.equiv
  exact InitiallySmall.mk' (E.inverse ⋙ fromInitialModel.{u} N)

variable [QuasiSeparatedSpace S]

/-- The actual functor of neighborhoods into the smooth site over the base. -/
@[colib_tag "COL-1057"]
def etaleNeighborhoodToSmooth : EtaleNeighborhood X ξ ⥤ SmoothSite S :=
  let F := Functor.Elements.π (etaleNeighborhoodFiber X ξ) ⋙
    AffineEtale.Spec X.left ⋙ Etale.forget X.left ⋙ Over.map X.hom
  MorphismProperty.Comma.lift (P := smoothSeparatedFiniteType) F
    (fun A ↦ by
      change smoothSeparatedFiniteType (A.obj.hom ≫ X.hom)
      let : Etale A.obj.hom := A.obj.prop
      let : CompactSpace (Scheme.Spec.obj A.obj.left) :=
        inferInstanceAs (CompactSpace (Spec A.obj.left.unop))
      exact ⟨⟨inferInstance, inferInstance⟩,
        quasiCompact_of_compactSpace (Y := S) (A.obj.hom ≫ X.hom)⟩)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

instance (A : EtaleNeighborhood X ξ) :
    IsAffine ((etaleNeighborhoodToSmooth X ξ).obj A).left := by
  change IsAffine (Spec A.obj.left.unop)
  infer_instance

/-- The actual morphism from a neighborhood to the selected smooth object. -/
def etaleNeighborhoodHom (A : EtaleNeighborhood X ξ) :
    (etaleNeighborhoodToSmooth X ξ).obj A ⟶ X :=
  homMk A.obj.hom rfl

instance etaleNeighborhoodHom_etale (A : EtaleNeighborhood X ξ) :
    Etale (etaleNeighborhoodHom X ξ A).left :=
  A.obj.prop

/-- The actual field-valued marking of a neighborhood. -/
def etaleNeighborhoodMark (A : EtaleNeighborhood X ξ) :
    Spec (.of Ω) ⟶ ((etaleNeighborhoodToSmooth X ξ).obj A).left :=
  A.val.left

@[reassoc (attr := simp)]
theorem etaleNeighborhoodMark_hom (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodMark X ξ A ≫ (etaleNeighborhoodHom X ξ A).left =
      ξ :=
  Over.w A.val

@[reassoc (attr := simp)]
theorem etaleNeighborhoodMap_hom {A B : EtaleNeighborhood X ξ} (f : A ⟶ B) :
    ((etaleNeighborhoodToSmooth X ξ).map f).left ≫ (etaleNeighborhoodHom X ξ B).left =
      (etaleNeighborhoodHom X ξ A).left :=
  MorphismProperty.Over.w ((AffineEtale.Spec X.left).map f.hom)

@[reassoc (attr := simp)]
theorem etaleNeighborhoodMark_map {A B : EtaleNeighborhood X ξ} (f : A ⟶ B) :
    etaleNeighborhoodMark X ξ A ≫ ((etaleNeighborhoodToSmooth X ξ).map f).left =
      etaleNeighborhoodMark X ξ B :=
  congrArg (fun g ↦ g.left) f.map_val

/-- A morphism over the smooth object respecting the two markings is a neighborhood morphism. -/
def etaleNeighborhoodHomMk {A B : EtaleNeighborhood X ξ}
    (f : ((etaleNeighborhoodToSmooth X ξ).obj A).left ⟶
      ((etaleNeighborhoodToSmooth X ξ).obj B).left)
    (hf : f ≫ (etaleNeighborhoodHom X ξ B).left = (etaleNeighborhoodHom X ξ A).left)
    (hl : etaleNeighborhoodMark X ξ A ≫ f = etaleNeighborhoodMark X ξ B) :
    A ⟶ B :=
  let g : (AffineEtale.Spec X.left).obj A.obj ⟶ (AffineEtale.Spec X.left).obj B.obj :=
    MorphismProperty.Over.homMk f hf
  Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage g) (by
    apply Over.OverMorphism.ext
    change etaleNeighborhoodMark X ξ A ≫
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage g)).left =
        etaleNeighborhoodMark X ξ B
    rw [Functor.map_preimage]
    exact hl)

@[simp]
theorem etaleNeighborhoodHomMk_map_left {A B : EtaleNeighborhood X ξ}
    (f : ((etaleNeighborhoodToSmooth X ξ).obj A).left ⟶
      ((etaleNeighborhoodToSmooth X ξ).obj B).left)
    (hf : f ≫ (etaleNeighborhoodHom X ξ B).left = (etaleNeighborhoodHom X ξ A).left)
    (hl : etaleNeighborhoodMark X ξ A ≫ f = etaleNeighborhoodMark X ξ B) :
    ((etaleNeighborhoodToSmooth X ξ).map (etaleNeighborhoodHomMk X ξ f hf hl)).left =
      f := by
  let g : (AffineEtale.Spec X.left).obj A.obj ⟶ (AffineEtale.Spec X.left).obj B.obj :=
    MorphismProperty.Over.homMk f hf
  change ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage g)).left = g.left
  exact congrArg (fun h ↦ h.left) ((AffineEtale.Spec X.left).map_preimage g)

/-- A pointed étale scheme over the smooth object admits a pointed affine refinement. -/
theorem exists_etaleNeighborhood_refinement {Y : Scheme.{u}} (f : Y ⟶ X.left) [Etale f]
    (l : Spec (.of Ω) ⟶ Y) (hl : l ≫ f = ξ) :
    ∃ (A : EtaleNeighborhood X ξ) (g : ((etaleNeighborhoodToSmooth X ξ).obj A).left ⟶ Y),
      g ≫ f = (etaleNeighborhoodHom X ξ A).left ∧ etaleNeighborhoodMark X ξ A ≫ g = l := by
  obtain ⟨R, j, hj, l', hl'⟩ := exists_affine_residueLift l
  let : IsOpenImmersion j := hj
  exact ⟨affineNeighborhoodMk X ξ (j ≫ f) l' (by rw [← Category.assoc, hl', hl]),
    j, rfl, hl'⟩

end AlgebraicGeometry.Scheme.SmoothSite
