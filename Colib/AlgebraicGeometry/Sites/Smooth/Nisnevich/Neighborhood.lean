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
# Pointed affine étale neighborhoods in the smooth site

A neighborhood of a point of a smooth object is an affine étale scheme
over the object with a lift of its residue-field arrow. The neighborhoods
form the category of elements of this lifting functor on the native
affine étale site.

Finite limits give cofilteredness on the full étale site. Affine open
refinement at the lifted point gives cofilteredness for the affine
neighborhoods and their small initial model. Over a quasi-separated
base these affine schemes give objects in the original smooth site.
The affine refinement argument follows Mathlib's `pointSmallEtale`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (X : SmoothSite S) (x : X.left)

/-- The functor of actual lifts of the residue-field arrow on the affine étale site. -/
abbrev nisnevichNeighborhoodFiber : X.left.AffineEtale ⥤ Type u :=
  AffineEtale.Spec X.left ⋙ Etale.forget X.left ⋙
    coyoneda.obj (op (Over.mk (X.left.fromSpecResidueField x)))

/-- The category of pointed affine étale neighborhoods of a point of a smooth object. -/
abbrev NisnevichNeighborhood := (nisnevichNeighborhoodFiber X x).Elements

private abbrev etaleNeighborhoodFiber : X.left.Etale ⥤ Type u :=
  Etale.forget X.left ⋙ coyoneda.obj (op (Over.mk (X.left.fromSpecResidueField x)))

private abbrev affineNeighborhoodInclusion :
    NisnevichNeighborhood X x ⥤ (etaleNeighborhoodFiber X x).Elements :=
  Functor.Elements.precomp (AffineEtale.Spec X.left) (etaleNeighborhoodFiber X x)

private def affineNeighborhoodInclusionFullyFaithful :
    (affineNeighborhoodInclusion X x).FullyFaithful where
  preimage f := Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage f.hom) (by
    change (etaleNeighborhoodFiber X x).map
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom)) _ = _
    rw [Functor.map_preimage]
    exact f.map_val)
  map_preimage f := by
    apply Functor.Elements.hom_ext
    change (AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom) = f.hom
    exact (AffineEtale.Spec X.left).map_preimage f.hom
  preimage_map f := Functor.Elements.hom_ext (Functor.preimage_map f.hom)

private def affineNeighborhoodMk {R : CommRingCat.{u}} (f : Spec R ⟶ X.left) [Etale f]
    (l : Spec (.of (X.left.residueField x)) ⟶ Spec R)
    (hl : l ≫ f = X.left.fromSpecResidueField x) :
    NisnevichNeighborhood X x :=
  (nisnevichNeighborhoodFiber X x).elementsMk (AffineEtale.mk f) (Over.homMk l hl)

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

private theorem exists_affineNeighborhood (A : (etaleNeighborhoodFiber X x).Elements) :
    ∃ B : NisnevichNeighborhood X x, Nonempty ((affineNeighborhoodInclusion X x).obj B ⟶ A) := by
  let f := A.obj.hom
  let : Etale f := A.obj.prop
  let l : Spec (.of (X.left.residueField x)) ⟶ A.obj.left := A.val.left
  have hl : l ≫ f = X.left.fromSpecResidueField x := Over.w A.val
  obtain ⟨R, j, hj, l', hl'⟩ := exists_affine_residueLift l
  let : IsOpenImmersion j := hj
  let B := affineNeighborhoodMk X x (j ≫ f) l' (by rw [← Category.assoc, hl', hl])
  refine ⟨B, ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk j rfl) ?_⟩⟩
  exact Over.OverMorphism.ext hl'

instance : IsCofiltered (NisnevichNeighborhood X x) := by
  let F := affineNeighborhoodInclusion X x
  let h := affineNeighborhoodInclusionFullyFaithful X x
  let : F.Full := h.full
  let : F.Faithful := h.faithful
  let : IsCofiltered (etaleNeighborhoodFiber X x).Elements :=
    Functor.isCofiltered_elements _
  exact IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F
    (exists_affineNeighborhood X x)

instance : InitiallySmall.{u} (NisnevichNeighborhood X x) :=
  initiallySmall_of_essentiallySmall _

/-- The same neighborhoods have a small initial model in a larger universe. -/
theorem nisnevichNeighborhoodInitiallySmall :
    InitiallySmall.{max u w} (NisnevichNeighborhood X x) := by
  let N := NisnevichNeighborhood X x
  let E : InitialModel.{u} N ≌ AsSmall.{w} (InitialModel.{u} N) := AsSmall.equiv
  exact InitiallySmall.mk' (E.inverse ⋙ fromInitialModel.{u} N)

variable [QuasiSeparatedSpace S]

/-- The actual functor of neighborhoods into the smooth site over the base. -/
def nisnevichNeighborhoodToSmooth : NisnevichNeighborhood X x ⥤ SmoothSite S :=
  let F := Functor.Elements.π (nisnevichNeighborhoodFiber X x) ⋙
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

instance (A : NisnevichNeighborhood X x) :
    IsAffine ((nisnevichNeighborhoodToSmooth X x).obj A).left := by
  change IsAffine (Spec A.obj.left.unop)
  infer_instance

/-- The actual morphism from a neighborhood to the selected smooth object. -/
def nisnevichNeighborhoodHom (A : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodToSmooth X x).obj A ⟶ X :=
  homMk A.obj.hom rfl

instance nisnevichNeighborhoodHom_etale (A : NisnevichNeighborhood X x) :
    Etale (nisnevichNeighborhoodHom X x A).left :=
  A.obj.prop

/-- The actual field-valued marking of a neighborhood. -/
def nisnevichNeighborhoodMark (A : NisnevichNeighborhood X x) :
    Spec (.of (X.left.residueField x)) ⟶ ((nisnevichNeighborhoodToSmooth X x).obj A).left :=
  A.val.left

@[reassoc (attr := simp)]
theorem nisnevichNeighborhoodMark_hom (A : NisnevichNeighborhood X x) :
    nisnevichNeighborhoodMark X x A ≫ (nisnevichNeighborhoodHom X x A).left =
      X.left.fromSpecResidueField x :=
  Over.w A.val

@[reassoc (attr := simp)]
theorem nisnevichNeighborhoodMap_hom {A B : NisnevichNeighborhood X x} (f : A ⟶ B) :
    ((nisnevichNeighborhoodToSmooth X x).map f).left ≫ (nisnevichNeighborhoodHom X x B).left =
      (nisnevichNeighborhoodHom X x A).left :=
  MorphismProperty.Over.w ((AffineEtale.Spec X.left).map f.hom)

@[reassoc (attr := simp)]
theorem nisnevichNeighborhoodMark_map {A B : NisnevichNeighborhood X x} (f : A ⟶ B) :
    nisnevichNeighborhoodMark X x A ≫ ((nisnevichNeighborhoodToSmooth X x).map f).left =
      nisnevichNeighborhoodMark X x B :=
  congrArg (fun g ↦ g.left) f.map_val

/-- A morphism over the smooth object respecting the two markings is a neighborhood morphism. -/
def nisnevichNeighborhoodHomMk {A B : NisnevichNeighborhood X x}
    (f : ((nisnevichNeighborhoodToSmooth X x).obj A).left ⟶
      ((nisnevichNeighborhoodToSmooth X x).obj B).left)
    (hf : f ≫ (nisnevichNeighborhoodHom X x B).left = (nisnevichNeighborhoodHom X x A).left)
    (hl : nisnevichNeighborhoodMark X x A ≫ f = nisnevichNeighborhoodMark X x B) :
    A ⟶ B :=
  let g : (AffineEtale.Spec X.left).obj A.obj ⟶ (AffineEtale.Spec X.left).obj B.obj :=
    MorphismProperty.Over.homMk f hf
  Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage g) (by
    apply Over.OverMorphism.ext
    change nisnevichNeighborhoodMark X x A ≫
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage g)).left =
        nisnevichNeighborhoodMark X x B
    rw [Functor.map_preimage]
    exact hl)

@[simp]
theorem nisnevichNeighborhoodHomMk_map_left {A B : NisnevichNeighborhood X x}
    (f : ((nisnevichNeighborhoodToSmooth X x).obj A).left ⟶
      ((nisnevichNeighborhoodToSmooth X x).obj B).left)
    (hf : f ≫ (nisnevichNeighborhoodHom X x B).left = (nisnevichNeighborhoodHom X x A).left)
    (hl : nisnevichNeighborhoodMark X x A ≫ f = nisnevichNeighborhoodMark X x B) :
    ((nisnevichNeighborhoodToSmooth X x).map (nisnevichNeighborhoodHomMk X x f hf hl)).left =
      f := by
  let g : (AffineEtale.Spec X.left).obj A.obj ⟶ (AffineEtale.Spec X.left).obj B.obj :=
    MorphismProperty.Over.homMk f hf
  change ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage g)).left = g.left
  exact congrArg (fun h ↦ h.left) ((AffineEtale.Spec X.left).map_preimage g)

/-- A pointed étale scheme over the smooth object admits a pointed affine refinement. -/
theorem exists_nisnevichNeighborhood_refinement {Y : Scheme.{u}} (f : Y ⟶ X.left) [Etale f]
    (l : Spec (.of (X.left.residueField x)) ⟶ Y) (hl : l ≫ f = X.left.fromSpecResidueField x) :
    ∃ (A : NisnevichNeighborhood X x) (g : ((nisnevichNeighborhoodToSmooth X x).obj A).left ⟶ Y),
      g ≫ f = (nisnevichNeighborhoodHom X x A).left ∧ nisnevichNeighborhoodMark X x A ≫ g = l := by
  obtain ⟨R, j, hj, l', hl'⟩ := exists_affine_residueLift l
  let : IsOpenImmersion j := hj
  exact ⟨affineNeighborhoodMk X x (j ≫ f) l' (by rw [← Category.assoc, hl', hl]),
    j, rfl, hl'⟩

end AlgebraicGeometry.Scheme.SmoothSite
