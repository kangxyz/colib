/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.SectionCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-! # Natural actual affine coordinates on the smooth site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

variable {k : Type u} [Field k]

attribute [local instance] sectionsAlgebra

/-- Ordinary restriction of sections is an algebra map for these original actions. -/
def sectionsMap {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    Γ(Y.left, ⊤) →ₐ[k] Γ(X.left, ⊤) where
  __ := f.left.appTop.hom
  commutes' r := by
    have he : Y.hom.appTop ≫ f.left.appTop = X.hom.appTop := by
      rw [← Scheme.Hom.comp_appTop, MorphismProperty.Over.w]
    exact congrArg (fun g => g ((Scheme.ΓSpecIso (.of k)).inv r)) he

variable (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

/-- Smoothness uses the existing canonical global-section algebra. -/
instance sectionsSmooth : Algebra.Smooth k Γ(X.left, ⊤) := sections_smooth X

/-- Noetherianness uses the existing canonical global-section algebra. -/
instance sectionsNoetherian : IsNoetherianRing Γ(X.left, ⊤) :=
  sections_isNoetherianRing X

/-- The canonical affine scheme comparison preserves the original base map. -/
theorem isoSpec_inv_base :
    X.left.isoSpec.inv ≫ X.hom = affineBaseMap k Γ(X.left, ⊤) := by
  rw [← Scheme.isoSpec_inv_naturality (show X.left ⟶ Spec (.of k) from X.hom),
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Canonical affine coordinates as an isomorphism in the actual smooth site. -/
def affineIso : affineSite k Γ(X.left, ⊤) ≅ X where
  hom := homMk X.left.isoSpec.inv (isoSpec_inv_base X)
  inv := homMk X.left.isoSpec.hom (by
    apply (cancel_epi X.left.isoSpec.inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (isoSpec_inv_base X).symm)
  hom_inv_id := by apply MorphismProperty.Over.Hom.ext; exact X.left.isoSpec.inv_hom_id
  inv_hom_id := by apply MorphismProperty.Over.Hom.ext; exact X.left.isoSpec.hom_inv_id

@[simp] theorem affineIso_hom_left : (affineIso X).hom.left = X.left.isoSpec.inv := rfl
@[simp] theorem affineIso_inv_left : (affineIso X).inv.left = X.left.isoSpec.hom := rfl

variable {X} {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]

/-- Canonical affine coordinates retain every actual ordinary morphism. -/
@[reassoc] theorem affineIso_naturality (f : X ⟶ Y) :
    affineMorphism (sectionsMap f) ≫ (affineIso Y).hom = (affineIso X).hom ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.isoSpec_inv_naturality f.left

end AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
