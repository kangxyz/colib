/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Colib.RingTheory.Smooth.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Canonical coordinates for affine smooth objects

The original smooth-site object is compared with `Spec Γ(X, ⊤)` by its actual
`isoSpec`. Smoothness of the global-section algebra is proved only for affine
`X`. Integral closure and Noetherianness of this ring follow from smoothness
over the field. No assertion about finite generation of global sections of a
general nonaffine smooth scheme is made.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

variable {k : Type u} [Field k]

/-- The base-field algebra structure induced by the actual scheme structure map. -/
@[instance_reducible]
def sectionsAlgebra (X : SmoothSite (Spec (.of k))) : Algebra k Γ(X.left, ⊤) :=
  (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

attribute [local instance] sectionsAlgebra

/-- On an affine smooth object, its actual global-section algebra is smooth. -/
theorem sections_smooth (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    Algebra.Smooth k Γ(X.left, ⊤) := by
  rw [← RingHom.smooth_algebraMap]
  change RingHom.Smooth (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  exact (RingHom.Smooth.of_bijective
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective).comp
      ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)
        (X := X.left) (Y := Spec (.of k)) (f := X.hom)).mp inferInstance)

/-- Affine global sections are integrally closed by genuine smooth normal ascent. -/
theorem sections_isIntegrallyClosed (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    IsIntegrallyClosed Γ(X.left, ⊤) := by
  have := sections_smooth X
  exact Algebra.Smooth.isIntegrallyClosed_of_field k Γ(X.left, ⊤)

/-- Only affine global sections are asserted Noetherian here. -/
theorem sections_isNoetherianRing (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    IsNoetherianRing Γ(X.left, ⊤) := by
  have := sections_smooth X
  exact Algebra.FiniteType.isNoetherianRing k Γ(X.left, ⊤)

/-- The original structure map, precomposed with the genuine affine scheme isomorphism. -/
abbrev structureMap (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    Spec Γ(X.left, ⊤) ⟶ Spec (.of k) := X.left.isoSpec.inv ≫ X.hom

/-- The same affine scheme with its actual smooth-site structure. -/
def obj (X : SmoothSite (Spec (.of k))) [IsAffine X.left] : SmoothSite (Spec (.of k)) :=
  mk (structureMap X)

/-- The canonical affine counit as an isomorphism of the actual smooth-site objects. -/
def iso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] : obj X ≅ X where
  hom := homMk X.left.isoSpec.inv rfl
  inv := homMk X.left.isoSpec.hom (by
    change X.left.isoSpec.hom ≫ (X.left.isoSpec.inv ≫ X.hom) = X.hom
    exact X.left.isoSpec.hom_inv_id_assoc X.hom)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact X.left.isoSpec.inv_hom_id
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact X.left.isoSpec.hom_inv_id

end AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
