/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialAffineCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.SectionCoordinates
public import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteDominantEndpointGenericity

/-!
# Genericity for the actual original polynomial endpoint

Canonical affine coordinates supply the literal evaluation square internally.
The finite dominant support is unchanged and need not be flat or normal. Only
the global section ring of the original affine base is assumed normal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [CommRing k] {X C F : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsAffine X]
  (m : C ⟶ parameterSpace p) (c : k)

/-- The whole actual endpoint fibre, in canonical polynomial coordinates, is
cartesian over literal scalar evaluation on the original affine base. -/
theorem polynomialEndpoint_coordinate_isPullback :
    IsPullback (pullback.snd (endpoint p c) m)
      (pullback.fst (endpoint p c) m ≫ X.isoSpec.hom)
      (m ≫ (affinePolynomialIso p).inv)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (affineScalar p c)))) :=
  (IsPullback.of_hasPullback (endpoint p c) m).flip.paste_vert
    (affinePolynomialIso_endpoint_isPullback p c)

/-- The actual original polynomial endpoint sends its generic points generically
into any finite endpoint over the same original normal affine base. -/
theorem polynomialEndpoint_generic_image_generic
    [IsIntegral C] [IsFinite m] [IsDominant m]
    [IsDomain Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (q : F ⟶ X) [IsFinite q]
    (r : pullback (endpoint p c) m ⟶ F)
    (hr : r ≫ q = pullback.fst (endpoint p c) m)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) m)) : r x.val ∈ genericPoints F := by
  exact Scheme.FiniteDominantFace.original_face_generic_image_generic
    (m ≫ (affinePolynomialIso p).inv) (pullback.snd (endpoint p c) m)
    (pullback.fst (endpoint p c) m ≫ X.isoSpec.hom) (affineScalar p c)
    (polynomialEndpoint_coordinate_isPullback p m c) (q ≫ X.isoSpec.hom) r
    (by rw [← Category.assoc, hr]) x.val x.property

end AlgebraicGeometry.PrincipalFamilyUnitOpen

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- Smoothness of the original affine base supplies normality internally, so
actual original endpoint genericity requires no separate coordinate or normality witness. -/
theorem polynomialEndpoint_generic_image_generic_of_smooth
    {k : Type u} [Field k] {X C F : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (m : C ⟶ parameterSpace p) [IsIntegral C] [IsFinite m] [IsDominant m]
    (c : k) (q : F ⟶ X) [IsFinite q]
    (r : pullback (endpoint p c) m ⟶ F)
    (hr : r ≫ q = pullback.fst (endpoint p c) m)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) m)) :
    r x.val ∈ genericPoints F := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  let : IsAffine (Scheme.SmoothSite.mk p).left := inferInstanceAs (IsAffine X)
  let : IsIntegrallyClosed Γ(X, ⊤) :=
    Scheme.SmoothSite.AffineSectionCoordinates.sections_isIntegrallyClosed
      (Scheme.SmoothSite.mk p)
  exact polynomialEndpoint_generic_image_generic p m c q r hr x

end AlgebraicGeometry.PrincipalFamilyUnitOpen
