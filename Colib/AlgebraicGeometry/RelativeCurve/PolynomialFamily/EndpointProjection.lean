/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen

/-!
# The actual polynomial endpoint map to the original curve

The endpoint of a full polynomial product is canonically its original source.
For an open retained subscheme of that product, the actual endpoint therefore
maps by an open immersion to the original source. The maps below are the
original projections, without replacing the endpoint or its support by a reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {R : Type u} [CommRing R] {X C V : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (q : C ⟶ X) (c : R)

/-- The projection of the whole literal polynomial endpoint to the original curve. -/
def polynomialEndpointProjection :
    pullback (endpoint p c) (lineMap p q) ⟶ C :=
  pullback.snd (endpoint p c) (lineMap p q) ≫ projection (q ≫ p)

instance : IsIso (polynomialEndpointProjection p q c) := by
  have H := (IsPullback.of_hasPullback (endpoint p c) (lineMap p q)).paste_vert
    (lineMap_isPullback p q)
  rw [endpoint_projection] at H
  exact H.isIso_snd_of_isIso

/-- The unchanged retained endpoint maps to the original curve by the actual
retained inclusion followed by the polynomial projection. -/
def retainedPolynomialEndpointToCurve (r : V ⟶ parameterSpace (q ≫ p)) :
    pullback (endpoint p c) (r ≫ lineMap p q) ⟶ C :=
  pullback.snd (endpoint p c) (r ≫ lineMap p q) ≫ r ≫ projection (q ≫ p)

instance (r : V ⟶ parameterSpace (q ≫ p)) [IsOpenImmersion r] :
    IsOpenImmersion (retainedPolynomialEndpointToCurve p q c r) := by
  let a := pullback.map (endpoint p c) (r ≫ lineMap p q)
    (endpoint p c) (lineMap p q) (𝟙 _) r (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion a := by
    dsimp only [a]
    infer_instance
  have he : retainedPolynomialEndpointToCurve p q c r =
      a ≫ polynomialEndpointProjection p q c := by
    simp only [retainedPolynomialEndpointToCurve, polynomialEndpointProjection,
      a, pullback.map, Category.assoc, pullback.lift_snd_assoc]
  rw [he]
  infer_instance

/-- The retained endpoint preserves the coheight of its actual original-curve image. -/
theorem coheight_retainedPolynomialEndpointToCurve
    (r : V ⟶ parameterSpace (q ≫ p)) [IsOpenImmersion r]
    (x : pullback (C := Scheme) (endpoint p c) (r ≫ lineMap p q)) :
    Order.coheight (retainedPolynomialEndpointToCurve p q c r x) = Order.coheight x :=
  coheight_eq_of_isOpenImmersion (retainedPolynomialEndpointToCurve p q c r)

end AlgebraicGeometry.PrincipalFamilyUnitOpen
