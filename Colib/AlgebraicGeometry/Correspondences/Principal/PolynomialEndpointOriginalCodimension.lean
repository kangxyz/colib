/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFiberMap
public import Colib.AlgebraicGeometry.Morphisms.Smooth.GenericFiberCodimension
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointProjection

/-!
# Original smooth endpoint codimension for whole polynomial supports

The whole finite dominant integral support has its literal endpoint over the
original smooth affine base. Its generic points map generically to that base
by the original polynomial endpoint theorem. The finite closed support then
computes their codimension in the whole smooth endpoint, not in an image support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original whole support endpoint supplies codimension in the unchanged
smooth ambient endpoint. Neither genericity nor codimension is an input. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_original_coheight
    {k : Type u} [Field k] {X V D : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : V ⟶ parameterSpace p) (n : ℕ) [SmoothOfRelativeDimension n q] [IsSeparated q]
    (i : D ⟶ V) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ q)] [IsDominant (i ≫ q)] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ q))) :
    Order.coheight (polynomialEndpointMap p q i c x.val) = n := by
  let a := polynomialEndpointMap p q i c
  let s := pullback.fst (endpoint p c) q
  have : IsClosedImmersion a :=
    MorphismProperty.of_isPullback (polynomialEndpointMap_isPullback p q i c) inferInstance
  have : SmoothOfRelativeDimension n s := by
    dsimp only [s]
    infer_instance
  have : IsSeparated s := by
    dsimp only [s]
    infer_instance
  have : IsFinite (a ≫ s) := by
    dsimp only [a, s]
    rw [polynomialEndpointMap_fst]
    infer_instance
  have hx : pullback.fst (endpoint p c) (i ≫ q) x.val ∈ genericPoints X :=
    polynomialEndpoint_generic_image_generic_of_smooth p (i ≫ q) c (𝟙 X)
      (pullback.fst (endpoint p c) (i ≫ q)) (by simp) x
  apply Scheme.coheight_eq_of_image_mem_genericPoints_finite_closed_support a s n x.val
  change (a ≫ s) x.val ∈ genericPoints X
  simpa only [a, s, polynomialEndpointMap_fst] using hx

/-- The unchanged point on an open chart of the original smooth endpoint has
the same codimension. In relative dimension one this supplies the chart point
required by the original signed principal support-cut theorem. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_chart_coheight
    {k : Type u} [Field k] {X V D W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : V ⟶ parameterSpace p) (n : ℕ) [SmoothOfRelativeDimension n q] [IsSeparated q]
    (i : D ⟶ V) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ q)] [IsDominant (i ≫ q)] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ q)))
    (j : W ⟶ pullback (endpoint p c) q) [IsOpenImmersion j]
    (y : W) (hy : j y = polynomialEndpointMap p q i c x.val) : Order.coheight y = n := by
  rw [← coheight_eq_of_isOpenImmersion j, hy]
  exact polynomialEndpoint_original_coheight p q n i c x

/-- The original curve projection keeps the original support point through the
literal endpoint map; no finite image or reduced endpoint is substituted. -/
@[reassoc (attr := simp)]
theorem polynomialEndpointMap_retainedPolynomialEndpointToCurve
    {R : Type u} [CommRing R] {X C V D : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (q : C ⟶ X)
    (r : V ⟶ parameterSpace (q ≫ p)) (i : D ⟶ V) (c : R) :
    polynomialEndpointMap p (r ≫ lineMap p q) i c ≫
        retainedPolynomialEndpointToCurve p q c r =
      pullback.snd (endpoint p c) (i ≫ (r ≫ lineMap p q)) ≫
        i ≫ r ≫ projection (q ≫ p) := by
  simp only [retainedPolynomialEndpointToCurve, polynomialEndpointMap_snd_assoc]

/-- The actual retained endpoint projection transports codimension to the
original curve, with its open-immersion property constructed internally. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_originalCurve_coheight
    {k : Type u} [Field k] {X C V D : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : C ⟶ X) (r : V ⟶ parameterSpace (q ≫ p)) [IsOpenImmersion r] (n : ℕ)
    [SmoothOfRelativeDimension n (r ≫ lineMap p q)] [IsSeparated (r ≫ lineMap p q)]
    (i : D ⟶ V) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ (r ≫ lineMap p q))] [IsDominant (i ≫ (r ≫ lineMap p q))] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ (r ≫ lineMap p q)))) :
    Order.coheight (retainedPolynomialEndpointToCurve p q c r
      (polynomialEndpointMap p (r ≫ lineMap p q) i c x.val)) = n :=
  (coheight_retainedPolynomialEndpointToCurve p q c r _).trans
    (polynomialEndpoint_original_coheight p (r ≫ lineMap p q) n i c x)

/-- Original curve charts retain the exact same endpoint point and codimension.
For relative dimension one this supplies the original affine chart point used
by `exists_chartFraction_signedEndpointSupport`. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_originalCurve_chart_coheight
    {k : Type u} [Field k] {X C V D W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : C ⟶ X) (r : V ⟶ parameterSpace (q ≫ p)) [IsOpenImmersion r] (n : ℕ)
    [SmoothOfRelativeDimension n (r ≫ lineMap p q)] [IsSeparated (r ≫ lineMap p q)]
    (i : D ⟶ V) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ (r ≫ lineMap p q))] [IsDominant (i ≫ (r ≫ lineMap p q))] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ (r ≫ lineMap p q))))
    (u : W ⟶ C) [IsOpenImmersion u] (y : W)
    (hy : u y = retainedPolynomialEndpointToCurve p q c r
      (polynomialEndpointMap p (r ≫ lineMap p q) i c x.val)) : Order.coheight y = n := by
  rw [← coheight_eq_of_isOpenImmersion u, hy]
  exact polynomialEndpoint_originalCurve_coheight p q r n i c x

/-- In the original retained polynomial family the original relative-curve
smoothness supplies all smooth-family data. The endpoint image has codimension
one in the original curve rather than only in the polynomial endpoint. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_retainedCurve_coheight
    {k : Type u} [Field k] {X C V D : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : C ⟶ X) [IsSeparated q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (i : D ⟶ parameterSpace (j ≫ (q ≫ p))) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q))]
    [IsDominant (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q))] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c)
      (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q)))) :
    Order.coheight (retainedPolynomialEndpointToCurve p q c (lineMap (q ≫ p) j)
      (polynomialEndpointMap p (lineMap (q ≫ p) j ≫ lineMap p q) i c x.val)) = 1 := by
  have : SmoothOfRelativeDimension 1 (lineMap (q ≫ p) j ≫ lineMap p q) :=
    MorphismProperty.of_isPullback
      ((lineMap_isPullback (q ≫ p) j).paste_horiz (lineMap_isPullback p q)).flip inferInstance
  have : IsSeparated (lineMap p q) :=
    MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance
  exact polynomialEndpoint_originalCurve_coheight p q (lineMap (q ≫ p) j) 1 i c x

/-- The exact retained relative-curve setup supplies codimension one at the
actual original affine-chart point used by the signed endpoint calculation. -/
@[colib_tag "COL-1090"]
theorem polynomialEndpoint_retainedCurve_chart_coheight
    {k : Type u} [Field k] {X C V D W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : C ⟶ X) [IsSeparated q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (i : D ⟶ parameterSpace (j ≫ (q ≫ p))) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q))]
    [IsDominant (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q))] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c)
      (i ≫ (lineMap (q ≫ p) j ≫ lineMap p q))))
    (u : W ⟶ C) [IsOpenImmersion u] (y : W)
    (hy : u y = retainedPolynomialEndpointToCurve p q c (lineMap (q ≫ p) j)
      (polynomialEndpointMap p (lineMap (q ≫ p) j ≫ lineMap p q) i c x.val)) :
    Order.coheight y = 1 := by
  rw [← coheight_eq_of_isOpenImmersion u, hy]
  exact polynomialEndpoint_retainedCurve_coheight p q j i c x

end AlgebraicGeometry.PrincipalFamilyUnitOpen
