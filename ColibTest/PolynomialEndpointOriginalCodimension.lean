/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointOriginalCodimension

/-! # Codimension one on the original endpoint and its unchanged chart -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X V D W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : V ⟶ parameterSpace p) [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    (i : D ⟶ V) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ q)] [IsDominant (i ≫ q)] (c : k)
    (x : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ q)))

example : Order.coheight (polynomialEndpointMap p q i c x.val) = 1 :=
  polynomialEndpoint_original_coheight p q 1 i c x

example (j : W ⟶ pullback (endpoint p c) q) [IsOpenImmersion j]
    (y : W) (hy : j y = polynomialEndpointMap p q i c x.val) : Order.coheight y = 1 :=
  polynomialEndpoint_chart_coheight p q 1 i c x j y hy

#print axioms polynomialEndpoint_original_coheight
#print axioms polynomialEndpoint_chart_coheight

example {K : Type u} [CommRing K] {S B A : Scheme.{u}}
    (b : S ⟶ Spec (.of K)) (a : B ⟶ S) (r : A ⟶ parameterSpace (a ≫ b))
    [IsOpenImmersion r] (d : K)
    (z : pullback (C := Scheme) (endpoint b d) (r ≫ lineMap b a)) :
    IsIso ((retainedPolynomialEndpointToCurve b a d r).stalkMap z) := inferInstance

example {K : Type u} [Field K] {S C A B U : Scheme.{u}}
    (b : S ⟶ Spec (.of K)) [IsAffine S] [IsIntegral S] [Smooth b]
    (a : C ⟶ S) [IsSeparated a] (j : A ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ a)]
    (i : B ⟶ parameterSpace (j ≫ (a ≫ b))) [IsClosedImmersion i] [IsIntegral B]
    [IsFinite (i ≫ (lineMap (a ≫ b) j ≫ lineMap b a))]
    [IsDominant (i ≫ (lineMap (a ≫ b) j ≫ lineMap b a))] (d : K)
    (z : genericPoints (pullback (C := Scheme) (endpoint b d)
      (i ≫ (lineMap (a ≫ b) j ≫ lineMap b a))))
    (u : U ⟶ C) [IsOpenImmersion u] (y : U)
    (hy : u y = retainedPolynomialEndpointToCurve b a d (lineMap (a ≫ b) j)
      (polynomialEndpointMap b (lineMap (a ≫ b) j ≫ lineMap b a) i d z.val)) :
    Order.coheight y = 1 :=
  polynomialEndpoint_retainedCurve_chart_coheight b a j i d z u y hy

#print axioms polynomialEndpointProjection
#print axioms coheight_retainedPolynomialEndpointToCurve
#print axioms polynomialEndpointMap_retainedPolynomialEndpointToCurve
#print axioms polynomialEndpoint_originalCurve_coheight
#print axioms polynomialEndpoint_originalCurve_chart_coheight
#print axioms polynomialEndpoint_retainedCurve_coheight
#print axioms polynomialEndpoint_retainedCurve_chart_coheight

end AlgebraicGeometry.PrincipalFamilyUnitOpen
