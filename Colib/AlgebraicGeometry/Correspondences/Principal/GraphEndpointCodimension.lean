/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointCutCodimension
public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointParameter

/-!
# Actual graph-incidence generic points have endpoint codimension one

The original graph fibre is identified with scalar evaluation by its actual
cartesian square. Its generic points, and hence actual native graph-incidence
generic points, map to coheight one in the unchanged integral support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The whole actual graph fibre is cartesian over literal scalar evaluation. -/
theorem graphFiber_endpoint_parameter_isPullback (c : k)
    (w : pullback (C := Scheme) (projection p ≫ p) h) :
    IsPullback
      (pullback.snd (endpoint p c)
        ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h))
      (correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp) ≫
        pullback.fst p h ≫ p)
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
      (PolynomialEndpointFiber.endpoint c) :=
  (isPullback_correspondenceGraphFiberMap p (projection p ≫ p) h w
    (endpoint p c) (by simp)).flip.paste_vert (graphEndpoint_parameter_isPullback p h c)

/-- Generic points of the unchanged whole graph fibre have coheight one on the
original integral support. Its parameter dominance is sufficient. -/
theorem graphFiber_endpoint_generic_coheight (c : k)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsLocallyNoetherian (integralComponentAt w).subscheme]
    [IsDominant ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (x : genericPoints (correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c))) :
    Order.coheight (pullback.snd (endpoint p c)
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h) x.val) = 1 := by
  let := isIntegral_integralComponentAt w
  let H := (graphFiber_endpoint_parameter_isPullback p h c w).flip
  let y : genericPoints _ :=
    ⟨H.isoPullback.hom x.val, mem_genericPoints_of_flat H.isoPullback.hom x.property⟩
  have hdim := PolynomialEndpointFiber.fiberInclusion_generic_coheight _ c y
  simpa only [y, PolynomialEndpointFiber.fiberInclusion, ← Scheme.Hom.comp_apply,
    H.isoPullback_hom_snd] using hdim

/-- Every actual native graph-incidence generic point gives a genuine coheight-one
point of the original right support; no flatness of that support is required. -/
theorem graphIncidence_endpoint_generic_coheight [IsIntegral X] [IsSeparated p]
    (c : k) (s : genericPoints X)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsLocallyNoetherian (integralComponentAt w).subscheme]
    [IsDominant ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (x : genericPoints (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)) :
    Order.coheight (pullback.snd (C := Scheme) _ _ x.val) = 1 := by
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsSeparated (projection p ≫ p) := inferInstance
  let e := correspondenceLeftGraphFiberIso p (projection p ≫ p) h w (endpoint p c)
    (by simp) s
  let y : genericPoints _ := ⟨e.hom x.val, mem_genericPoints_of_flat e.hom x.property⟩
  have H := graphFiber_endpoint_generic_coheight p h c w y
  simpa only [y, e, ← Scheme.Hom.comp_apply, correspondenceLeftGraphFiberIso_snd] using H

end Stacks.Chow
