/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointFundamentalCycle

/-! # Literal endpoint Tor cycle and full graph fibre regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

variable [IsIntegral X] [IsSeparated p] [Smooth p] [Smooth h]
  (c : k) (s : genericPoints X)
  (w : pullback (C := Scheme) (projection p ≫ p) h)
  [IsDominant ((integralComponentAt w).subschemeι ≫
    pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]

omit [IsIntegral X] [IsSeparated p] [Smooth p] in
private theorem endpoint_over : endpoint p c ≫ (projection p ≫ p) = p := by simp

example
    [IsSeparated h] [IsNoetherian X]
    (hw : IsFiniteCorrespondencePoint (projection p ≫ p) h w) :
    let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (endpoint_over p c) s.val
    let hδ := isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
      (endpoint p c) (endpoint_over p c) s
    letI := hw.1
    letI := isNoetherian_correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c) hw
    letI := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
      (endpoint p c) (endpoint_over p c) hw
    (incidenceTorCorrespondence p (projection p ≫ p) h δ w hδ hw).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (endpoint_over p c))
        (AlgebraicCycle.fundamentalCycle
          (correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c))) :=
  graphEndpoint_incidenceTorCorrespondence_eq_graphFiberPushforward p h c s w hw

end Stacks.Chow

#print axioms Stacks.Chow.graphIncidenceTorCoefficient_eq_fullStalkLength

#print axioms Stacks.Chow.graphEndpoint_incidenceTorCycle_eq_fundamentalCycle

#print axioms Stacks.Chow.graphEndpoint_incidenceTorCorrespondence_val

#print axioms Stacks.Chow.graphEndpoint_incidenceTorCorrespondence_eq_graphFiberPushforward
