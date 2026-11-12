/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryGraphEndpointPushforward

/-! # Whole native endpoint graph, original signed source cuts, and all collisions -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {k : Type u} [Field k] {C X Y V : Scheme.{u}}
    [IsIntegral C] [IsNoetherian C] [IsIntegral X] [IsAffine X]
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k))
    [IsSeparated p] [IsSeparated h] [Smooth p] [Smooth h]
    (q : C ⟶ parameterSpace p) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (F : Γ(C, U)) (hF : IsUnit F)
    (g : V ⟶ Y) (hg : j ≫ q ≫ (projection p ≫ p) = g ≫ h)

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

/-- Regression of the actual whole graph and original whole principal correspondence. -/
example (c : k) (s : genericPoints X)
    (y : pullback (C := Scheme) p h) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p c) (by simp) hX)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val y =
      ∑ z : support U F,
        sourceEndpointPushforwardCoefficient p h q j U hU F hF g hg z c s y :=
  correspondence_endpointGraph_coefficient p h q j U hU F hF g hg c s y

#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_graphEndpointPushforwardCoefficient
#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_graphPairing_coefficient
#print axioms Stacks.Chow.PrincipalBoundary.correspondence_graphPairing_coefficient
#print axioms Stacks.Chow.PrincipalBoundary.correspondence_endpointGraph_coefficient

end Stacks.Chow.PrincipalBoundary
