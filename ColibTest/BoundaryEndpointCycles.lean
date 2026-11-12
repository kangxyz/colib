/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryEndpointCycles

/-! # Original signed boundary and native whole endpoint cycle regression -/

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


omit [IsIntegral X] [IsAffine X] [IsSeparated p] [Smooth p] in
private theorem endpoint_over (c : k) : endpoint p c ≫ (projection p ≫ p) = p := by simp

example (c : k) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p c) (endpoint_over p c) hX)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val =
      ∑ z : support U F, componentEndpointCycle p h q j U hU F hF g hg z c :=
  correspondence_endpointGraph_eq_sourceEndpointCycles p h q j U hU F hF g hg c

end Stacks.Chow.PrincipalBoundary

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_stalkMap_ker

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_stalk_length

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpointMap_fiber_bijOn

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_finsum_stalkLength

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_fundamentalCycle_pushforward

#print axioms Stacks.Chow.PrincipalBoundary.componentMap_endpoint_source_fibres

#print axioms Stacks.Chow.PrincipalBoundary.componentEndpoint_source_projection

#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_graphPairing_eq_endpointCycle

#print axioms Stacks.Chow.PrincipalBoundary.correspondence_endpointGraph_eq_sourceEndpointCycles
