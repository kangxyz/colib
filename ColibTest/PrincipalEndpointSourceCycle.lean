/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalEndpointOrderCycle

/-! # Regression for original whole signed source endpoint cycles -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : C ⟶ X) [IsIntegral C] [IsNoetherian C]
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W]

example
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen (q ≫ p) v f)]
    (x : C) (hx : Order.coheight x = 1) :
    signedSourceEndpointCycle p q 0 (ambientRationalFunction (q ≫ p) v f) x = 0 ∧
    signedSourceEndpointCycle p q 1 (ambientRationalFunction (q ≫ p) v f) x =
      C.ord (curveRationalFunction v f) x :=
  signedSourceEndpointCycle_zero_one_of_coheight p q v f hf x hx

end AlgebraicGeometry.PrincipalFamilyUnitOpen

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpointProjection_endpoint
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.sourceEndpointToCurve_endpoint
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.sourceEndpoint_fundamentalCycle_coefficient
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.sourceEndpointToCurve_range
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.sourceEndpoint_fundamentalCycle_apply
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.signedSourceEndpointCycle_apply
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.signedSourceEndpointCycle_zero_one_of_coheight
