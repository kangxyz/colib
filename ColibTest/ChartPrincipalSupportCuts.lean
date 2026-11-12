/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.ChartPrincipalSupportCuts

/-! # Regression for original chart principal-cycle endpoint cuts -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open AlgebraicGeometry.PrincipalFamilyEndpointCuts

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

variable {k : Type u} [Field k] {C W U : Scheme.{u}}
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W] [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsIntegral (parameterSpace p)]
    (u : U ⟶ C) [IsOpenImmersion u] [IsIntegral U]
    [IsAffine U] [IsNoetherian U] [IsNoetherian (parameterSpace (u ≫ p))]

local instance : IsIntegral (parameterSpace (u ≫ p)) := by
  have : Nonempty (parameterSpace (u ≫ p)) := ⟨endpoint (u ≫ p) 0 (genericPoint U)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p u)

example
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)]
    (x : U) (hx : Order.coheight x = 1) :
    let P := parameterSpace (u ≫ p)
    let F := (lineMap p u).functionFieldMap (ambientRationalFunction p v f)
    (∑ᶠ z ∈ principalSupportThrough P (endpoint (u ≫ p) 0 x) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint (u ≫ p) 0 x) z
        (endpointEquation (u ≫ p) 0)) = 0 ∧
    (∑ᶠ z ∈ principalSupportThrough P (endpoint (u ≫ p) 1 x) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint (u ≫ p) 1 x) z
        (endpointEquation (u ≫ p) 1)) =
      U.ord (u.functionFieldMap (curveRationalFunction v f)) x :=
  chartPrincipalSupportCuts_zero_one v p u f hf x hx

end AlgebraicGeometry.PrincipalFamilyUnitOpen

#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.principalSupportCuts_eq_signedEndpointSupportCoefficient
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.chartPrincipalSupportCuts_zero_one
