/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.AmbientPrincipalSupportCuts

/-! # Regression for original ambient principal support endpoint identities -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

variable {k : Type u} [Field k] {C W U : Scheme.{u}}
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W] [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsIntegral (parameterSpace p)]
    [IsLocallyNoetherian (parameterSpace p)]
    (u : U ⟶ C) [IsOpenImmersion u] [IsIntegral U]
    [IsAffine U] [IsNoetherian U] [IsNoetherian (parameterSpace (u ≫ p))]

local instance : IsIntegral (parameterSpace (u ≫ p)) := by
  have : Nonempty (parameterSpace (u ≫ p)) := ⟨endpoint (u ≫ p) 0 (genericPoint U)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p u)

example [IsLocallyNoetherian C]
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)]
    (x : U) (hx : Order.coheight x = 1) :
    let P := parameterSpace p
    let F := ambientRationalFunction p v f
    (∑ᶠ z ∈ principalSupportThrough P (endpoint p 0 (u x)) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint p 0 (u x)) z
        (endpointEquation p 0)) = 0 ∧
    (∑ᶠ z ∈ principalSupportThrough P (endpoint p 1 (u x)) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint p 1 (u x)) z
        (endpointEquation p 1)) = C.ord (curveRationalFunction v f) (u x) :=
  ambientPrincipalSupportCuts_zero_one v p u f hf x hx

end AlgebraicGeometry.PrincipalFamilyUnitOpen

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.endpoint_lineMap
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.lineMap_endpointEquation
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.ambientPrincipalSupportCuts_zero_one
