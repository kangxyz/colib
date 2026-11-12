/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.ChartSignedSupportCuts

/-! # Genuine original chart and signed full support endpoint regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyEndpointCuts

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

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

/-- The original section and original chart produce literal polynomial fractions
whose full signed integral-support cuts cancel at zero and equal the original
curve order at one. No local regularity or fraction-identity certificate is an input. -/
example
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)] :
    ∃ a b : Γ(U, ⊤),
      U.germToFunctionField ⊤ a / U.germToFunctionField ⊤ b =
        u.functionFieldMap (curveRationalFunction v f) ∧
      (lineMap p u).functionFieldMap (ambientRationalFunction p v f) =
        (parameterSpace (u ≫ p)).germToFunctionField ⊤ (numerator (u ≫ p) a b) /
          (parameterSpace (u ≫ p)).germToFunctionField ⊤ (denominator (u ≫ p) b) ∧
      ∀ (x : U) (_hx : Order.coheight x = 1),
        signedEndpointSupportCoefficient (u ≫ p) 0 x
          (numerator (u ≫ p) a b) (denominator (u ≫ p) b) = 0 ∧
        signedEndpointSupportCoefficient (u ≫ p) 1 x
          (numerator (u ≫ p) a b) (denominator (u ≫ p) b) =
            U.ord (u.functionFieldMap (curveRationalFunction v f)) x :=
  exists_chartFraction_signedEndpointSupport v p u f hf

#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.signedEndpointSupportCoefficient_eq_cutLengthDifference
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.signedEndpointSupportCoefficient_eq_weightedTorDifference
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.exists_chartFraction_signedEndpointSupport

end AlgebraicGeometry.PrincipalFamilyUnitOpen
