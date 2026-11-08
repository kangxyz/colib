/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalPairStalk

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example [IsSeparated h]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) (n : ℕ) :
    let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk a
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π a)
    letI := correspondenceIncidenceTorModule g h i w v (π a) n
    letI : Algebra P₀ P := (π.stalkMap a).hom.toAlgebra
    letI := correspondenceRightRemainingFiniteTorStalkStageModule f g h i z w v x q y hρ n
    ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a) n) := by
  exact correspondenceRightRemainingFiniteOriginalPairStalkLinearEquiv
    f g h i z w v x q y hρ n

end Stacks.Chow
