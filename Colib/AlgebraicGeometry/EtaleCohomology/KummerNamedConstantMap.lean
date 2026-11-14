/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerLiteralConstantMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback

/-!
# Original named constant map

Import the actual module defining the original named map;
no replacement declaration and no assumption of equality is introduced.
This only identifies the degree-zero source morphism, not the full Ext equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The morphism from the original corepresentations equals the existing named source map. -/
theorem kummerConstantRestriction_eq_originalConstantMap :
    (etaleModuleUnderlyingAbelianConstantIso X).inv ≫
      (etaleModuleUnderlyingAbelian X ℤ).map (kummerConstantRestrictionHom Λ X) =
      etaleModuleUnderlyingAbelianConstantMap Λ X := by
  exact kummerConstantRestriction_eq_literal Λ X

end Stacks.EtaleCohomology
end
