/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange

/-!
# The braid relation for the original three independent product factors

Arbitrary fixed maps to
the integral terminal scheme are used, with no compactness assumptions. The two literal
three-swap words retain the left-nested pullback objects. The current consumer is scalar
compatibility of independent Laurent variables in the double Bass construction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}

/-- The two adjacent-swap words agree as actual maps of the original nested products. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseBraid.lean:28"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
theorem baseProductSwapMap_braid (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor r).map (baseProductSwapMap p q X) ≫
        baseProductSwapMap p r ((baseProductFunctor q).obj X) ≫
          (baseProductFunctor p).map (baseProductSwapMap q r X) =
      baseProductSwapMap q r ((baseProductFunctor p).obj X) ≫
        (baseProductFunctor q).map (baseProductSwapMap p r X) ≫
          baseProductSwapMap p q ((baseProductFunctor r).obj X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [baseProductSwapMap, baseProductFunctor, Category.assoc]
    · simp [baseProductSwapMap, baseProductFunctor, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, Category.assoc]

end AlgebraicGeometry.Scheme.Products
