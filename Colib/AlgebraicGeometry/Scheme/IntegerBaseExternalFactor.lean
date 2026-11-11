/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseBraid

/-!
# Moving an external factor past two internal factors

The current
consumer is the external Laurent track over the double Bass interchange. All maps use
original left-nested pullbacks, and the opposite square retains its reversed direction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}

/-- Move the last factor to the first position without changing the two internal factors. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalFactor.lean:27"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
def baseProductMoveExternal (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor r).obj ((baseProductFunctor q).obj ((baseProductFunctor p).obj X)) ⟶
      (baseProductFunctor q).obj ((baseProductFunctor p).obj ((baseProductFunctor r).obj X)) :=
  baseProductSwapMap q r ((baseProductFunctor p).obj X) ≫
    (baseProductFunctor q).map (baseProductSwapMap p r X)

/-- Internal interchange commutes with moving the distinguished external factor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalFactor.lean:35"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
theorem baseProductMoveExternal_swap (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor r).map (baseProductSwapMap p q X) ≫
        baseProductMoveExternal q p r X =
      baseProductMoveExternal p q r X ≫
        baseProductSwapMap p q ((baseProductFunctor r).obj X) := by
  simpa only [baseProductMoveExternal, Category.assoc] using baseProductSwapMap_braid p q r X

/-- The same index square in the actual contravariant variance. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalFactor.lean:44"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
theorem baseProductMoveExternal_swap_op (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductMoveExternal q p r X).op ≫
        ((baseProductFunctor r).map (baseProductSwapMap p q X)).op =
      (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op ≫
        (baseProductMoveExternal p q r X).op :=
  congrArg Quiver.Hom.op (baseProductMoveExternal_swap p q r X)

/-- The complete external projection is unchanged by the two original swaps. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalFactor.lean:53"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
theorem baseProductMoveExternal_projection (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    baseProductMoveExternal p q r X ≫
        pullback.fst
          (specULiftZIsTerminal.from ((baseProductFunctor p).obj
            ((baseProductFunctor r).obj X))) q ≫
          pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor r).obj X)) p ≫
            pullback.snd (specULiftZIsTerminal.from X) r =
      pullback.snd
        (specULiftZIsTerminal.from
          ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) r := by
  simp [baseProductMoveExternal, baseProductSwapMap, baseProductFunctor, Category.assoc]

end AlgebraicGeometry.Scheme.Products
