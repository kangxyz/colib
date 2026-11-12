/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfect
public import Colib.CategoryTheory.Functor.IdentityAutomorphism
public import Colib.KTheory.Waldhausen.Iterated.IdentityActionInterchangeSign

/-!
# Global scalar identity actions on bounded-above flat perfect K-groups

The actual global unit is lifted through the existing faithful small equivalence.
The unchanged original K-operation is induced by its complete identity-action track.
Two such operations anticommute in every nonnegative degree, including input K-zero.
This statement does not identify a double-cokernel swap in negative K-theory.

Source: Quillen revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`, the scalar-action
parts of `ProductSwapUnit`, `GlobalUnitIdentityOperation` and `ProductUnitInterchangeSign`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] boundedAboveFlatPerfectGlobalUnitIso

namespace ProductSwapUnit

local instance {Y : Scheme.{u}} :
    (AsSmall.down : AsSmall.{0}
      (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory).IsEquivalence :=
  (AsSmall.equiv : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ≌
    AsSmall.{0}
      (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory).isEquivalence_inverse

/-- The genuine global scalar along the original faithful small equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:90-94"
  "adaptation" "Actual global unit lifted along the unchanged small equivalence."]
def smallUnit (Y : Scheme.{u}) (r : (Γ(Y, ⊤))ˣ) :
    𝟭 (AsSmall.{0} (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) ≅
      𝟭 (AsSmall.{0} (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :=
  lift (AsSmall.down : AsSmall.{0}
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory)
    (boundedAboveFlatPerfectGlobalUnitIso Y r)

end ProductSwapUnit

namespace GlobalUnitIdentityOperation

/-- The original scalar action on the scheme's unchanged nonnegative K-group. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:40-47"
  "adaptation" "Original global scalar K-operation, including degree zero."]
def unitKOperation (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    boundedAboveFlatPerfectK X.toRingedSpace n →*
      boundedAboveFlatPerfectK X.toRingedSpace (n + 1) :=
  originalKSelfTrackOperation (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (prespectrumIsoHomotopy
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (ProductSwapUnit.smallUnit X r)) n

end GlobalUnitIdentityOperation

namespace ProductUnitInterchange
open GlobalUnitIdentityOperation

set_option maxRecDepth 4000 in
/-- Two genuine scalar actions anticommute on every original nonnegative K-class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:35-41"
  "adaptation" "Original geometric scalar identity-action sign in all nonnegative degrees."]
theorem unitKOperation_interchange_sign (X : Scheme.{u}) (r s : (Γ(X, ⊤))ˣ)
    (n : ℕ) (a : boundedAboveFlatPerfectK X.toRingedSpace n) :
    unitKOperation X s (n + 1) (unitKOperation X r n a) =
      (unitKOperation X r (n + 1) (unitKOperation X s n a))⁻¹ :=
  originalKIdentityAction_interchange_sign (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (ProductSwapUnit.smallUnit X r) (ProductSwapUnit.smallUnit X s) n a

end ProductUnitInterchange
end AlgebraicGeometry.Scheme.Modules
