/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# Pullback of the difference sheaf of Cartier divisors

The signs and order are fixed by the actual module `𝒪(D) ⊗ 𝒪(-E)`.
The comparison uses the native pullback tensor comparison and the two native
Cartier sheaf comparisons. The morphism need not be flat.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- The actual module `𝒪(D) ⊗ 𝒪(-E)`, with this order and sign convention. -/
def differenceSheaf {X : Scheme.{u}} (D E : X.IdealSheafData) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
    (invertibleSheaf' D)).obj (negativeTwist' E)

/-- Pullback of a Cartier divisor difference, on the actual sheaves of modules.
Both inverse images are required to be Cartier; no flatness of the pullback map is assumed. -/
@[stacks 0C4U "Pullback of the positive divisor sheaf in a divisor difference",
  stacks 01CD "The actual tensor comparison used for the divisor difference"]
def differenceSheafPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D E : Y.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f D] [IsPullbackDefined f E] :
    (Scheme.Modules.pullback f).obj (differenceSheaf D E) ≅
      differenceSheaf (D.comap f) (E.comap f) :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).mapIso
      (invertibleSheafPullbackIso f D)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
      (invertibleSheaf' (D.comap f))).mapIso
        (pullbackIdealSheafComapIso f E inferInstance)

end Stacks.Divisors
