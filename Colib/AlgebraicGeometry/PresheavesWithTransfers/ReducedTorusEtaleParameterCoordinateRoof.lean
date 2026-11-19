/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleDerivedProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterAW
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterReindex

/-! # Coordinate insertion through the actual parameter AW roof

This is the missing coordinate cancellation, before signed endpoint transport.
The numerator uses the original coordinate insertion followed by parameter-reindexed
AW. The denominator is that same AW, proved invertible after exact presheaf
reindexing and sheafification. Cancelling it returns the literal insertion/pairing
composite occurring in `reducedTorusEtaleParameterSquare_reindex`; no sheaf
parameter functor is applied to an already localized inverse.

The one-way reindex/sheafification comparison, coefficient forgetting, topology
change and native signed placement remain separate comparisons. They are not
inverted or replaced by identities here.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{v} (SmoothEtaleIntegralSheaves k)]

/-- The concrete coordinate numerator and inverse-AW roof give exactly the original
chain insertion/pairing composite, with presheaf parameter reindexing retained. -/
theorem reducedTorusEtaleParameterCoordinateRoof_eq (q : ℕ) :
    ((integralEtaleChainToDerived k).map (reducedTorusChainCoordinateInsertion k q) ≫
        (integralEtaleParameterChainToDerived k).map (reducedTorusPresheafAW k q)) ≫
      (inv ((integralEtaleParameterChainToDerived k).map (reducedTorusPresheafAW k q)) ≫
        (integralEtaleParameterChainToDerived k).map (reducedTorusPresheafChainPairing k q)) =
      (integralEtaleChainToDerived k).map (reducedTorusChainCoordinateInsertion k q ≫
        ((reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)).map
          (reducedTorusPresheafChainPairing k q)) := by
  have cancelRoof {W X Y Z : DerivedCategory (SmoothEtaleIntegralSheaves k)}
      (u : W ⟶ X) (d : X ⟶ Y) [IsIso d] (p : X ⟶ Z) :
      (u ≫ d) ≫ (inv d ≫ p) = u ≫ p := by
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (@cancelRoof _ _ _ _
    ((integralEtaleChainToDerived k).map (reducedTorusChainCoordinateInsertion k q))
    ((integralEtaleParameterChainToDerived k).map (reducedTorusPresheafAW k q))
    (reducedTorusEtaleParameterDerivedAW_isIso k q)
    ((integralEtaleParameterChainToDerived k).map (reducedTorusPresheafChainPairing k q))).trans
      ((integralEtaleChainToDerived k).map_comp _ _).symm

end AlgebraicGeometry.PresheafWithTransfers
