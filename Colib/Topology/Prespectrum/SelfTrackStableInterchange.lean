/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackInterchange
public import Colib.Topology.Prespectrum.SelfTrackNonnegativeStage
public import Colib.Topology.Prespectrum.StableOmega

/-!
# Stable interchange of independent self-tracks

The finite interchange sign passes through the actual nonnegative stage-zero
inclusion. Only the source prespectrum is assumed to be an Omega-spectrum,
so every source stable class has an actual stage-zero representative. Both
operations retain their original normalization and stable comparison maps.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackStableInterchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable {E F G K : LoopPrespectrum.{u}}
variable {f : E ⟶ F} {g : E ⟶ G} {f' : G ⟶ K} {g' : F ⟶ K}

/-- Actual pointwise interchange gives the nonnegative stable anti-commutation sign. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableInterchange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_interchange_sign
    (H : Homotopy f f) (J : Homotopy g g)
    (H' : Homotopy f' f') (J' : Homotopy g' g')
    (h : ∀ n s t x, H'.level n (s, J.level n (t, x)) =
      J'.level n (t, H.level n (s, x)))
    (hE : E.IsOmega) (n : ℕ) (a : stableHomotopyGroup E (n : ℤ)) :
    J'.stableOperation ((n + 1 : ℕ) : ℤ) (H.stableOperation (n : ℤ) a) =
      -(H'.stableOperation ((n + 1 : ℕ) : ℤ) (J.stableOperation (n : ℤ) a)) := by
  let b := (nonnegativeStableStageEquiv E n).symm
    ((stableHomotopyStageZeroIso E hE (n : ℤ)).hom a)
  have ha : stableHomotopyι E (n : ℤ) 0 (nonnegativeStableStageEquiv E n b) = a := by
    dsimp only [b]
    rw [AddEquiv.apply_symm_apply, ← stableHomotopyStageZeroIso_inv E hE]
    exact ConcreteCategory.congr_hom (Iso.hom_inv_id (stableHomotopyStageZeroIso E hE _)) a
  rw [← ha]
  change J'.stableOperation ((n + 1 : ℕ) : ℤ)
      (H.stableOperation (n : ℤ)
        (stableHomotopyι E (n : ℤ) 0
          (nonnegativeStableStageEquiv E n (Additive.ofMul (Additive.toMul b))))) =
    -(H'.stableOperation ((n + 1 : ℕ) : ℤ)
      (J.stableOperation (n : ℤ)
        (stableHomotopyι E (n : ℤ) 0
          (nonnegativeStableStageEquiv E n (Additive.ofMul (Additive.toMul b))))))
  rw [H.stableOperation_nonnegative_stage, J'.stableOperation_nonnegative_stage,
    J.stableOperation_nonnegative_stage, H'.stableOperation_nonnegative_stage,
    H.homotopyClassOperation_interchange_sign J H' J' h]
  change stableHomotopyι K ((n + 2 : ℕ) : ℤ) 0
      (nonnegativeStableStageEquiv K (n + 2) (-Additive.ofMul _)) = _
  rw [map_neg, map_neg]
  rfl

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.stableOperation_interchange_sign
