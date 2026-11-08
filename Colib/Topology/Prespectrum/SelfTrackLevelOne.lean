/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackNonnegativeStage
public import Colib.Topology.Prespectrum.SelfTrackSuccessorPositive
public import Colib.Topology.Prespectrum.StableLevelOne

/-!
# The original level-one self-track comparison and its sign

The original stable comparison first uses the level-one structure map.
Consequently the transported operation is the inverse of the literal
level-one finite self-track operation. The positive successor theorem includes
input degree one; no additivity assumption in that degree is introduced.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackLevelOne.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The unchanged level-one stable comparison retains the actual successor inverse sign. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackLevelOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_levelOne (H : Homotopy f f)
    (hE : E.IsOmega) (hF : F.IsOmega) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) :
    H.stableOperation (n : ℤ) (levelOneStableEquiv E hE n (Additive.ofMul a)) =
      levelOneStableEquiv F hF (n + 1)
        (Additive.ofMul ((H.homotopyClassOperation 1 n a)⁻¹)) := by
  rw [levelOneStableEquiv_apply, levelOneStableEquiv_apply]
  change H.stableOperation (n : ℤ)
      (stableHomotopyι E (n : ℤ) 0
        (nonnegativeStableStageEquiv E n (Additive.ofMul (structurePiMap E 1 n a)))) =
    stableHomotopyι F ((n + 1 : ℕ) : ℤ) 0
      (nonnegativeStableStageEquiv F (n + 1)
        (Additive.ofMul (structurePiMap F 1 (n + 1)
          ((H.homotopyClassOperation 1 n a)⁻¹))))
  rw [H.stableOperation_nonnegative_stage,
    H.homotopyClassOperation_structure_sign_positive,
    ← (structurePiMap F 1 (n + 1)).map_inv (H.homotopyClassOperation 1 n a)]

end Topology.LoopPrespectrum
