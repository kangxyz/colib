/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationLevelOne
public import Colib.Topology.Prespectrum.SelfTrackPath

/-!
# Original K-zero evaluation on a supplied actual path

An explicit original small-model representative equality identifies the
K-zero input with a supplied based path. The level-one successor inverse
and the literal track/spatial normalization inverse then cancel. The result
is the forward original K-one normalization of the actual path self-track.
No representative is selected, and no geometric scalar value is assumed.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SelfTrackKOperationPath.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- On the supplied original K-zero representative, the two proved inverse signs cancel. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_path (H : Homotopy f f) (a : W.K 0)
    (γ : Path ((originalPrespectrum W).point 1) ((originalPrespectrum W).point 1))
    (hγ : W.asSmallKEquiv 0 a = ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧) :
    V.asSmallKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      loopKOneNormalization (basedLoopMap (f.map 1) (f.map_point 1) γ)
        (FundamentalGroup.fromPath ⟦H.pathSelfTrack 1 γ⟧) := by
  rw [originalKSelfTrackOperation_levelOne, hγ]
  exact (congrArg
    (fun b : HomotopyGroup.Pi 2 ((originalPrespectrum V).space 1)
      ((originalPrespectrum V).point 1) ↦ b⁻¹)
    (H.homotopyClassOperation_finOne 1 γ)).trans (inv_inv _)

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0321"]
  CategoryTheory.Waldhausen.IteratedS.originalKSelfTrackOperation_path
