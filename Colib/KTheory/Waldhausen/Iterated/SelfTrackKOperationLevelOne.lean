/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperation
public import Colib.Topology.Prespectrum.SelfTrackLevelOne

/-!
# The finite original K-group representative of a self-track operation

The small-model comparison and the original level-one structure map identify
the transported operation with the inverse of the literal finite self-track
class. In particular the statement includes original K-zero. A comparison
with a separately defined forward scalar class is not assumed.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SelfTrackKOperationLevelOne.lean`
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
variable (W : Structure C) (V : Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The actual original K-class is the inverse level-one normalized track class. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationLevelOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_levelOne (H : Homotopy f f) (n : ℕ) (a : W.K n) :
    V.asSmallKEquiv (n + 1) (originalKSelfTrackOperation W V H n a) =
      (H.homotopyClassOperation 1 n (W.asSmallKEquiv n a))⁻¹ := by
  have h := originalKSelfTrackOperation_stable W V H n a
  change levelOneStableEquiv (originalPrespectrum V) (originalPrespectrum_isOmega V) (n + 1)
      (Additive.ofMul (V.asSmallKEquiv (n + 1) (originalKSelfTrackOperation W V H n a))) =
    H.stableOperation (n : ℤ)
      (levelOneStableEquiv (originalPrespectrum W) (originalPrespectrum_isOmega W) n
        (Additive.ofMul (W.asSmallKEquiv n a))) at h
  rw [H.stableOperation_levelOne (originalPrespectrum_isOmega W)
    (originalPrespectrum_isOmega V) n (W.asSmallKEquiv n a)] at h
  exact (levelOneStableEquiv (originalPrespectrum V)
    (originalPrespectrum_isOmega V) (n + 1)).injective h

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0321"]
  CategoryTheory.Waldhausen.IteratedS.originalKSelfTrackOperation_levelOne
