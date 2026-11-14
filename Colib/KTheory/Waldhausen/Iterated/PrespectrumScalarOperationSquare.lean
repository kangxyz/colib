/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIntertwiningHomotopy
public import Colib.Topology.Prespectrum.SelfTrackIntertwining
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-! # Stable operations of a commuting scalar square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- A genuine scalar square on the original exact models intertwines their stable operations. -/
theorem prespectrumTransformation_stableOperation_square
    {V W T U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (i : (F ≫ b).hom.toFunctor ⟶ (a ≫ G).hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hi : ∀ X, U.obj.waldhausen.weq (i.app X))
    (he : whiskerRight η b.hom.toFunctor ≫ i = i ≫ whiskerLeft a.hom.toFunctor θ) (d : ℤ) :
    (prespectrumTransformationHomotopy η hη).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (prespectrumMap b) =
      (stableHomotopyFunctor d).map (prespectrumMap a) ≫
        (prespectrumTransformationHomotopy θ hθ).stableOperation d := by
  have h := Homotopy.stableOperation_intertwine _ _ _
    (prespectrumTransformationIntertwiningHomotopy F G a b η θ i hη hθ hi he) d
  exact ((prespectrumTransformationHomotopy η hη).stableOperation_postcomp
    (prespectrumMap b) d).symm.trans (h.trans
      ((prespectrumTransformationHomotopy θ hθ).stableOperation_precomp (prespectrumMap a) d))

end CategoryTheory.Waldhausen.IteratedS
