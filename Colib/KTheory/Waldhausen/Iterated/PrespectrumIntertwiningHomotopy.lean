/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Whole original transformation tracks across a Model comparison

An actual intertwining equation gives the relative comparison of the original postwhiskered
and prewhiskered loops across the unchanged comparison track. All levels, including original
zero-level loops, and independent structure parameters are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- A genuine transformation square preserves the original two whole track pastings. -/
def prespectrumTransformationIntertwiningHomotopy {V W T U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (θ : G.hom.toFunctor ⟶ G.hom.toFunctor)
    (i : (F ≫ b).hom.toFunctor ⟶ (a ≫ G).hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.obj.waldhausen.weq (θ.app X))
    (hi : ∀ X, U.obj.waldhausen.weq (i.app X))
    (he : whiskerRight η b.hom.toFunctor ≫ i = i ≫ whiskerLeft a.hom.toFunctor θ) :
    (((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap b)).trans
      ((prespectrumTransformationHomotopy i hi).cast
        (prespectrumFunctor.map_comp F b) (prespectrumFunctor.map_comp a G))).RelHomotopy
    (((prespectrumTransformationHomotopy i hi).cast
      (prespectrumFunctor.map_comp F b) (prespectrumFunctor.map_comp a G)).trans
        (Homotopy.precomp (prespectrumMap a) (prespectrumTransformationHomotopy θ hθ))) := by
  let J := prespectrumTransformationPastingHomotopy
    (F := F ≫ b) (G := F ≫ b) (G' := a ≫ G) (H := a ≫ G)
    (whiskerRight η b.hom.toFunctor) i i (whiskerLeft a.hom.toFunctor θ)
    (fun X ↦ b.hom.isExact.weak _ (hη X)) hi hi (fun X ↦ hθ (a.hom.toFunctor.obj X)) he
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · exact (prespectrumTransformationHomotopy_postcomp_level η hη b n).symm
    · rfl
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (prespectrumTransformationHomotopy_precomp_level θ hθ a n).symm

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/PrespectrumIntertwiningHomotopy.lean:27-53"
  "adaptation" "Original whole transformation tracks across an actual native small-model square"]
  CategoryTheory.Waldhausen.IteratedS.prespectrumTransformationIntertwiningHomotopy
