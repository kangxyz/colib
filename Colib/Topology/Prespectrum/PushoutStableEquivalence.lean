/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.PushoutCollapseNaturality
public import Colib.Topology.Prespectrum.ConeStableDetection
public import Colib.Topology.Prespectrum.PositiveLevelEquivalence

/-!
# Genuine stable preservation for the original reduced-pushout map

The original C-cone collapse and its strict naturality compare the actual right-inclusion
cone map to the cone map of the original left attaching arrows. Genuine signed cone sequences
then detect stability of the unchanged pushout map. The generic statement retains actual
point HEP and genuine row-excision hypotheses, rather than assuming complete weak side maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- Original row excision and stable original corners preserve the exact reduced-pushout map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutStableEquivalence.lean:32"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem map_isStableEquivalence_of_excision
    (hA : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + 1)))))
    (hB : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + 1)))))
    (hC : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + 1)))))
    (hA' : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A'.point (n + 1)))))
    (hB' : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B'.point (n + 1)))))
    (hC' : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C'.point (n + 1)))))
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hf' : IsStableEquivalence (mappingConeFiberComparison f'))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hi' : IsStableEquivalence (mappingConeFiberComparison (inr f' g')))
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (hc : IsStableEquivalence c) :
    IsStableEquivalence (map f g f' g' a b c wf wg) := by
  have hcol : IsStableEquivalence (rightConeCollapse f g) :=
    isStableEquivalence_of_positiveLevel _ (fun n ↦
      rightConeCollapse_level_isWeakHomotopyEquivalence f g (n + 1) (hA n) (hB n) (hC n))
  have hcol' : IsStableEquivalence (rightConeCollapse f' g') :=
    isStableEquivalence_of_positiveLevel _ (fun n ↦
      rightConeCollapse_level_isWeakHomotopyEquivalence f' g' (n + 1) (hA' n) (hB' n) (hC' n))
  have hleft : IsStableEquivalence
      (mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk f') a b wf.symm)) :=
    mappingConeMap_isStableEquivalence_of_excision _ hf hf' ha hb
  have hcomp := hcol.comp hleft
  rw [← rightConeCollapse_naturality f g f' g' a b c wf wg] at hcomp
  have hright : IsStableEquivalence
      (mappingConeMap (rightInclusionSquare f g f' g' a b c wf wg)) := by
    intro d
    let := hcol' d
    let : IsIso ((stableHomotopyFunctor d).map
        (mappingConeMap (rightInclusionSquare f g f' g' a b c wf wg)) ≫
          (stableHomotopyFunctor d).map (rightConeCollapse f' g')) := by
      simpa only [Functor.map_comp] using hcomp d
    exact IsIso.of_isIso_comp_right
      ((stableHomotopyFunctor d).map
        (mappingConeMap (rightInclusionSquare f g f' g' a b c wf wg)))
      ((stableHomotopyFunctor d).map (rightConeCollapse f' g'))
  exact right_isStableEquivalence_of_coneMap
    (rightInclusionSquare f g f' g' a b c wf wg) hi hi' hc hright

end Topology.LoopPrespectrum.HomotopyPushout
