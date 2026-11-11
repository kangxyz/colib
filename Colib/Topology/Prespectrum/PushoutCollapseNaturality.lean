/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.PushoutConeCollapse

/-!
# Original strict-span naturality of the actual right-cone collapse

An unchanged strict span map gives its actual square of original C inclusions. Its existing
cone map commutes strictly with the genuine C-cone collapse and the original cone map of the
left attaching arrow. Every original target and cylinder coordinate is retained.
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

/-- The unchanged span map and C side form the original strict right-inclusion square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutCollapseNaturality.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def rightInclusionSquare : Arrow.mk (inr f g) ⟶ Arrow.mk (inr f' g') :=
  Arrow.homMk c (map f g f' g' a b c wf wg) (inr_map f g f' g' a b c wf wg).symm

/-- The original cone collapse commutes with the entire original strict span map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutCollapseNaturality.lean:34"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem rightConeCollapse_naturality :
    mappingConeMap (rightInclusionSquare f g f' g' a b c wf wg) ≫ rightConeCollapse f' g' =
      rightConeCollapse f g ≫
        mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk f') a b wf.symm) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext
      funext n
      ext x
      exact ((mappingConeMap
        (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk f') a b wf.symm)).map_point n).symm
    · intro n s x; rfl
  · intro n s x
    exact ((mappingConeMap
      (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk f') a b wf.symm)).map_point n).symm

end Topology.LoopPrespectrum.HomotopyPushout
