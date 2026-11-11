/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.PushoutConeInterchange
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : Arrow LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

example : prespectrum f.left g.left ⟶ prespectrum f.right g.right :=
  spanArrowMap f g

example :
    coneInterchange f g ≫ coneInterchangeInv f g = 𝟙 (mappingCone (spanArrowMap f g)) :=
  coneInterchange_hom_inv f g

example :
    coneInterchangeInv f g ≫ coneInterchange f g =
      𝟙 (prespectrum (mappingConeMap f) (mappingConeMap g)) :=
  coneInterchange_inv_hom f g

example : mappingCone (spanArrowMap f g) ≅
    prespectrum (mappingConeMap f) (mappingConeMap g) :=
  coneInterchangeIso f g

example :
    mappingConeInclusion (spanArrowMap f g) ≫ coneInterchange f g = coneInterchangeTarget f g :=
  coneInterchange_inclusion f g

example (n : ℕ) (r s : unitInterval) (x : A.left.space n) :
    (coneInterchange f g).map n
      (ReducedMappingCone.cylinder ((prespectrum f.left g.left).point n)
        ((prespectrum f.right g.right).point n) ((spanArrowMap f g).map n)
        (r, cylinder f.left g.left n (s, x))) =
      cylinder (mappingConeMap f) (mappingConeMap g) n
        (s, ReducedMappingCone.cylinder (A.left.point n) (A.right.point n) (A.hom.map n)
          (r, x)) :=
  coneInterchange_doubleCylinder f g n r s x

end Topology.LoopPrespectrum.HomotopyPushout
end
