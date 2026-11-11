/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.ConeConeTranspose
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.ConeConeTranspose
variable {E F G H : LoopPrespectrum.{u}} (f : E ⟶ F) (g : G ⟶ H)
  (a : E ⟶ G) (b : F ⟶ H) (h : a ≫ g = f ≫ b)

example (n : ℕ) (y : H.space n) :
    (hom f g a b h).map n ((mappingConeInclusion (horizontal f g a b h)).map n
      ((mappingConeInclusion g).map n y)) =
        (mappingConeInclusion (vertical f g a b h)).map n
          ((mappingConeInclusion b).map n y) :=
  hom_inclusion_inclusion f g a b h n y

example (n : ℕ) (s : unitInterval) (z : G.space n) :
    (hom f g a b h).map n ((mappingConeInclusion (horizontal f g a b h)).map n
      (ReducedMappingCone.cylinder (G.point n) (H.point n) (g.map n) (s, z))) =
        ReducedMappingCone.cylinder ((mappingCone a).point n) ((mappingCone b).point n)
          ((vertical f g a b h).map n) (s, (mappingConeInclusion a).map n z) :=
  hom_inclusion_cylinder f g a b h n s z

example (n : ℕ) (r : unitInterval) (y : F.space n) :
    (hom f g a b h).map n
      (ReducedMappingCone.cylinder ((mappingCone f).point n) ((mappingCone g).point n)
        ((horizontal f g a b h).map n) (r, (mappingConeInclusion f).map n y)) =
          (mappingConeInclusion (vertical f g a b h)).map n
            (ReducedMappingCone.cylinder (F.point n) (H.point n) (b.map n) (r, y)) :=
  hom_cylinder_inclusion f g a b h n r y

example (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (hom f g a b h).map n
      (ReducedMappingCone.cylinder ((mappingCone f).point n) ((mappingCone g).point n)
        ((horizontal f g a b h).map n)
        (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x))) =
          ReducedMappingCone.cylinder ((mappingCone a).point n) ((mappingCone b).point n)
            ((vertical f g a b h).map n)
            (s, ReducedMappingCone.cylinder (E.point n) (G.point n) (a.map n) (r, x)) :=
  hom_cylinder_cylinder f g a b h n r s x

example :
    hom f g a b h ≫ hom a b f g h.symm = 𝟙 (mappingCone (horizontal f g a b h)) :=
  hom_comp_transpose f g a b h

example : mappingCone (horizontal f g a b h) ≅ mappingCone (vertical f g a b h) :=
  iso f g a b h

end Topology.LoopPrespectrum.ConeConeTranspose
end
