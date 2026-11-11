/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeMapHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Transposing the two original cone coordinates

A strictly commuting square of loop prespectra gives a literal isomorphism between the cone
of its horizontal cone map and the cone of its vertical cone map. The target face is an actual
mapping-cone map. Its whole source nullhomotopy is obtained from the original two side-cone
homotopies through `mappingConeMapHomotopy`, so quotient descent precedes interval evaluation.

The four original quotient-generator formulas are retained. On the doubly cylindrical
stratum, transposition swaps the two cone coordinates, keeping the structure-loop parameter
independent. Transposing the original square a second time gives a strict inverse.

This is a point-set isomorphism of the actual prespectra. Swapping two cone coordinates is
orientation-sensitive; no equality of iterated signed boundary maps is asserted here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.ConeConeTranspose

variable {E F G H : LoopPrespectrum.{u}} (f : E ⟶ F) (g : G ⟶ H)
  (a : E ⟶ G) (b : F ⟶ H) (h : a ≫ g = f ≫ b)

/-- The original cone map of the square, with the horizontal arrows forming its two cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:40"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def horizontal : mappingCone f ⟶ mappingCone g :=
  mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk g) a b h)

/-- The original cone map of the transposed square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:44"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def vertical : mappingCone a ⟶ mappingCone b :=
  mappingConeMap (Arrow.homMk (f := Arrow.mk a) (g := Arrow.mk b) f g h.symm)

/-- The original target inclusions form a strict square into the vertical cone map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:48"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def targetSquare : Arrow.mk g ⟶ Arrow.mk (vertical f g a b h) :=
  Arrow.homMk (mappingConeInclusion a) (mappingConeInclusion b) (by
    apply Hom.ext
    funext n
    ext z
    rfl)

/-- The target face of the transposition is an actual map of the original quotient cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:56"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def target : mappingCone g ⟶ mappingCone (vertical f g a b h) :=
  mappingConeMap (targetSquare f g a b h)

/-- The original side cylinders descend together to the whole source nullhomotopy.
Their all-time square is the literal cylinder formula of the vertical cone map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:61"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def nullHomotopy :
    Homotopy (horizontal f g a b h ≫ target f g a b h)
      (zeroHom (mappingCone f) (mappingCone (vertical f g a b h))) :=
  (mappingConeMapHomotopy
    (s := (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk g) a b h) ≫
      targetSquare f g a b h)
    (t := Arrow.homMk (zeroHom E (mappingCone a)) (zeroHom F (mappingCone b)) (by
      apply Hom.ext
      funext n
      ext x
      exact (vertical f g a b h).map_point n))
    (mappingConeHomotopy a) (mappingConeHomotopy b) (by intro n r x; rfl)).cast
    (by
      apply mappingCone_hom_ext
      · apply Hom.ext
        funext n
        ext y
        rfl
      · intro n r x
        rfl)
    (by
      apply mappingCone_hom_ext
      · apply Hom.ext
        funext n
        ext y
        rfl
      · intro n r x
        exact ReducedMappingCone.cylinder_base ((mappingCone a).point n)
          ((mappingCone b).point n) ((vertical f g a b h).map n) r)

/-- Transpose the original double cone by its actual target face and whole source nullhomotopy. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:92"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def hom : mappingCone (horizontal f g a b h) ⟶ mappingCone (vertical f g a b h) :=
  mappingConeDesc (horizontal f g a b h) (target f g a b h) (nullHomotopy f g a b h)

/-- The double target is unchanged by transposition. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:96"
  "adaptation" "Original double-cone isomorphism and all four quotient strata.", simp]
theorem hom_inclusion_inclusion (n : ℕ) (y : H.space n) :
    (hom f g a b h).map n ((mappingConeInclusion (horizontal f g a b h)).map n
      ((mappingConeInclusion g).map n y)) =
        (mappingConeInclusion (vertical f g a b h)).map n
          ((mappingConeInclusion b).map n y) := rfl

/-- A cylinder in the original target cone becomes the outer cylinder of the transposed cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:103"
  "adaptation" "Original double-cone isomorphism and all four quotient strata.", simp]
theorem hom_inclusion_cylinder (n : ℕ) (s : unitInterval) (z : G.space n) :
    (hom f g a b h).map n ((mappingConeInclusion (horizontal f g a b h)).map n
      (ReducedMappingCone.cylinder (G.point n) (H.point n) (g.map n) (s, z))) =
        ReducedMappingCone.cylinder ((mappingCone a).point n) ((mappingCone b).point n)
          ((vertical f g a b h).map n) (s, (mappingConeInclusion a).map n z) := rfl

/-- An outer cylinder on the source target becomes the inner cylinder of the transposed cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:110"
  "adaptation" "Original double-cone isomorphism and all four quotient strata.", simp]
theorem hom_cylinder_inclusion (n : ℕ) (r : unitInterval) (y : F.space n) :
    (hom f g a b h).map n
      (ReducedMappingCone.cylinder ((mappingCone f).point n) ((mappingCone g).point n)
        ((horizontal f g a b h).map n) (r, (mappingConeInclusion f).map n y)) =
          (mappingConeInclusion (vertical f g a b h)).map n
            (ReducedMappingCone.cylinder (F.point n) (H.point n) (b.map n) (r, y)) := rfl

/-- On the original double cylinder, the two independent cone coordinates are swapped. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:118"
  "adaptation" "Original double-cone isomorphism and all four quotient strata.", simp]
theorem hom_cylinder_cylinder (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (hom f g a b h).map n
      (ReducedMappingCone.cylinder ((mappingCone f).point n) ((mappingCone g).point n)
        ((horizontal f g a b h).map n)
        (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x))) =
          ReducedMappingCone.cylinder ((mappingCone a).point n) ((mappingCone b).point n)
            ((vertical f g a b h).map n)
            (s, ReducedMappingCone.cylinder (E.point n) (G.point n) (a.map n) (r, x)) := rfl

/-- Transposing the original square twice is the identity on all four quotient strata. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:128"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
theorem hom_comp_transpose :
    hom f g a b h ≫ hom a b f g h.symm = 𝟙 (mappingCone (horizontal f g a b h)) := by
  apply mappingCone_hom_ext
  · apply mappingCone_hom_ext
    · apply Hom.ext
      funext n
      ext y
      rfl
    · intro n s z
      rfl
  · intro n r p
    induction p using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z => rfl

/-- The actual cones of the two original cone maps are strictly isomorphic.
This isomorphism retains the coordinate swap and makes no signed-boundary assertion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeConeTranspose.lean:146"
  "adaptation" "Original double-cone isomorphism and all four quotient strata."]
def iso : mappingCone (horizontal f g a b h) ≅ mappingCone (vertical f g a b h) where
  hom := hom f g a b h
  inv := hom a b f g h.symm
  hom_inv_id := hom_comp_transpose f g a b h
  inv_hom_id := hom_comp_transpose a b f g h.symm

end Topology.LoopPrespectrum.ConeConeTranspose
