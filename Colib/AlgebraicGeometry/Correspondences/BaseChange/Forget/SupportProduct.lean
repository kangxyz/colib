/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Incidence

/-!
# The actual support-product open square after forgetting an unramified base

The original support product maps to the forgotten support product by first
forgetting its base and then applying the two original component isomorphisms.
This is an actual open immersion for an unramified finite-type base map.
Together with the ambient and triple-product maps it supplies the literal open
squares for the existing stalk Tor comparison.

Adapted from motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Incidence.lean`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T) [IsSeparated r]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The support isomorphisms compare the actual two products over the smaller base. -/
def forgetBaseSupportProductFactorsMap :
    pullback (((integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g) ≫ r)
      (((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ g) ≫ r) ⟶
      correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) :=
  pullback.map _ _ _ _ (forgetBaseSupportIso r f g z).hom
    (forgetBaseSupportIso r g h w).hom (𝟙 S) (by simp) (by simp)

instance : IsIso (forgetBaseSupportProductFactorsMap r f g h z w) := by
  unfold forgetBaseSupportProductFactorsMap
  infer_instance

/-- The actual coefficient scheme maps by the separated-base inclusion and support isomorphisms. -/
def forgetBaseSupportProductMap :
    correspondenceSupportProduct f g h z w ⟶
      correspondenceSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) :=
  forgetBaseProductMap r
    ((integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ g) ≫
      forgetBaseSupportProductFactorsMap r f g h z w

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseSupportProductMap r f g h z w) := by
  unfold forgetBaseSupportProductMap
  infer_instance

@[reassoc (attr := simp)]
theorem forgetBaseSupportProductMap_fst :
    forgetBaseSupportProductMap r f g h z w ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (forgetBaseSupportIso r f g z).hom := by
  simp [forgetBaseSupportProductMap, forgetBaseSupportProductFactorsMap]

@[reassoc (attr := simp)]
theorem forgetBaseSupportProductMap_snd :
    forgetBaseSupportProductMap r f g h z w ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (forgetBaseSupportIso r g h w).hom := by
  simp [forgetBaseSupportProductMap, forgetBaseSupportProductFactorsMap]

/-- The two actual support inclusions form a square with the actual ambient comparison. -/
theorem forgetBaseSupportProduct_square :
    forgetBaseSupportProductMap r f g h z w ≫
        correspondenceSupportProductInclusion (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) =
      correspondenceSupportProductInclusion f g h z w ≫ forgetBaseAmbientMap r f g h := by
  apply pullback.hom_ext <;> simp

/-- The original incidence point has the same actual image in the coefficient scheme. -/
@[reassoc]
theorem forgetBaseIncidenceMap_supportProduct :
    forgetBaseIncidenceMap r f g h z w ≫
        correspondenceIncidenceToSupportProduct (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) =
      correspondenceIncidenceToSupportProduct f g h z w ≫
        forgetBaseSupportProductMap r f g h z w := by
  apply pullback.hom_ext <;> simp

end Stacks.Chow
