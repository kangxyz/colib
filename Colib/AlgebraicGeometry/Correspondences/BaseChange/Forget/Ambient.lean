/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Support
public import Colib.AlgebraicGeometry.Correspondences.Composition.Diagonal

/-! # Original incidence geometry under forgetting an unramified base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow
open AlgebraicGeometry.Scheme

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T)

/-- Forget the base on the two adjacent products, keeping the common middle object. -/
def forgetBaseTripleMap : correspondenceTripleProduct f g h ⟶
    correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r) :=
  pullback.map _ _ _ _ (forgetBaseProductMap r f g) (forgetBaseProductMap r g h)
    (𝟙 Y) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem forgetBaseTripleMap_fst :
    forgetBaseTripleMap r f g h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ forgetBaseProductMap r f g := by
  simp [forgetBaseTripleMap]

@[reassoc (attr := simp)]
theorem forgetBaseTripleMap_snd :
    forgetBaseTripleMap r f g h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ forgetBaseProductMap r g h := by
  simp [forgetBaseTripleMap]

/-- The second part of the four-factor ambient map, after forgetting its outer base. -/
def forgetBaseAmbientFactorsMap :
    pullback ((pullback.snd f g ≫ g) ≫ r) ((pullback.fst g h ≫ g) ≫ r) ⟶
      correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r) :=
  pullback.map _ _ _ _ (forgetBaseProductMap r f g) (forgetBaseProductMap r g h)
    (𝟙 S) (by simp) (by simp)

/-- The actual four-factor ambient comparison. -/
def forgetBaseAmbientMap : correspondenceIntersectionAmbient f g h ⟶
    correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r) :=
  forgetBaseProductMap r (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
    forgetBaseAmbientFactorsMap r f g h

@[reassoc (attr := simp)]
theorem forgetBaseAmbientMap_fst :
    forgetBaseAmbientMap r f g h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ forgetBaseProductMap r f g := by
  simp [forgetBaseAmbientMap, forgetBaseAmbientFactorsMap]

@[reassoc (attr := simp)]
theorem forgetBaseAmbientMap_snd :
    forgetBaseAmbientMap r f g h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ forgetBaseProductMap r g h := by
  simp [forgetBaseAmbientMap, forgetBaseAmbientFactorsMap]

/-- The literal diagonal intersection square commutes. -/
theorem forgetBaseTripleInclusion_square :
    forgetBaseTripleMap r f g h ≫ correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r) =
      correspondenceTripleInclusion f g h ≫ forgetBaseAmbientMap r f g h := by
  apply pullback.hom_ext <;> simp

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseTripleMap r f g h) := by
  unfold forgetBaseTripleMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r f g)))
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r g h))) (by simp) (by simp)

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseAmbientFactorsMap r f g h) := by
  unfold forgetBaseAmbientFactorsMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r f g)))
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r g h))) (by simp) (by simp)

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseAmbientMap r f g h) := by
  unfold forgetBaseAmbientMap
  infer_instance

end Stacks.Chow
