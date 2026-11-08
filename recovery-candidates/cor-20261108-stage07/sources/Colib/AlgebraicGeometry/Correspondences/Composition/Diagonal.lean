/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Embedding

/-!
# The actual middle diagonal and product support

The four-factor ambient scheme is the product of the two adjacent products over
the base. The triple product enters by the native `pullback.mapDesc`, the base
change of the middle diagonal. The product of the full integral supports enters
by the native closed pullback map. The incidence maps to both, and the square
commutes as scheme morphisms, retaining nilpotents and actual stalk maps.

Source: motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean.
Native mathematical supplier: Mathlib `pullback_map_diagonal_isPullback` and
`IsSeparated`'s closed-immersion instance for `pullback.mapDesc`.
This recovery leaf only restores the displayed actual geometry; it does not yet
claim restoration of every historical ideal-kernel or Cartesian-square theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The actual product of adjacent products over the base. -/
abbrev correspondenceIntersectionAmbient : Scheme.{u} :=
  pullback (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)

/-- The actual middle-diagonal inclusion. -/
def correspondenceTripleInclusion :
    correspondenceTripleProduct f g h ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.mapDesc (pullback.snd f g) (pullback.fst g h) g

instance isClosedImmersion_correspondenceTripleInclusion [IsSeparated g] :
    IsClosedImmersion (correspondenceTripleInclusion f g h) := by
  unfold correspondenceTripleInclusion
  infer_instance

/-- The actual product of the two full integral support schemes. -/
abbrev correspondenceSupportProduct
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) : Scheme.{u} :=
  pullback ((integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ g)

/-- The actual product-support closed inclusion in the four-factor ambient. -/
def correspondenceSupportProductInclusion
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceSupportProduct f g h z w ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.map _ _ _ _ (integralComponentAt z).subschemeι
    (integralComponentAt w).subschemeι (𝟙 S) (by simp) (by simp)

instance isClosedImmersion_correspondenceSupportProductInclusion
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    IsClosedImmersion (correspondenceSupportProductInclusion f g h z w) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance rfl rfl

/-- The incidence maps to the actual product of its two integral supports. -/
def correspondenceIncidenceToSupportProduct
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidence f g h z w ⟶ correspondenceSupportProduct f g h z w :=
  pullback.mapDesc ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h) g

instance isClosedImmersion_correspondenceIncidenceToSupportProduct [IsSeparated g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    IsClosedImmersion (correspondenceIncidenceToSupportProduct f g h z w) := by
  unfold correspondenceIncidenceToSupportProduct
  infer_instance

/-- The middle diagonal preserves the left adjacent product. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleInclusion_fst :
    correspondenceTripleInclusion f g h ≫ pullback.fst _ _ =
      pullback.fst (pullback.snd f g) (pullback.fst g h) := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The middle diagonal preserves the right adjacent product. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleInclusion_snd :
    correspondenceTripleInclusion f g h ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd f g) (pullback.fst g h) := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The product-support inclusion preserves its left support coordinate. -/
@[reassoc (attr := simp)]
theorem correspondenceSupportProductInclusion_fst
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceSupportProductInclusion f g h z w ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι :=
  pullback.lift_fst _ _ _

/-- The product-support inclusion preserves its right support coordinate. -/
@[reassoc (attr := simp)]
theorem correspondenceSupportProductInclusion_snd
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceSupportProductInclusion f g h z w ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (integralComponentAt w).subschemeι :=
  pullback.lift_snd _ _ _

/-- The incidence-to-product map preserves the actual left support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToSupportProduct_fst
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidenceToSupportProduct f g h z w ≫ pullback.fst _ _ =
      pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
        ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The incidence-to-product map preserves the actual right support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToSupportProduct_snd
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidenceToSupportProduct f g h z w ≫ pullback.snd _ _ =
      pullback.snd ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
        ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The two actual incidence maps have the same four-factor ambient image. -/
@[reassoc]
theorem correspondenceIncidence_ambient_comm
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidenceInclusion f g h z w ≫ correspondenceTripleInclusion f g h =
    correspondenceIncidenceToSupportProduct f g h z w ≫
      correspondenceSupportProductInclusion f g h z w := by
  apply pullback.hom_ext <;> simp

end Stacks.Chow
