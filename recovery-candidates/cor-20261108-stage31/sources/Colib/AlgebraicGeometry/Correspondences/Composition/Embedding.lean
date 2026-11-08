/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The actual closed incidence in the triple product

The two integral closed supports map to their adjacent products. Their native
pullback over the middle factor is therefore a closed subscheme of the native
triple product. All morphisms below are the existing pullback maps.

Source: motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Support/Basic.lean. The mathematical construction is
MVW2006, Lecture 1, the composition construction preceding Proposition 1.7.
Reconstructed from retained consumer interfaces; no historical byte identity is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The actual triple product, associating along the common middle factor. -/
abbrev correspondenceTripleProduct : Scheme.{u} :=
  pullback (pullback.snd f g) (pullback.fst g h)

/-- The closed incidence inclusion retains both full integral support schemes. -/
def correspondenceIncidenceInclusion
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidence f g h z w ⟶ correspondenceTripleProduct f g h :=
  pullback.map _ _ _ _ (integralComponentAt z).subschemeι
    (integralComponentAt w).subschemeι (𝟙 Y) (by simp) (by simp)

instance isClosedImmersion_correspondenceIncidenceInclusion
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    IsClosedImmersion (correspondenceIncidenceInclusion f g h z w) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance rfl rfl

/-- The incidence inclusion has the original left support coordinate. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceInclusion_fst
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidenceInclusion f g h z w ≫
      pullback.fst (pullback.snd f g) (pullback.fst g h) =
    pullback.fst _ _ ≫ (integralComponentAt z).subschemeι := by
  simp [correspondenceIncidenceInclusion]

/-- The incidence inclusion has the original right support coordinate. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceInclusion_snd
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) :
    correspondenceIncidenceInclusion f g h z w ≫
      pullback.snd (pullback.snd f g) (pullback.fst g h) =
    pullback.snd _ _ ≫ (integralComponentAt w).subschemeι := by
  simp [correspondenceIncidenceInclusion]

end Stacks.Chow
