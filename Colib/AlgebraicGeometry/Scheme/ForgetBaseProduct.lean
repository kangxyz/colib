/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Products after forgetting a separated base

The product over the original base includes as a closed subscheme in the
product over a separated smaller base. Pushing the original integral support
through this inclusion preserves its source projection, not its scalar degree.
For an unramified finite-type base map the product inclusion is also open.
These constructions do not yet assert preservation of correspondence composition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)

/-- The original two projections, now viewed over the smaller base. -/
def forgetBaseProductMap : pullback f g ⟶ pullback (f ≫ r) (g ≫ r) :=
  pullback.map f g (f ≫ r) (g ≫ r) (𝟙 X) (𝟙 Y) r
    (Category.id_comp _).symm (Category.id_comp _).symm

@[reassoc (attr := simp)]
theorem forgetBaseProductMap_fst :
    forgetBaseProductMap r f g ≫ pullback.fst (f ≫ r) (g ≫ r) = pullback.fst f g := by
  simp [forgetBaseProductMap, pullback.map]

@[reassoc (attr := simp)]
theorem forgetBaseProductMap_snd :
    forgetBaseProductMap r f g ≫ pullback.snd (f ≫ r) (g ≫ r) = pullback.snd f g := by
  simp [forgetBaseProductMap, pullback.map]

instance [IsSeparated r] : IsClosedImmersion (forgetBaseProductMap r f g) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g r)
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal r)))

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseProductMap r f g) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g r)
    (inferInstanceAs (IsOpenImmersion (pullback.diagonal r)))

end AlgebraicGeometry.Scheme
