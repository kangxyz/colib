/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich

/-! # Actual composition and arrows of small etale objects -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Point/Persistent/MarkedSection.lean`, blob `9f8ff5275051ed22d1d81ac4845c70273acfaf91`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S : Scheme.{u}}

/-- Compose actual étale structure maps, retaining the underlying object. -/
def composeObject (V : EtaleSeparatedFiniteType S) (W : EtaleSeparatedFiniteType V.left) :
    EtaleSeparatedFiniteType S :=
  MorphismProperty.Over.mk ⊤ (W.hom ≫ V.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The same underlying arrow between composed étale objects, with its original equation over
the base. -/
def composeObjectMap (V : EtaleSeparatedFiniteType S) {W Z : EtaleSeparatedFiniteType V.left}
    (f : W ⟶ Z) : composeObject V W ⟶ composeObject V Z :=
  MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (Z.hom ≫ V.hom) = W.hom ≫ V.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

/-- The original structure morphism from the composed étale object to `V`. -/
def composeObjectProjection (V : EtaleSeparatedFiniteType S) (W : EtaleSeparatedFiniteType V.left) :
    composeObject V W ⟶ V := MorphismProperty.Over.homMk W.hom rfl

/-- Every original arrow into V is again an actual object of its small étale site. -/
def arrowObject {W V : EtaleSeparatedFiniteType S} (f : W ⟶ V) : EtaleSeparatedFiniteType V.left :=
    by
  have hp : etaleSeparatedFiniteType (f.left ≫ V.hom) := by
    rw [MorphismProperty.Over.w]
    exact W.prop
  exact MorphismProperty.Over.mk ⊤ f.left
    (etaleSeparatedFiniteType.of_postcomp f.left V.hom V.prop hp)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
