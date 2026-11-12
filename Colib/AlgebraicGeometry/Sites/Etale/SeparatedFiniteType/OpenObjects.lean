/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ResidueGerms
public import Mathlib.AlgebraicGeometry.Noetherian


/-! # Actual small-site separatedness for residue-splitting zero families -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/OpenZeroFamily.lean`, blob
`07c39794a16d341052407e95405f9ac261fb0a3a`.
Only the actual open-object and restriction maps are extracted. No persistent or dense-open
section detection theorem is assumed.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {U : Scheme.{u}} [IsNoetherian U]

/-- An actual open subscheme as an object of the original small site. -/
def openObject (W : U.Opens) : EtaleSeparatedFiniteType U :=
  MorphismProperty.Over.mk ⊤ W.ι ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Restriction of an actual small-site object to an original base open. -/
def openRestrictedObject (V : EtaleSeparatedFiniteType U) (W : U.Opens) : EtaleSeparatedFiniteType U
    := by
  let : QuasiCompact (((V.hom ∣_ W) ≫ W.ι)) := inferInstance
  have : QuasiCompact ((V.hom ⁻¹ᵁ W).ι ≫ V.hom) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact MorphismProperty.Over.mk ⊤ ((V.hom ⁻¹ᵁ W).ι ≫ V.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The literal inclusion of the restriction over the base open `W` into `V`. -/
def openRestrictedInclusion (V : EtaleSeparatedFiniteType U) (W : U.Opens) :
    openRestrictedObject V W ⟶ V := MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ W).ι rfl

/-- The restricted structure morphism to the base-open object `openObject W`. -/
def openRestrictedMap (V : EtaleSeparatedFiniteType U) (W : U.Opens) :
    openRestrictedObject V W ⟶ openObject W :=
  MorphismProperty.Over.homMk (V.hom ∣_ W) (morphismRestrict_ι _ _)

@[reassoc] theorem openRestrictedMap_toBase (V : EtaleSeparatedFiniteType U) (W : U.Opens) :
    openRestrictedMap V W ≫ toBaseObject (openObject W) =
      openRestrictedInclusion V W ≫ toBaseObject V := by
  apply MorphismProperty.Over.Hom.ext
  exact morphismRestrict_ι V.hom W


end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
