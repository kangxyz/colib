/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.EtaleSeparable

/-! # Native residue separability descends along the actual scheme map -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- The image residue embeds in the source residue, with its native scalar map.
No étaleness or finiteness assumption on the scheme map is needed. -/
theorem isSeparable_residueField_image_of_over_field
    {F : Type u} [Field F] {A X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (g : A ⟶ X) (a : A)
    (hs : letI := (fieldToResidue (g ≫ f) a).hom.toAlgebra
      Algebra.IsSeparable F (A.residueField a)) :
    letI := (fieldToResidue f (g a)).hom.toAlgebra
    Algebra.IsSeparable F (X.residueField (g a)) := by
  let : Algebra F (X.residueField (g a)) := (fieldToResidue f (g a)).hom.toAlgebra
  let : Algebra F (A.residueField a) := (fieldToResidue (g ≫ f) a).hom.toAlgebra
  let : Algebra (X.residueField (g a)) (A.residueField a) :=
    (g.residueFieldMap a).hom.toAlgebra
  let : Algebra.IsSeparable F (A.residueField a) := hs
  let : IsScalarTower F (X.residueField (g a)) (A.residueField a) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change (fieldToResidue (g ≫ f) a).hom r = _
    rw [fieldToResidue_comp_native]
    rfl
  exact Algebra.isSeparable_tower_bot_of_isSeparable
    F (X.residueField (g a)) (A.residueField a)

end AlgebraicGeometry
