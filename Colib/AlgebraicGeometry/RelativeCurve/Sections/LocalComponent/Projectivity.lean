/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel

/-!
# The original finite projective-line cover supplies projectivity

The glued projective line is the native projective-space model over the affine base. Its
projectivity supplies an ample invertible sheaf, and the native finite-morphism and composition
theorems supply projectivity of the original cover. The ample affine base then supplies an
actual closed immersion into a projective space. No projectivity witness is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite cover of the original projective line is H-projective over its affine base. -/
theorem isProjectiveMorphism_of_finite_projectiveLine
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) : IsProjectiveMorphism p := by
  have hA : HasAmpleInvertibleSheaf (Spec (.of A)) :=
    Scheme.Modules.exists_isAmple_of_isAffine _
  have hline : IsProjectiveMorphism (projectiveLine A ↘ Spec (.of A)) :=
    ⟨1, (projectiveLineIsoProjectiveSpaceOver A).hom, inferInstance,
      projectiveLineIsoProjectiveSpaceOver_hom_fst A⟩
  have hline' : IsProjective (projectiveLine A ↘ Spec (.of A)) :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hA).mpr hline
  have hlineAmple : HasAmpleInvertibleSheaf (projectiveLine A) :=
    ((isProjective_iff_isProper_and_hasAmpleInvertibleSheaf _ hA).mp hline').2
  have hπ' : IsProjective π :=
    isProjective_of_isFinite_of_hasAmpleInvertibleSheaf π hlineAmple
  have hp : IsProjective p := by
    rw [← hπ]
    exact isProjective_comp_of_hasAmpleInvertibleSheaf π _ hA hline' hπ'
  exact (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf p hA).mp hp

end AlgebraicGeometry.Scheme
