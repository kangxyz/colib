/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Contraction.Basic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GeneratorEpi

/-! # Literal Laurent representatives and vanishing ambient corrections -/
/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/Contraction/Representatives.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `9c5aaf8ff90cfc6b399be525aa609a996de77ef8`. All generator and image-sieve maps use the
actual native Laurent cylinder and closed inverse-image boundary.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

@[reassoc (attr := simp)]
theorem presheafBoundaryRestriction_generator :
    presheafBoundaryRestriction P j ≫ presheafBoundaryGenerator P j i = 0 := by
  unfold presheafBoundaryGenerator
  rw [← Category.assoc, presheafBoundaryRestriction_projection, zero_comp]

/-- A correction extending to the original ambient neighborhood dies before any
sheaf coefficient replacement: this is the actual quotient relation. -/
theorem presheafBoundaryGenerator_extend (W : EtaleSeparatedFiniteType Y.left)
    (s : P.obj (op ((toSmoothSite Y).obj W))) :
    (presheafBoundaryGenerator P j i).app (op W)
      ((presheafBoundaryRestriction P j).app (op W) s) = 0 :=
  ConcreteCategory.congr_hom (congr_app
    (presheafBoundaryRestriction_generator P j i) (op W)) s

namespace OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : PresheafWithTransfers.{u + 1} k)

/-- The sheafified canonical map on a Laurent representative is the unchanged
quotient projection followed by the actual ambient and inverse-image units. -/
@[reassoc]
theorem laurent_sheafified_boundary :
    Functor.whiskerLeft (toSmoothSite X).op
        ((PresheafWithTransfers.toPresheaf k).map (PresheafWithTransfers.toContraction F)) ≫
      toSheafify (nisnevichTopology X.left) _ ≫ (contractionToBoundary X F).hom =
      laurentToAmbientCokernel X F ≫ ambientCokernelToBoundary X F := by
  rw [toSheafify_contractionToBoundary, toContraction_contractionToBoundaryPresheaf]

end OriginalPresheaf
end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

