/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionZero

/-!
# The original pointwise zero section with support

The chosen section is the existing pointwise zero; support is proved after actual restriction.
Adapted from Quillen `BoundedFlat/SupportedSectionZero.lean:31-45` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- The existing original zero section satisfies actual acyclicity on every specified open. -/
theorem boundedAboveFlatAffineSectionZero_supported (j : U ⟶ Spec R) [IsOpenImmersion j] :
    boundedAboveFlatAffineSectionSupported j (boundedAboveFlatAffineSectionZero R) := by
  change (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((boundedAboveFlatAffineOriginalEvaluation R).obj
    (boundedAboveFlatAffineSectionZero R)).obj).Acyclic
  rw [boundedAboveFlatAffineOriginalEvaluation_sectionZero]
  exact HomologicalComplex.acyclic_of_isZero _ (((restrictFunctor j).mapHomologicalComplex
    (ComplexShape.up ℤ)).map_isZero
    ((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι.map_isZero
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero))

/-- The supported chosen zero is the same original source-independent section. -/
def boundedAboveFlatAffineSupportedSectionZero (j : U ⟶ Spec R) [IsOpenImmersion j] :
    BoundedAboveFlatAffineSupportedSections j :=
  ⟨boundedAboveFlatAffineSectionZero R, boundedAboveFlatAffineSectionZero_supported j⟩

/-- The unchanged chosen section is a genuine zero object in the actual supported category. -/
theorem isZero_boundedAboveFlatAffineSupportedSectionZero
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    IsZero (boundedAboveFlatAffineSupportedSectionZero j) :=
  IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatAffineSectionSupported j).ι _
    (isZero_boundedAboveFlatAffineSectionZero R)

end AlgebraicGeometry.Scheme.Modules
