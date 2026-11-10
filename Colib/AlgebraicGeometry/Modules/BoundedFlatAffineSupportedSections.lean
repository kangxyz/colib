/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport
public import Colib.CategoryTheory.ObjectProperty.NestedEquivalence

/-!
# Actual supported bounded-flat affine section evaluation

The original cocartesian sections are restricted by actual open acyclicity of identity
section evaluation. The existing categorical equivalence restricts and flattens its target.
Adapted from Quillen `BoundedFlat/SupportedSections.lean:33-50` and
`SupportedSectionEquivalence.lean:28-65` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- Actual support of a section is acyclicity of its original evaluated complex on the open. -/
def boundedAboveFlatAffineSectionSupported (j : U ⟶ Spec R) [IsOpenImmersion j] :
    ObjectProperty (BoundedAboveFlatAffineSections R) := fun s ↦
  (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((boundedAboveFlatAffineOriginalEvaluation R).obj s).obj).Acyclic

/-- Supported objects are original cocartesian sections with the actual support predicate. -/
abbrev BoundedAboveFlatAffineSupportedSections (j : U ⟶ Spec R) [IsOpenImmersion j] :=
  (boundedAboveFlatAffineSectionSupported j).FullSubcategory

/-- Original evaluation lands in the original supported bounded-flat category. -/
def boundedAboveFlatAffineSupportedEvaluation (j : U ⟶ Spec R) [IsOpenImmersion j] :
    BoundedAboveFlatAffineSupportedSections j ⥤ (boundedAboveFlatPerfectSupported j).FullSubcategory
      :=
  (boundedAboveFlatPerfectSupported j).lift
    ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineOriginalEvaluation R ⋙
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι)
    (fun s ↦ ⟨((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)

/-- Forgetting support after evaluation retains the literal original chain complex. -/
theorem boundedAboveFlatAffineSupportedEvaluation_obj (j : U ⟶ Spec R) [IsOpenImmersion j]
    (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedEvaluation j).obj s).obj =
      ((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj).obj := rfl

variable (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original support is exactly the inverse-image predicate under the actual evaluation. -/
theorem boundedAboveFlatAffineSupportedEvaluation_property :
    ((boundedAboveFlatPerfectSupported j).inverseImage (boundedAboveFlatPerfectComplex (Spec
      R).toRingedSpace).ι).inverseImage
        (boundedAboveFlatAffineSectionEquivalence R).functor =
      boundedAboveFlatAffineSectionSupported j := by
  funext s
  apply propext
  exact and_iff_right ((boundedAboveFlatAffineOriginalEvaluation R).obj s).property

/-- Restrict the original equivalence and flatten the actual supported target, without replacement.
-/
def boundedAboveFlatAffineSupportedSectionEquivalence :
    BoundedAboveFlatAffineSupportedSections j ≌
      (boundedAboveFlatPerfectSupported j).FullSubcategory := by
  exact @CategoryTheory.ObjectProperty.evaluationRestrictionEquivalence.{u + 1, u, u + 1, u + 1}
    (CochainComplex (Spec R).Modules ℤ) inferInstance
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace) (boundedAboveFlatPerfectSupported j)
    (fun _ h ↦ h.1) (BoundedAboveFlatAffineSections R) inferInstance
    (boundedAboveFlatAffineSectionEquivalence R) (boundedAboveFlatAffineSectionSupported j)
    (boundedAboveFlatPerfectSupported_closedUnderIsomorphisms j)
    (boundedAboveFlatAffineSupportedEvaluation_property j)

/-- The forward equivalence is literally the original supported evaluation on objects and maps. -/
theorem boundedAboveFlatAffineSupportedSectionEquivalence_functor :
    (boundedAboveFlatAffineSupportedSectionEquivalence j).functor =
      boundedAboveFlatAffineSupportedEvaluation j :=
  @CategoryTheory.ObjectProperty.evaluationRestrictionEquivalence_functor.{u + 1, u, u + 1, u + 1}
    (CochainComplex (Spec R).Modules ℤ) inferInstance
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace) (boundedAboveFlatPerfectSupported j)
    (fun _ h ↦ h.1) (BoundedAboveFlatAffineSections R) inferInstance
    (boundedAboveFlatAffineSectionEquivalence R) (boundedAboveFlatAffineSectionSupported j)
    (boundedAboveFlatPerfectSupported_closedUnderIsomorphisms j)
    (boundedAboveFlatAffineSupportedEvaluation_property j) _

instance boundedAboveFlatAffineSupportedEvaluation_isEquivalence :
    (boundedAboveFlatAffineSupportedEvaluation j).IsEquivalence := by
  rw [← boundedAboveFlatAffineSupportedSectionEquivalence_functor]
  infer_instance

/-- The original counit supplies every original supported complex under the same evaluation. -/
def boundedAboveFlatAffineSupportedEvaluationCounit
    (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    (boundedAboveFlatAffineSupportedEvaluation j).obj
      ((boundedAboveFlatAffineSupportedSectionEquivalence j).inverse.obj K) ≅ K :=
  (boundedAboveFlatAffineSupportedSectionEquivalence j).counitIso.app K

end AlgebraicGeometry.Scheme.Modules
