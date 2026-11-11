/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport
public import Colib.CategoryTheory.ObjectProperty.NestedEquivalence
public import Colib.Util.References

/-!
# Actual support of global cocartesian sections

Adapted from `GlobalSupportedSections.lean` in the original Quillen bounded-flat proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Support is the inverse image of the existing
geometric support predicate under the original evaluation. No second perfect-complex category
or replacement of its objects or morphisms is introduced.

The coefficient-restriction statements from the latter half of the original file are a later
closure: they require the genuine joint scheme/coefficient index, not the affine-only functor.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- A global section is supported exactly when its evaluated complex is acyclic on the open. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedSections.lean:42"
  "adaptation" "The original acyclicity predicate on unchanged global sections."]
def boundedAboveFlatGlobalSectionSupported : ObjectProperty (BoundedAboveFlatGlobalSections X) :=
  fun S ↦ (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((boundedAboveFlatGlobalSectionEvaluation X).obj S).obj).Acyclic

/-- Original evaluation restricted to the actual supported full subcategory. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedSections.lean:47"
  "adaptation" "Original evaluation and its actual supported geometric target."]
def boundedAboveFlatGlobalSupportedEvaluation :
    (boundedAboveFlatGlobalSectionSupported j).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  (boundedAboveFlatPerfectSupported j).lift
    ((boundedAboveFlatGlobalSectionSupported j).ι ⋙ boundedAboveFlatGlobalSectionEvaluation X ⋙
      (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).ι)
    (fun S ↦ ⟨((boundedAboveFlatGlobalSectionEvaluation X).obj S.obj).property, S.property⟩)

/-- The geometric support predicate pulls back to the original section-support predicate. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedSections.lean:55"
  "adaptation" "The same evaluation inverse-image identity and original proof."]
theorem boundedAboveFlatGlobalSupportedEvaluation_property :
    ((boundedAboveFlatPerfectSupported j).inverseImage
      (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).ι).inverseImage
        (boundedAboveFlatGlobalSectionEvaluation X).asEquivalence.functor =
      boundedAboveFlatGlobalSectionSupported j := by
  funext S
  apply propext
  exact and_iff_right ((boundedAboveFlatGlobalSectionEvaluation X).obj S).property

/-- The original global evaluation remains an equivalence on the actual support predicate. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedSections.lean:63"
  "adaptation" "Restriction of the original evaluation equivalence to actual support."]
instance boundedAboveFlatGlobalSupportedEvaluation_isEquivalence :
    (boundedAboveFlatGlobalSupportedEvaluation j).IsEquivalence := by
  let e := @CategoryTheory.ObjectProperty.evaluationRestrictionEquivalence.{u + 1, u, u + 1, u + 1}
    (CochainComplex X.unop.Modules ℤ) inferInstance
    (boundedAboveFlatPerfectComplex X.unop.toRingedSpace) (boundedAboveFlatPerfectSupported j)
    (fun _ h ↦ h.1) (BoundedAboveFlatGlobalSections X) inferInstance
    (boundedAboveFlatGlobalSectionEvaluation X).asEquivalence
    (boundedAboveFlatGlobalSectionSupported j)
    (boundedAboveFlatPerfectSupported_closedUnderIsomorphisms j)
    (boundedAboveFlatGlobalSupportedEvaluation_property j)
  have he : e.functor = boundedAboveFlatGlobalSupportedEvaluation j := rfl
  rw [← he]
  exact e.isEquivalence_functor

end AlgebraicGeometry.Scheme.Modules
