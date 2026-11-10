/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation

/-!
# Exact forgetting of the original support condition on affine sections

The actual inclusion retains the original section and every morphism. Its literal evaluation
square and the existing geometric support-forgetting functor prove exactness. The genuine
ambient evaluation equivalence reflects zero objects and pushouts, and the chosen zero is
unchanged. This is not a localization assertion.

Adapted from Quillen `SupportedSectionForgetEvaluation.lean:28-35` and
`SupportedSectionForgetExact.lean:30-63` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem lift_comp_inclusion_precomp {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (P Q : ObjectProperty B) (h : P ≤ Q) (I : A ⥤ C)
    (F : C ⥤ Q.FullSubcategory) (hF : ∀ X, P (F.obj (I.obj X)).obj) :
    P.lift (I ⋙ F ⋙ Q.ι) hF ⋙ ObjectProperty.ιOfLE h = I ⋙ F := rfl

variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence

/-- Forgetting geometric support retains the literal original evaluated section and every map. -/
theorem boundedAboveFlatAffineSupportedEvaluation_forget_to_boundedFlat :
    boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedForget j =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙
        boundedAboveFlatAffineOriginalEvaluation R :=
  lift_comp_inclusion_precomp (boundedAboveFlatPerfectSupported j)
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace) (fun _ h ↦ h.1)
    (boundedAboveFlatAffineSectionSupported j).ι (boundedAboveFlatAffineOriginalEvaluation R)
    (fun s ↦ ⟨((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)

/-- The actual support inclusion is exact after original geometric evaluation. -/
theorem boundedAboveFlatAffineSupportedSectionForget_evaluation_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).weq
      ((boundedAboveFlatAffineSectionSupported j).ι ⋙
        boundedAboveFlatAffineOriginalEvaluation R) := by
  rw [← boundedAboveFlatAffineSupportedEvaluation_forget_to_boundedFlat]
  exact (boundedAboveFlatAffineSupportedEvaluation_exact j).comp
    (boundedAboveFlatPerfectSupportedForget_isExact j)

/-- Actual support forgetting preserves the original Waldhausen classes and cofibration pushouts.
-/
theorem boundedAboveFlatAffineSupportedSectionForget_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatAffineSectionSupported j).ι where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatAffineOriginalEvaluation R) _
    ((boundedAboveFlatAffineSupportedSectionForget_evaluation_exact j).zero hx)
  cofibration a ha := by
    change (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).cof
      ((boundedAboveFlatAffineOriginalEvaluation R).map _)
    exact (boundedAboveFlatAffineSupportedSectionForget_evaluation_exact j).cofibration a ha
  weak a ha := by
    change (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).weq
      ((boundedAboveFlatAffineOriginalEvaluation R).map _)
    exact (boundedAboveFlatAffineSupportedSectionForget_evaluation_exact j).weak a ha
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatAffineOriginalEvaluation R)
    exact (boundedAboveFlatAffineSupportedSectionForget_evaluation_exact j).pushout hi hp

/-- The original chosen zero section is literally unchanged after forgetting support. -/
theorem boundedAboveFlatAffineSupportedSectionForget_zero :
    (boundedAboveFlatAffineSectionSupported j).ι.obj
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
      (boundedAboveFlatAffineSectionWaldhausen R).zero := rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSectionForgetEvaluation.lean:28-35"
  "adaptation" "Literal geometric evaluation and support-forgetting square"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedEvaluation_forget_to_boundedFlat

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionForgetExact.lean:30-63"
  "adaptation" "Actual exactness reflected through evaluation and literal chosen zero"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionForget_evaluation_exact
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionForget_exact
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionForget_zero
