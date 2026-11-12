/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportRestriction
public import Colib.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Actual native fiber-support inclusion

Only the additional fiber support is forgotten. The original evaluation retains the same
complex and literal full-subcategory inclusion.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
    boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- Original intersection support implies the unchanged auxiliary support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberInclusion.lean:33"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientFiberSupport_le (a : Under R) :
    boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      a).ι ≤
      boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T a).ι
        := by
  intro S hS
  exact ((restrictAcyclic_sup_iff (boundedAboveFlatCoefficientSupportOpen Q T a)
    (schemeMap f a).opensRange
    ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S).obj).mp hS).1

/-- Forget only the additional closed fiber support, keeping the actual native section. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberInclusion.lean:42"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedFiberForget (a : Under R) :
    BoundedAboveFlatCoefficientSupportedFiberSections f T a ⥤
      BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a :=
  ObjectProperty.ιOfLE (boundedAboveFlatCoefficientFiberSupport_le f T a)

/-- Evaluation commutes literally with the two specified property inclusions. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberInclusion.lean:47"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem propertyEvaluation_forget {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (hPQ : P ≤ Q) (A B : ObjectProperty D) (hAB : A ≤ B)
    (E : C ⥤ D) (hEA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hEB : ∀ X : Q.FullSubcategory, B (E.obj X.obj)) :
    A.lift (P.ι ⋙ E) hEA ⋙ ObjectProperty.ιOfLE hAB =
      ObjectProperty.ιOfLE hPQ ⋙ B.lift (Q.ι ⋙ E) hEB := rfl

/-- Original intersection support inclusion after evaluation keeps the actual complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberInclusion.lean:55"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedFiberEvaluation_forget (a : Under R) :
    boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientFiberSupportOpen f
      T a).ι ⋙
      ObjectProperty.ιOfLE
        (show boundedAboveFlatPerfectSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
          a).ι ≤
          boundedAboveFlatPerfectSupported (boundedAboveFlatCoefficientSupportOpen Q T a).ι from
          fun K hK ↦ ((boundedAboveFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a) K).mp hK).1) =
      boundedAboveFlatCoefficientSupportedFiberForget f T a ⋙
        boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι := by
  unfold boundedAboveFlatCoefficientSupportedEvaluation
  dsimp only [boundedAboveFlatCoefficientSupportedFiberForget]
  exact propertyEvaluation_forget _ _ _ _ _ _ _ _ _

/-- Equal underlying functors have equal lifts to the same object property. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberInclusion.lean:68"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem supportLift_congr {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) :
    P.lift F hF = P.lift G hG := by
  subst h
  rfl

end AlgebraicGeometry.Scheme.Modules
