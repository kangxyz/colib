/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedSections
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientModelRestriction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedSections
/-! # Original coefficient restriction on the actual supported global sections

The first four support/evaluation declarations are reused from the existing native owner.
Only the original restriction square and its necessary private lift calculation are added.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
private theorem liftSquare {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (P : ObjectProperty A) (Q : ObjectProperty B) (T : ObjectProperty D)
    (F : A ⥤ B) (G : B ⥤ C) (E : A ⥤ C) (I : C ⥤ D) (h : F ⋙ G = E)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, T (I.obj (G.obj X.obj)))
    (hE : ∀ X : P.FullSubcategory, T (I.obj (E.obj X.obj))) :
    Q.lift (P.ι ⋙ F) hF ⋙ T.lift (Q.ι ⋙ G ⋙ I) hG =
      T.lift (P.ι ⋙ E ⋙ I) hE := by
  change T.lift (P.ι ⋙ F ⋙ G ⋙ I) _ = _
  apply supported_lift_congr
  rw [← Functor.assoc F, h]

variable (R : CommRingCat.{u}) (c : Index R) {U : Scheme.{u}}
    (j : U ⟶ space c) [IsOpenImmersion j]

/-- The original coefficient restriction preserves the exact acyclicity predicate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedSections.lean:76"
  "adaptation" "Original supported global coefficient restriction and literal evaluation square"]
theorem restriction_supported (S : BoundedAboveFlatGlobalSections
    ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)) :
    boundedAboveFlatCoefficientSectionSupported j
      (((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).hom.toFunctor.obj S) ↔
      boundedAboveFlatGlobalSectionSupported (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j S := by
  have h := congrArg (fun F => F.obj S)
    (boundedAboveFlatGlobalCoefficientModelRestriction_evaluation R c)
  exact Iff.of_eq (congrArg (fun K : (boundedAboveFlatPerfectComplex (space
    c).toRingedSpace).FullSubcategory =>
    (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).Acyclic) h)

/-- Restrict actual supported global sections to original coefficient sections. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedSections.lean:85"
  "adaptation" "Original supported global coefficient restriction and literal evaluation square"]
def supportedRestriction :
    (boundedAboveFlatGlobalSectionSupported (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)
      j).FullSubcategory ⥤
    BoundedAboveFlatCoefficientSupportedSections j :=
  (boundedAboveFlatCoefficientSectionSupported j).lift
    ((boundedAboveFlatGlobalSectionSupported (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).ι ⋙
      ((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).hom.toFunctor)
    (fun S => (restriction_supported R c j S.obj).mpr S.property)

/-- The support-forgetful square retains every original section and morphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedSections.lean:95"
  "adaptation" "Original supported global coefficient restriction and literal evaluation square"]
theorem supportedRestriction_forget :
    supportedRestriction R c j ⋙ (boundedAboveFlatCoefficientSectionSupported j).ι =
      (boundedAboveFlatGlobalSectionSupported (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).ι ⋙
        ((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).hom.toFunctor := rfl

/-- The supported evaluation square is literal equality of full functors. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedSections.lean:101"
  "adaptation" "Original supported global coefficient restriction and literal evaluation square"]
theorem supportedRestriction_evaluation :
    supportedRestriction R c j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j =
      boundedAboveFlatGlobalSupportedEvaluation
        (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j := by
  exact liftSquare _ _ _ ((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).hom.toFunctor
    (boundedAboveFlatCoefficientOriginalEvaluation c) (boundedAboveFlatGlobalSectionEvaluation _)
    (boundedAboveFlatPerfectComplex (space c).toRingedSpace).ι
      (boundedAboveFlatGlobalCoefficientModelRestriction_evaluation R c) _ _ _

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
