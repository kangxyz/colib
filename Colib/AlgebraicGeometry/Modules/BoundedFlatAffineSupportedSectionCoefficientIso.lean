/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionReindex

/-!
# Original supported affine coefficient transition

Lift the inverse actual cocartesian evaluation transition through the native fully
faithful supported inclusion. The endpoint transports and underlying chain map
remain explicit; geometric evaluation is not asserted strictly natural.

Adapted from Quillen `SupportedSectionCoefficientIso.lean:31-144` in
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem lift_comp_inclusion_eq {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ x, P (F.obj x)) :
    P.lift F hF ⋙ P.ι = F := rfl

private theorem supported_comp_forget_eq {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (P : ObjectProperty A) (Q : ObjectProperty B) (T : ObjectProperty D)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (G : Q.FullSubcategory ⥤ T.FullSubcategory)
    (H : A ⥤ B) (K : B ⥤ C) (L : C ⥤ D)
    (hF : F ⋙ Q.ι = P.ι ⋙ H) (hG : G ⋙ T.ι = Q.ι ⋙ K ⋙ L) :
    (F ⋙ G) ⋙ T.ι = P.ι ⋙ (H ⋙ K) ⋙ L := by
  rw [Functor.assoc, hG, ← Functor.assoc F Q.ι, hF]
  simp only [Functor.assoc]

private theorem supported_comp_forget_comparison {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (P : ObjectProperty A) (Q : ObjectProperty B) (T : ObjectProperty C)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (G : Q.FullSubcategory ⥤ T.FullSubcategory)
    (I : A ⥤ D) (J : D ⥤ B) (K : B ⥤ C) (L : D ⥤ E) (M : E ⥤ C)
    (hF : F ⋙ Q.ι = P.ι ⋙ I ⋙ J) (hG : G ⋙ T.ι = Q.ι ⋙ K)
    (hL : L ⋙ M = J ⋙ K) :
    (F ⋙ G) ⋙ T.ι = P.ι ⋙ (I ⋙ L) ⋙ M := by
  rw [Functor.assoc, hG, ← Functor.assoc F Q.ι, hF]
  simp only [Functor.assoc]
  rw [← hL]

variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt

variable (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- Forgetting support after evaluation retains the actual complex-valued functor. -/
theorem boundedAboveFlatAffineSupportedEvaluation_forget :
    boundedAboveFlatAffineSupportedEvaluation j ⋙ (boundedAboveFlatPerfectSupported j).ι =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineOriginalEvaluation R ⋙
        (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι :=
  lift_comp_inclusion_eq (boundedAboveFlatPerfectSupported j)
    ((boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineOriginalEvaluation R ⋙
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι)
    (fun s ↦ ⟨((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)


section

attribute [local irreducible] boundedAboveFlatAffineSupportedSectionsMap
  boundedAboveFlatAffineSupportedEvaluation

/-- Forgetting the actual reindexed evaluation retains the same chain objects and maps. -/
theorem boundedAboveFlatAffineSupportedReindexEvaluation_forget :
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatAffineSupportedEvaluation j') ⋙ (boundedAboveFlatPerfectSupported j').ι =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙
        (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S) ⋙
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι :=
  supported_comp_forget_eq
    (boundedAboveFlatAffineSectionSupported j) (boundedAboveFlatAffineSectionSupported j')
    (boundedAboveFlatPerfectSupported j')
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h)
    (boundedAboveFlatAffineSupportedEvaluation j')
    (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι
    (boundedAboveFlatAffineSupportedSectionsMap_forget j j' f l h)
    (boundedAboveFlatAffineSupportedEvaluation_forget j')

/-- Actual supported pair pullback forgets to the original complex pullback. -/
theorem boundedAboveFlatAffineSupportedPairPullback_forget :
    boundedAboveFlatPerfectSupportedPullback
        (boundedAboveFlatAffineSupportedPairSquare j j' f l h) ⋙
        (boundedAboveFlatPerfectSupported j').ι =
      (boundedAboveFlatPerfectSupported j).ι ⋙
        (pullback (Spec.map f)).mapHomologicalComplex (.up ℤ) :=
  lift_comp_inclusion_eq (boundedAboveFlatPerfectSupported j')
    ((boundedAboveFlatPerfectSupported j).ι ⋙
      (pullback (Spec.map f)).mapHomologicalComplex (.up ℤ))
    (fun K ↦ boundedAboveFlatPerfectSupported_pairPullback
      (boundedAboveFlatAffineSupportedPairSquare j j' f l h) K.property)

/-- Original bounded-flat pullback retains the literal complex pullback functor. -/
theorem boundedAboveFlatAffineOriginalPullback_forget :
    boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι =
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι ⋙
        (pullback (Spec.map f)).mapHomologicalComplex (.up ℤ) :=
  lift_comp_inclusion_eq (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace)
    ((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι ⋙
      (pullback (Spec.map f)).mapHomologicalComplex (.up ℤ))
    (fun K ↦ boundedAboveFlatPerfectComplex_pullback (Spec.map f) K.property)

attribute [local irreducible] boundedAboveFlatPerfectSupportedPullback
  boundedAboveFlatPerfectPullback

/-- The actual geometric pair pullback forgets to the original termwise complex pullback. -/
theorem boundedAboveFlatAffineSupportedEvaluationPullback_forget :
    (boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedPullback
        (boundedAboveFlatAffineSupportedPairSquare j j' f l h)) ⋙
        (boundedAboveFlatPerfectSupported j').ι =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙
        (boundedAboveFlatAffineOriginalEvaluation R ⋙
          boundedAboveFlatPerfectPullback (Spec.map f)) ⋙
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι :=
  supported_comp_forget_comparison
    (boundedAboveFlatAffineSectionSupported j) (boundedAboveFlatPerfectSupported j)
    (boundedAboveFlatPerfectSupported j') (boundedAboveFlatAffineSupportedEvaluation j)
    (boundedAboveFlatPerfectSupportedPullback
      (boundedAboveFlatAffineSupportedPairSquare j j' f l h))
    (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι
    ((pullback (Spec.map f)).mapHomologicalComplex (.up ℤ))
    (boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι
    (boundedAboveFlatAffineSupportedEvaluation_forget j)
    (boundedAboveFlatAffineSupportedPairPullback_forget j j' f l h)
    (boundedAboveFlatAffineOriginalPullback_forget f)

/-- The original coefficient transition lifted through the actual fully faithful inclusion. -/
def boundedAboveFlatAffineSupportedSectionCoefficientIso :
    boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatAffineSupportedEvaluation j' ≅
      boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedPullback
        (boundedAboveFlatAffineSupportedPairSquare j j' f l h) :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported j').ι
    (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm)

end

/-- The left endpoint transport is literally identity on the original evaluated complex. -/
theorem boundedAboveFlatAffineSupportedReindexEvaluation_forget_eqToHom
    (s : BoundedAboveFlatAffineSupportedSections j) :
    eqToHom (congrArg (fun K : BoundedAboveFlatAffineSupportedSections j ⥤
      CochainComplex (Spec S).Modules ℤ ↦ K.obj s)
      (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h)) =
      𝟙 (((boundedAboveFlatAffineOriginalEvaluation S).obj
        ((boundedAboveFlatAffineSectionsMap f).obj s.obj)).obj) := rfl

/-- The right endpoint transport is literally identity on the original pulled-back complex. -/
theorem boundedAboveFlatAffineSupportedEvaluationPullback_forget_eqToHom
    (s : BoundedAboveFlatAffineSupportedSections j) :
    eqToHom (congrArg (fun K : BoundedAboveFlatAffineSupportedSections j ⥤
      CochainComplex (Spec S).Modules ℤ ↦ K.obj s)
      (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm) =
      𝟙 (((boundedAboveFlatPerfectPullback (Spec.map f)).obj
        ((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj)).obj) := rfl


end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSectionCoefficientIso.lean:31-144"
  "adaptation"
  "Fully faithful lift of the actual inverse evaluation transition and endpoint transports"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionCoefficientIso
