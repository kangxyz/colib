/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackUnit
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-! # The actual Laurent-unit equation across original evaluation

The original evaluation comparison has the reverse orientation to the geometric
pullback-to-section evaluation transition. The conjugation below retains that orientation.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.GrothendieckSections
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
private theorem reverseEvaluationIso {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (h : D = B) :
    eqToIso h ≪≫ e.symm = (e ≪≫ eqToIso h.symm).symm := by
  subst h
  rfl

private theorem unitEvaluationSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (A : C ⥤ D) (P : D ⥤ E) (B : C ⥤ F) (Q : F ⥤ E)
    (e : A ⋙ P ≅ B ⋙ Q) (a : 𝟭 F ≅ 𝟭 F) (b : 𝟭 E ≅ 𝟭 E)
    (hQ : ∀ x, Q.map (a.hom.app x) = b.hom.app (Q.obj x)) :
    whiskerLeft A ((Functor.rightUnitor P).symm ≪≫
        isoWhiskerLeft P b ≪≫ Functor.rightUnitor P).hom ≫ e.hom =
      e.hom ≫ whiskerRight (Functor.IdentityAutomorphism.onFunctor B a).hom Q := by
  apply NatTrans.ext
  funext x
  let b₀ : P.obj (A.obj x) ⟶ P.obj (A.obj x) := b.hom.app (P.obj (A.obj x))
  let b₁ : Q.obj (B.obj x) ⟶ Q.obj (B.obj x) := b.hom.app (Q.obj (B.obj x))
  change (𝟙 (P.obj (A.obj x)) ≫ b₀ ≫ 𝟙 (P.obj (A.obj x))) ≫ e.hom.app x =
    e.hom.app x ≫ Q.map (a.hom.app (B.obj x))
  rw [Category.id_comp, Category.comp_id, hQ]
  have hn := (b.hom.naturality (e.hom.app x)).symm
  change b₀ ≫ e.hom.app x = e.hom.app x ≫ b₁ at hn
  exact hn


namespace AlgebraicGeometry.Scheme.Modules

/-- The original Laurent evaluation transition, directed from geometric pullback to sections. -/
def boundedAboveFlatAffineSectionLaurentEvaluationIso (R : CommRingCat.{u}) :
    boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatPerfectPullback
      (laurentProjection R) ≅
    boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R) ⋙
      boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)) :=
  boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk (laurentCoefficientInclusion R)) ≪≫
    eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation
      (laurentCoefficientInclusion R)).symm

/-- The native coefficient comparison is the reverse original evaluation transition. -/
theorem boundedAboveFlatAffineSectionCoefficientIso_laurent (R : CommRingCat.{u}) :
    originalCoefficientIso boundedAboveFlatAffinePseudofunctor (laurentCoefficientInclusion R) =
      (boundedAboveFlatAffineSectionLaurentEvaluationIso R).symm :=
  reverseEvaluationIso
    (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk (laurentCoefficientInclusion R)))
    (boundedAboveFlatAffineSectionsMap_comp_evaluation (laurentCoefficientInclusion R))

/-- Original evaluation intertwines the actual strict and geometric Laurent actions. -/
theorem boundedAboveFlatAffineSectionLaurentPullbackUnitIso_evaluation
    (R : CommRingCat.{u}) :
    whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom ≫
      (boundedAboveFlatAffineSectionLaurentEvaluationIso R).hom =
    (boundedAboveFlatAffineSectionLaurentEvaluationIso R).hom ≫
      whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) :=
  unitEvaluationSquare
    (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectPullback (laurentProjection R))
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineSectionLaurentEvaluationIso R)
    (boundedAboveFlatAffineSectionUnitIso (.of (LaurentPolynomial R)) (laurentCoordinate R))
    (boundedAboveFlatPerfectGlobalUnitIso (Spec (.of (LaurentPolynomial R))) (laurentCoordinate R))
    (boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom
      (.of (LaurentPolynomial R)) (laurentCoordinate R))

/-- Reverse evaluation intertwines units in precisely the coefficient track's direction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentEvaluationUnit.lean:34-58"
  "adaptation" "Original forward Laurent action and reverse evaluation comparison"]
theorem boundedAboveFlatAffineSectionLaurentCoefficientUnitSquare (R : CommRingCat.{u}) :
    whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) ≫
      (originalCoefficientIso boundedAboveFlatAffinePseudofunctor
        (laurentCoefficientInclusion R)).hom =
    (originalCoefficientIso boundedAboveFlatAffinePseudofunctor
      (laurentCoefficientInclusion R)).hom ≫
      whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom := by
  rw [boundedAboveFlatAffineSectionCoefficientIso_laurent]
  change whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
      (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) ≫
        (boundedAboveFlatAffineSectionLaurentEvaluationIso R).inv =
    (boundedAboveFlatAffineSectionLaurentEvaluationIso R).inv ≫
      whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom
  have h := congrArg (fun η => (boundedAboveFlatAffineSectionLaurentEvaluationIso R).inv ≫
    η ≫ (boundedAboveFlatAffineSectionLaurentEvaluationIso R).inv)
      (boundedAboveFlatAffineSectionLaurentPullbackUnitIso_evaluation R)
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h.symm

end AlgebraicGeometry.Scheme.Modules
