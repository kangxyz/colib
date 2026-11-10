/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentEvaluationHomotopy

/-! # Consumers of the actual raw square, original null and forward Laurent unit -/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
variable (R : CommRingCat.{u})

example : boundedAboveFlatBassSquareHomotopy R =
    (boundedAboveFlatLaurentPlusHomotopy R).symm.trans
      (boundedAboveFlatLaurentMinusHomotopy R) := rfl

example : boundedAboveFlatBassSourceLeg R =
    boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
      HomotopyPushout.inl _ _ := rfl

example : boundedAboveFlatBassSourceLeg R ≫ boundedAboveFlatBassSquareComparison R =
    boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R) :=
  boundedAboveFlatBassSourceLeg_comparison R

example (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassSquareComparison R).map n
      (HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) n (s, x)) =
    ((boundedAboveFlatLaurentPlusHomotopy R).symm.trans
      (boundedAboveFlatLaurentMinusHomotopy R)).level n (s, x) := rfl

example (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level (n + 1)
      (s, (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).structureMap n x t) =
    (mappingCone (boundedAboveFlatBassSquareComparison R)).structureMap n
      ((boundedAboveFlatBassLaurentNullHomotopy R).level n (s, x)) t :=
  (boundedAboveFlatBassLaurentNullHomotopy R).comm n s x t

example (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    Path.toContinuousMap ((boundedAboveFlatAffineBassTransition R).map n x) s =
    ((boundedAboveFlatBassLaurentNullHomotopy R).symm.trans
      (((boundedAboveFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).trans
          (boundedAboveFlatBassLaurentNullHomotopy R))).level n (s, x) := rfl

example (s : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space 0) :
    Path.toContinuousMap ((boundedAboveFlatAffineBassTransition R).map 0 x) s =
    ((boundedAboveFlatBassLaurentNullHomotopy R).symm.trans
      (((boundedAboveFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).trans
          (boundedAboveFlatBassLaurentNullHomotopy R))).level 0 (s, x) := rfl

example : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom (laurentCoordinate R).val =
    LaurentPolynomial.T 1 := by
  rw [laurentCoordinate_val]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _

example : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom (↑((laurentCoordinate R)⁻¹)) =
    LaurentPolynomial.T (-1) := by
  rw [laurentCoordinate_inv_val]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _

example :
    ((boundedAboveFlatAffineSectionLaurentEvaluationOldUnit R).trans
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (laurentCoefficientInclusion R))).RelHomotopy
      ((boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (laurentCoefficientInclusion R)).trans
          (boundedAboveFlatAffineSectionLaurentEvaluationNewUnit R)) :=
  boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting R

example (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare R).level (n + 1)
      (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
    (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare R).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare R).comm n r s x t

example (r s : unitInterval) :
    (boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare R).level 0
      (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point 0)) =
    (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace)).point 0 :=
  (boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare R).at_point 0 r s

example : boundedAboveFlatLaurentUnitHomotopy R =
    boundedAboveFlatPerfectUnitHomotopy (laurentProjection R) (laurentCoordinate R) := rfl

example : CategoryTheory.GrothendieckSections.originalCoefficientIso
    boundedAboveFlatAffinePseudofunctor (laurentCoefficientInclusion R) =
      (boundedAboveFlatAffineSectionLaurentEvaluationIso R).symm :=
  boundedAboveFlatAffineSectionCoefficientIso_laurent R

example :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) ≫
      (CategoryTheory.GrothendieckSections.originalCoefficientIso
        boundedAboveFlatAffinePseudofunctor (laurentCoefficientInclusion R)).hom =
    (CategoryTheory.GrothendieckSections.originalCoefficientIso
      boundedAboveFlatAffinePseudofunctor (laurentCoefficientInclusion R)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom :=
  boundedAboveFlatAffineSectionLaurentCoefficientUnitSquare R

example :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentModelUnit R)
        (boundedAboveFlatAffineEvaluationModelMap (.of (LaurentPolynomial R))).hom.toFunctor ≫
      (boundedAboveFlatAffineEvaluationModelIso (laurentCoefficientInclusion R)).hom =
    (boundedAboveFlatAffineEvaluationModelIso (laurentCoefficientInclusion R)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatAffineEvaluationModelMap R).hom.toFunctor
        (boundedAboveFlatAffineOriginalLaurentModelUnit R) :=
  boundedAboveFlatAffineSectionLaurentModelEvaluationUnitSquare R

example (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level n
      (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x) =
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
      ((boundedAboveFlatLaurentPlusHomotopy R).level n (t, x)) :=
  boundedAboveFlatBassLaurentNullHomotopy_first_half R n t x

example (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level n
      (⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x) =
    ReducedMappingCone.cylinder
      ((HomotopyPushout.prespectrum
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))).point n)
      ((originalPrespectrum (boundedAboveFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial R))).toRingedSpace)).point n)
      ((boundedAboveFlatBassSquareComparison R).map n)
      (t, (boundedAboveFlatBassSourceLeg R).map n x) :=
  boundedAboveFlatBassLaurentNullHomotopy_second_half R n t x

example (t : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space 0) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level 0
      (⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x) =
    (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level 0
      (t, (boundedAboveFlatBassSourceLeg R).map 0 x) :=
  boundedAboveFlatBassLaurentNullHomotopy_second_half R 0 t x
