/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentModelUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineBassStep
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIntertwiningHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyIntertwining
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting

/-! # The original whole Laurent-unit evaluation square -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The unchanged section unit has the original model's pointwise weakness. -/
theorem boundedAboveFlatAffineSectionLaurentModelUnit_weak
    (X : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))).obj.waldhausen.weq
      ((boundedAboveFlatAffineSectionLaurentModelUnit R).app X) := by
  change (boundedAboveFlatAffineSectionWaldhausen (.of (LaurentPolynomial R))).weq
    ((boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom.app X)
  exact (boundedAboveFlatAffineSectionWaldhausen (.of (LaurentPolynomial R))).weq_iso _ (by
    change IsIso ((boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom.app X)
    exact NatIso.hom_app_isIso (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R) X)

/-- The original normalized unit retains pointwise weakness after its actual universe lift. -/
theorem boundedAboveFlatAffineOriginalLaurentModelUnit_weak
    (X : (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace)).obj.waldhausen.weq
      ((boundedAboveFlatAffineOriginalLaurentModelUnit R).app X) :=
  normalizedWeakTransformation_weak
    (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
    (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
    (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace).weq_iso _
      inferInstance) (AsSmall.down.obj X)

/-- The complete original strict unit followed by evaluation. -/
def boundedAboveFlatAffineSectionLaurentEvaluationOldUnit :=
  (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))

/-- The complete original raw geometric unit preceded by evaluation. -/
def boundedAboveFlatAffineSectionLaurentEvaluationNewUnit :=
  Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatLaurentUnitHomotopy R)

/-- The actual unchanged coefficient track intertwines both whole original Laurent actions. -/
def boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting :
    ((boundedAboveFlatAffineSectionLaurentEvaluationOldUnit R).trans
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R))).RelHomotopy
    ((boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R)).trans
        (boundedAboveFlatAffineSectionLaurentEvaluationNewUnit R)) := by
  let J := prespectrumTransformationIntertwiningHomotopy
    (boundedAboveFlatAffineSectionModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficientInclusion R))
    (boundedAboveFlatAffinePullbackModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelMap R)
    (boundedAboveFlatAffineEvaluationModelMap (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineSectionLaurentModelUnit R)
    (boundedAboveFlatAffineOriginalLaurentModelUnit R)
    (boundedAboveFlatAffineEvaluationModelIso
      (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R)).hom
    (boundedAboveFlatAffineSectionLaurentModelUnit_weak R)
    (boundedAboveFlatAffineOriginalLaurentModelUnit_weak R)
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace).asSmall.weq_iso _ (by
        change IsIso ((boundedAboveFlatAffineEvaluationModelIso
          (laurentCoefficientInclusion R)).hom.app x)
        infer_instance))
    (boundedAboveFlatAffineSectionLaurentModelEvaluationUnitSquare R)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

/-- Actual reverse-track cancellation produces the precise boundary needed by square descent. -/
def boundedAboveFlatAffineSectionLaurentEvaluationUnitBoundary :
    (boundedAboveFlatAffineSectionLaurentEvaluationOldUnit R).RelHomotopy
      (((boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R)).trans
          (boundedAboveFlatAffineSectionLaurentEvaluationNewUnit R)).trans
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy
          (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R)).symm) :=
  Homotopy.RelHomotopy.conjugateBoundary _ _ _
    (boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting R)

/-- The original strict/raw Laurent actions have a genuine whole evaluation square. -/
def boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare :
    (boundedAboveFlatAffineSectionLaurentEvaluationOldUnit R).Square
      (boundedAboveFlatAffineSectionLaurentEvaluationNewUnit R)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R))
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficientInclusion R)) :=
  (boundedAboveFlatAffineSectionLaurentEvaluationUnitBoundary R).toSquare

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentEvaluationHomotopy.lean:39-117"
  "adaptation" "Original forward Laurent actions and actual evaluation whole-track intertwining"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentEvaluationUnitBoundary
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentEvaluationUnitSquare
