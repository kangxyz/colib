/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationBoundary
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTower
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineBassStep

/-!
# The actual one-step Bass evaluation map

The proved original geometric boundary descends to the literal two comparison maps and then
to their original cones. Compatibility with the original Laurent-unit seed requires its
additional unit/null comparison and is not asserted here.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original positive source leg, Laurent
unit and independent whole-homotopy parameters are retained in native objects. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- Original evaluation maps the whole strict polynomial span to the raw geometric span. -/
def boundedAboveFlatAffineSectionBassSpanEvaluation :
    StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R) ⟶
      HomotopyPushout.prespectrum
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) :=
  HomotopyPushout.mapOfHomotopies
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))

/-- Original source-cylinder endpoints regroup for literal quotient descent. -/
def boundedAboveFlatAffineSectionBassEvaluationSourceDescTrack :=
  (boundedAboveFlatAffineSectionBassEvaluationSourceTrack R).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Original target-cylinder endpoints regroup for the same quotient descent. -/
def boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R)))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R))) :=
  (boundedAboveFlatAffineSectionBassEvaluationTargetTrack R).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The original Laurent boundaries are precomposed by the literal strict source legs. -/
def boundedAboveFlatAffineSectionBassEvaluationPastedDescTrack :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom Polynomial.toLaurent) ≫
            boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) ≫
            boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))) :=
  ((Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom
    (Polynomial.C : R →+* Polynomial R))))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom Polynomial.toLaurent))).trans
      (boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack R)).trans
    (Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom
      (Polynomial.C : R →+* Polynomial R))))
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)))).symm

/-- The proved original geometric boundary supplies the exact moving-descent interface. -/
def boundedAboveFlatAffineSectionBassEvaluationDescPasting :
    (boundedAboveFlatAffineSectionBassEvaluationSourceDescTrack R).RelHomotopy
      (boundedAboveFlatAffineSectionBassEvaluationPastedDescTrack R) :=
  (boundedAboveFlatAffineSectionBassEvaluationPasting R).ofLevels _ _ (fun _ => rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · rfl)

/-- The target cylinder is the original span-map cylinder followed by original raw Bass. -/
theorem boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack R).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
        (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))).postcomp
          (boundedAboveFlatBassSquareComparison R)).level n := by
  simp only [boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack, Homotopy.cast_level,
    boundedAboveFlatAffineSectionBassEvaluationTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · rfl
    · exact congrArg (fun H => H.level n)
        (Homotopy.postcomp_symm
          (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C
            : R →+* Polynomial R))))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R))).symm

/-- Source descent is the original strict comparison followed by unchanged Laurent evaluation. -/
theorem boundedAboveFlatAffineSectionBassEvaluationSourceDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (CommRingCat.ofHom
        Polynomial.toLaurent) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) ≫
          boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedAboveFlatAffineSectionBassEvaluationSourceDescTrack R) =
    StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- Target descent is the actual original span evaluation followed by raw Bass comparison. -/
theorem boundedAboveFlatAffineSectionBassEvaluationTargetDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))))
      (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R))
      (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R))
      (boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack R) =
    boundedAboveFlatAffineSectionBassSpanEvaluation R ≫ boundedAboveFlatBassSquareComparison R := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack_level R n)
      (s, x)

/-- The proved whole geometric filler descends to the two unchanged comparison-map composites. -/
def boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy :
    Homotopy (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedAboveFlatAffineSectionBassSpanEvaluation R ≫ boundedAboveFlatBassSquareComparison
        R) :=
  (HomotopyPushout.descSquareHomotopy
    (H₀ := boundedAboveFlatAffineSectionBassEvaluationSourceDescTrack R)
    (H₁ := boundedAboveFlatAffineSectionBassEvaluationTargetDescTrack R)
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom Polynomial.toLaurent))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)))
    (boundedAboveFlatAffineSectionBassEvaluationDescPasting R).toSquare).cast
      (boundedAboveFlatAffineSectionBassEvaluationSourceDesc_eq R)
      (boundedAboveFlatAffineSectionBassEvaluationTargetDesc_eq R)

/-- Every positive endpoint retains the complete original positive evaluation homotopy. -/
theorem boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_inl (n : ℕ)
    (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inl
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))).map n x) =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom Polynomial.toLaurent)).level n (r, x) := rfl

/-- The independent inverse-coordinate endpoint keeps its distinct original evaluation track. -/
theorem boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_inr (n : ℕ)
    (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inr
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))).map n x) =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))).level n
          (r, x) := rfl

/-- The complete original double cylinder is the proved moving geometric evaluation square. -/
theorem boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_cylinder (n : ℕ)
    (r s : unitInterval) (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, HomotopyPushout.cylinder
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R))))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C :
          R →+* Polynomial R)))) n (s, x)) =
      (boundedAboveFlatAffineSectionBassEvaluationDescPasting R).toSquare.level n (r, (s, x)) := rfl

/-- Original evaluation and its proved comparison square map the literal Bass cones. -/
def boundedAboveFlatAffineSectionBassConeEvaluation :
    boundedAboveFlatAffineSectionBassCone R ⟶ mappingCone (boundedAboveFlatBassSquareComparison
      R) :=
  mappingConeSquareMap (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))
    (boundedAboveFlatBassSquareComparison R) (boundedAboveFlatAffineSectionBassSpanEvaluation R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R)

/-- Laurent evaluation remains literal on the original cone inclusion. -/
theorem boundedAboveFlatAffineSectionBassConeEvaluation_inclusion :
    mappingConeInclusion (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)) ≫
        boundedAboveFlatAffineSectionBassConeEvaluation R =
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)) ≫
        mappingConeInclusion (boundedAboveFlatBassSquareComparison R) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- Parameter looping yields the actual one-step evaluation map on the original Bass objects. -/
def boundedAboveFlatAffineSectionBassStepEvaluation :
    (boundedAboveFlatAffineSectionBassDiagram 1).obj R ⟶ boundedAboveFlatAffineBassStep R :=
  parameterLoopingMap (boundedAboveFlatAffineSectionBassConeEvaluation R)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluation.lean:37-238"
  "adaptation" "Actual moving-boundary span map and cone evaluation with original polynomial \
    faces and cylinder"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStepEvaluation
