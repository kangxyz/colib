/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting

/-!
# The original strict-section Bass evaluation boundary

Cancel the common actual Laurent evaluation track in the two proved chart pastings. The
source is the original strict square's constant cylinder, and the target keeps both original
coefficient evaluation tracks and the original bounded-flat Bass cylinder.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationBoundary.lean`
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

/-- The central two-chart boundary retains the original polynomial evaluation tracks. -/
def boundedAboveFlatAffineSectionBassEvaluationBoundaryMiddle :
    Topology.LoopPrespectrum.Homotopy
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R))
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R)) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ kp =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent R
  let hm : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ km =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent_invert R
  (boundedAboveFlatAffineSectionChartSecondTrack R kp).trans
    ((((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffineSectionChartGeometricTrack R kp hp)).cast rfl
        (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffineSectionChartGeometricTrack R km hm)).cast rfl
          (Category.assoc _ _ _).symm)).trans
      (boundedAboveFlatAffineSectionChartSecondTrack R km).symm)

/-- The explicit loop obtained by pasting the two original chart evaluation boundaries. -/
def boundedAboveFlatAffineSectionBassEvaluationBoundaryTarget :
    Topology.LoopPrespectrum.Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ kp =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent R
  let hm : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ km =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent_invert R
  ((boundedAboveFlatAffineSectionChartFirstTrack R kp hp).trans
    (boundedAboveFlatAffineSectionBassEvaluationBoundaryMiddle R)).trans
      (boundedAboveFlatAffineSectionChartFirstTrack R km hm).symm

/-- Both genuine Laurent-chart pastings cancel their one common evaluation track. -/
def boundedAboveFlatAffineSectionBassEvaluationBoundary :
    (Topology.LoopPrespectrum.Homotopy.refl
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).RelHomotopy
      (boundedAboveFlatAffineSectionBassEvaluationBoundaryTarget R) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ kp =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent R
  let hm : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ km =
    laurentCoefficientInclusion R :=
    coefficient_toLaurent_invert R
  Homotopy.RelHomotopy.pasteStrictSourceSquares
    (T := boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R))
    (Lp := boundedAboveFlatAffineSectionChartFirstTrack R kp hp)
    (Pp := boundedAboveFlatAffineSectionChartSecondTrack R kp)
    (Kp := (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffineSectionChartGeometricTrack R kp hp)).cast rfl
        (Category.assoc _ _ _).symm)
    (Lm := boundedAboveFlatAffineSectionChartFirstTrack R km hm)
    (Pm := boundedAboveFlatAffineSectionChartSecondTrack R km)
    (Km := (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffineSectionChartGeometricTrack R km hm)).cast rfl
        (Category.assoc _ _ _).symm)
    (boundedAboveFlatAffineSectionChartFirstPasting R kp hp)
    (boundedAboveFlatAffineSectionChartFirstPasting R km hm)

/-- The actual strict Bass cylinder is followed by unchanged original Laurent evaluation. -/
def boundedAboveFlatAffineSectionBassEvaluationSourceTrack :=
  (StrictSquare.track (boundedAboveFlatAffineSectionBassSquare R)).postcomp
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))

/-- The target cylinder keeps the original polynomial evaluation tracks and raw Bass square. -/
def boundedAboveFlatAffineSectionBassEvaluationTargetTrack :=
  ((boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R →+*
    Polynomial R)))).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R))).trans
    (((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatBassSquareHomotopy R)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R)))).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R))).symm)

/-- The positive moving boundary retains the entire original Laurent coefficient track. -/
def boundedAboveFlatAffineSectionBassEvaluationPlusTrack :=
  boundedAboveFlatAffineSectionChartMovingTrack R (CommRingCat.ofHom Polynomial.toLaurent)

/-- The other moving boundary retains the distinct inverse-coordinate track. -/
def boundedAboveFlatAffineSectionBassEvaluationMinusTrack :=
  boundedAboveFlatAffineSectionChartMovingTrack R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

/-- The complete three-sided evaluation boundary has the exact moving-square association. -/
def boundedAboveFlatAffineSectionBassEvaluationPastedTrack :=
  ((boundedAboveFlatAffineSectionBassEvaluationPlusTrack R).trans
    (boundedAboveFlatAffineSectionBassEvaluationTargetTrack R)).trans
      (boundedAboveFlatAffineSectionBassEvaluationMinusTrack R).symm

/-- The boundary begins at the literal original constant strict-square cylinder. -/
theorem boundedAboveFlatAffineSectionBassEvaluationSourceTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationSourceTrack R).level n =
      (Topology.LoopPrespectrum.Homotopy.refl
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
          boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).level n
        := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change (((boundedAboveFlatAffineSectionBassSquare R).left.hom ≫
      (boundedAboveFlatAffineSectionBassSquare R).hom.right) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n x =
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n x
  rw [boundedAboveFlatAffineSectionBassSquare_source]
  rfl

/-- The middle geometric square keeps the two original Laurent chart tracks and their signs. -/
theorem boundedAboveFlatAffineSectionBassEvaluationMiddleTrack_level (n : ℕ) :
    ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatBassSquareHomotopy R)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).level n =
    (((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffineSectionChartGeometricTrack R (CommRingCat.ofHom Polynomial.toLaurent)
        (coefficient_toLaurent R))).cast rfl
          (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffineSectionChartGeometricTrack R
          (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
          (coefficient_toLaurent_invert R))).cast rfl
            (Category.assoc _ _ _).symm)).level n := by
  simp only [Homotopy.cast_level, boundedAboveFlatBassSquareHomotopy,
    Homotopy.precomp_trans, Homotopy.precomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (boundedAboveFlatAffineSectionChartGeometricTrack_plus
      R).symm
  · apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (boundedAboveFlatAffineSectionChartGeometricTrack_minus
      R).symm

/-- The central boundary is the whole original target Bass comparison track. -/
theorem boundedAboveFlatAffineSectionBassEvaluationTargetTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationTargetTrack R).level n =
      (boundedAboveFlatAffineSectionBassEvaluationBoundaryMiddle R).level n := by
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · exact boundedAboveFlatAffineSectionBassEvaluationMiddleTrack_level R n
    · rfl

/-- The positive moving side retains the original whole chart evaluation track. -/
theorem boundedAboveFlatAffineSectionBassEvaluationPlusTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationPlusTrack R).level n =
      (boundedAboveFlatAffineSectionChartFirstTrack R (CommRingCat.ofHom Polynomial.toLaurent)
        (coefficient_toLaurent R)).level n := rfl

/-- The negative moving side separately retains the whole inverse-coordinate chart track. -/
theorem boundedAboveFlatAffineSectionBassEvaluationMinusTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationMinusTrack R).level n =
      (boundedAboveFlatAffineSectionChartFirstTrack R
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
        (coefficient_toLaurent_invert R)).level n :=
  boundedAboveFlatAffineSectionChartMovingTrack_level R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
    (coefficient_toLaurent_invert R) n

/-- The final boundary keeps both original coefficient tracks and the original Bass cylinder. -/
theorem boundedAboveFlatAffineSectionBassEvaluationPastedTrack_level (n : ℕ) :
    (boundedAboveFlatAffineSectionBassEvaluationPastedTrack R).level n =
      (boundedAboveFlatAffineSectionBassEvaluationBoundaryTarget R).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · exact boundedAboveFlatAffineSectionBassEvaluationPlusTrack_level R n
    · exact boundedAboveFlatAffineSectionBassEvaluationTargetTrack_level R n
  · apply Homotopy.symm_level_congr
    exact boundedAboveFlatAffineSectionBassEvaluationMinusTrack_level R n

/-- The proved chart geometry supplies the full original Bass evaluation pasted relation. -/
def boundedAboveFlatAffineSectionBassEvaluationPasting :
    (boundedAboveFlatAffineSectionBassEvaluationSourceTrack R).RelHomotopy
      (boundedAboveFlatAffineSectionBassEvaluationPastedTrack R) :=
  (boundedAboveFlatAffineSectionBassEvaluationBoundary R).ofLevels _ _
    (boundedAboveFlatAffineSectionBassEvaluationSourceTrack_level R)
    (boundedAboveFlatAffineSectionBassEvaluationPastedTrack_level R)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationBoundary.lean:34-220"
  "adaptation" "Cancellation of the common actual Laurent evaluation track with unchanged \
    boundary maps"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassEvaluationPasting
