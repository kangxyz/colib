/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationChart
public import Colib.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting
public import Colib.Topology.Prespectrum.StrictSquareCone

/-!
# The original global Bass evaluation overlap

Cancel the common original Laurent evaluation in the two genuine chart pastings. The source
is the original strict-section square's constant cylinder; the target retains both actual
polynomial evaluation tracks and the full original raw two-chart overlap.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- The strict square's positive diagonal is the original Laurent projection map. -/
theorem sectionSquare_source :
    (sectionSquare X).left.hom ≫ (sectionSquare X).hom.right =
      sectionMap (GlobalRawBass.laurentProjection.app X) := by
  change sectionMap (projection.app X) ≫ sectionMap (plus.app X) = _
  rw [← sectionMap_comp, GlobalRawBass.plus_projection]

/-- The two actual chart pastings meet along the original raw Bass overlap. -/
def boundaryMiddle :=
  (chartSecondTrack X (plus.app X)).trans
    ((((Homotopy.precomp (evaluation X)
      (chartGeometricTrack X (plus.app X) (GlobalRawBass.plus_projection X))).cast
        rfl (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (evaluation X)
        (chartGeometricTrack X (minus.app X) (GlobalRawBass.minus_projection X))).cast
        rfl (Category.assoc _ _ _).symm)).trans (chartSecondTrack X (minus.app X)).symm)

/-- The original two-chart boundary retains both moving evaluation sides. -/
def boundaryTarget :=
  ((chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X)).trans
    (boundaryMiddle X)).trans
      (chartFirstTrack X (minus.app X) (GlobalRawBass.minus_projection X)).symm

/-- Both genuine chart pastings cancel the same unchanged Laurent evaluation track. -/
def boundary :
    (Topology.LoopPrespectrum.Homotopy.refl
      (sectionMap (GlobalRawBass.laurentProjection.app X) ≫
        evaluation (laurent.obj X))).RelHomotopy (boundaryTarget X) :=
  Homotopy.RelHomotopy.pasteStrictSourceSquares
    (T := evaluationComparison (GlobalRawBass.laurentProjection.app X))
    (Lp := chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X))
    (Pp := chartSecondTrack X (plus.app X))
    (Kp := (Homotopy.precomp (evaluation X)
      (chartGeometricTrack X (plus.app X) (GlobalRawBass.plus_projection X))).cast
      rfl (Category.assoc _ _ _).symm)
    (Lm := chartFirstTrack X (minus.app X) (GlobalRawBass.minus_projection X))
    (Pm := chartSecondTrack X (minus.app X))
    (Km := (Homotopy.precomp (evaluation X)
      (chartGeometricTrack X (minus.app X) (GlobalRawBass.minus_projection X))).cast
      rfl (Category.assoc _ _ _).symm)
    (chartPasting X (plus.app X) (GlobalRawBass.plus_projection X))
    (chartPasting X (minus.app X) (GlobalRawBass.minus_projection X))

/-- The actual strict square cylinder followed by original Laurent evaluation. -/
def sourceTrack := (StrictSquare.track (sectionSquare X)).postcomp (evaluation (laurent.obj X))

/-- Both actual polynomial evaluation tracks retain the original raw Bass overlap between them. -/
def targetTrack :=
  ((evaluationComparison (projection.app X)).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))).trans
    (((Homotopy.precomp (evaluation X) (GlobalRawBass.squareHomotopy X)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((evaluationComparison (projection.app X)).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X))).symm)

/-- The full moving evaluation boundary, with both original distinct Laurent chart sides. -/
def pastedTrack :=
  ((chartMovingTrack X (plus.app X)).trans (targetTrack X)).trans
    (chartMovingTrack X (minus.app X)).symm

/-- The entire strict source cylinder is the original constant Laurent diagonal. -/
theorem sourceTrack_level (n : ℕ) :
    (sourceTrack X).level n =
      (Topology.LoopPrespectrum.Homotopy.refl
        (sectionMap (GlobalRawBass.laurentProjection.app X) ≫
          evaluation (laurent.obj X))).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change (((sectionSquare X).left.hom ≫ (sectionSquare X).hom.right) ≫
      evaluation (laurent.obj X)).map n x =
    (sectionMap (GlobalRawBass.laurentProjection.app X) ≫ evaluation (laurent.obj X)).map n x
  rw [sectionSquare_source]
  rfl

/-- The middle overlap retains both original chart tracks and their signs. -/
theorem middleTrack_level (n : ℕ) :
    ((Homotopy.precomp (evaluation X) (GlobalRawBass.squareHomotopy X)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).level n =
    (((Homotopy.precomp (evaluation X)
      (chartGeometricTrack X (plus.app X) (GlobalRawBass.plus_projection X))).cast
      rfl (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (evaluation X)
        (chartGeometricTrack X (minus.app X) (GlobalRawBass.minus_projection X))).cast
        rfl (Category.assoc _ _ _).symm)).level n := by
  simp only [Homotopy.cast_level, GlobalRawBass.squareHomotopy,
    Homotopy.precomp_trans, Homotopy.precomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (chartGeometricTrack_plus X).symm
  · apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (chartGeometricTrack_minus X).symm

/-- The actual target track is the central boundary supplied by original chart geometry. -/
theorem targetTrack_level (n : ℕ) : (targetTrack X).level n = (boundaryMiddle X).level n := by
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · exact middleTrack_level X n
    · rfl

/-- Both moving sides retain the entire original chart comparisons. -/
theorem pastedTrack_level (n : ℕ) : (pastedTrack X).level n = (boundaryTarget X).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · exact chartMovingTrack_level X (plus.app X) (GlobalRawBass.plus_projection X) n
    · exact targetTrack_level X n
  · apply Homotopy.symm_level_congr
    exact chartMovingTrack_level X (minus.app X) (GlobalRawBass.minus_projection X) n

/-- The original strict cylinder has a genuine relative pasting to the full raw overlap. -/
def pasting : (sourceTrack X).RelHomotopy (pastedTrack X) :=
  (boundary X).ofLevels _ _ (sourceTrack_level X) (pastedTrack_level X)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
