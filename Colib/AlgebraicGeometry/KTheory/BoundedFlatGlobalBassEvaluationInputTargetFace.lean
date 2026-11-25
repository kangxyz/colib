/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawPastedSeam
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawPastedNative

/-!
# The entire target face of the mixed evaluation overlap

The original postcomposed Y descent square and the three-piece raw input surface are glued
on their complete nerve edge. The resulting compact family is precisely the original pasted
comparison homotopy on the strict span cylinder, with all nested half clocks unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTargetFace
open GlobalSectionChangeIndex Path.CarrierHalfPaths
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire actual target face uses its proved full nerve seam and original outer half clock. -/
def parameter :=
  ScalarRectangle.concatFirst (InputMixedDesc.postSquareParameter g)
    (InputRawPastedParameter.parameter g) (InputRawPastedSeam.seam g)

/-- The whole first half is the original Y descent after raw Laurent pullback. -/
theorem parameter_lower (r s : unitInterval) :
    parameter g (lower r, s) = InputMixedDesc.postSquareParameter g (r, s) :=
  ScalarRectangle.concatFirst_lower _ _ (InputRawPastedSeam.seam g) r s

/-- The whole second half is the raw homotopy on the unchanged evaluated span cylinder. -/
theorem parameter_upper (r s : unitInterval) :
    parameter g (upper r, s) = InputRawPastedParameter.parameter g (r, s) :=
  ScalarRectangle.concatFirst_upper _ _ (InputRawPastedSeam.seam g) r s

/-- The exact original strict cylinder retains its independent height coordinate. -/
def cylinderParameter (n : ℕ) :
    C((unitInterval × unitInterval) ×
      (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n,
      unitInterval × (StrictSquare.span (sectionSquare Y)).space n) :=
  ⟨fun z => (z.1.1, HomotopyPushout.cylinder (sectionMap (projection.app Y))
    (sectionMap (projection.app Y)) n (z.1.2, z.2)), by fun_prop⟩

/-- The target family is the original composite-square track, not a same-boundary replacement. -/
def nativeFamily (n : ℕ) :=
  ((coneSquarePastedHomotopy
    (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison Y)
    (GlobalRawBass.comparison X) (spanEvaluation Y) (evaluation (laurent.obj Y))
    (GlobalRawBass.spanMap g) (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g)).level n).comp
      (cylinderParameter (Y := Y) n)

/-- The first native half keeps the actual selected Y descent square. -/
theorem native_lower (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeFamily g n ((lower r, s), x) =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g)).map n
        ((descPasting Y).toSquare.level n (r, (s, x))) :=
  (coneSquarePasted_lower_cell
    (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison Y)
    (GlobalRawBass.comparison X) (spanEvaluation Y) (evaluation (laurent.obj Y))
    (GlobalRawBass.spanMap g) (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g) n r
    (HomotopyPushout.cylinder (sectionMap (projection.app Y))
      (sectionMap (projection.app Y)) n (s, x))).trans
    (congrArg ((boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g)).map n)
      (comparisonHomotopy_cylinder Y n r s x))

/-- The second native half retains every point of the original evaluated raw input surface. -/
theorem native_upper (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeFamily g n ((upper r, s), x) = InputRawPastedNative.nativeFamily g n ((r, s), x) :=
  coneSquarePasted_upper_cell
    (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison Y)
    (GlobalRawBass.comparison X) (spanEvaluation Y) (evaluation (laurent.obj Y))
    (GlobalRawBass.spanMap g) (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g) n r
    (HomotopyPushout.cylinder (sectionMap (projection.app Y))
      (sectionMap (projection.app Y)) n (s, x))

/-- The whole compact target face recovers the original pasted homotopy at every native level. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g) n = nativeFamily g n := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g) (InputMixedDesc.postSquareParameter g)
      (lower t, s) (t, s) (parameter_lower g t s) n x).trans
      ((InputMixedDesc.post_square_parameter_native g n t s x).trans
        (native_lower g n t s x).symm)
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g) (InputRawPastedParameter.parameter g)
      (upper t, s) (t, s) (parameter_upper g t s) n x).trans
      ((DFunLike.congr_fun (InputRawPastedNative.whole_native g n) ((t, s), x)).trans
        (native_upper g n t s x).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTargetFace
