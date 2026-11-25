/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCubeFaces
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputComparisonTracks
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterWhole

/-!
# The original mixed evaluation comparison cube

The six fully compatible common-reference faces are evaluated jointly on the original overlap
source. The complete original comparison square descends from this cube and its two prescribed
polynomial chart squares. All three cube times and the independent structure time survive.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCube
open GlobalSectionChangeIndex InputComparisonTracks
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual compact three-parameter family acts on the unchanged strict overlap source. -/
def level (n : ℕ) :
    C(unitInterval × (unitInterval × (unitInterval ×
      (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n)),
      (prespectrum (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace))).space n) :=
  ⟨fun z => CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) n (![z.1, z.2.1, z.2.2.1], z.2.2.2), by fun_prop⟩

/-- The whole source face is the original strict-precomposed X descent surface. -/
theorem at_zero (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (0, (r, (s, x))) =
      (source g).level n (r, HomotopyPushout.cylinder
        (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (s, x)) :=
  (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputMixedDesc.preSquareParameter g)
    ![0, r, s] (r, s) (InputCubeFaces.zero g r s) n x).trans
    ((InputMixedDesc.pre_square_parameter_native g n r s x).trans
      (source_cylinder g n r s x).symm)

/-- The whole target face keeps both original outer comparison halves and all inner heights. -/
theorem at_one (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (1, (r, (s, x))) =
      (target g).level n (r, HomotopyPushout.cylinder
        (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (s, x)) :=
  (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputTargetFace.parameter g)
    ![1, r, s] (r, s) (InputCubeFaces.one g r s) n x).trans
    (DFunLike.congr_fun (InputTargetFace.whole_native g n) ((r, s), x))

/-- The Laurent face retains the actual unpaused evaluation on the strict comparison. -/
theorem bottom (n : ℕ) (q s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (q, (0, (s, x))) =
      (left g).level n (q, HomotopyPushout.cylinder
        (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (s, x)) :=
  (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputLaurentFace.parameter g)
    ![q, 0, s] (q, s) (InputCubeFaces.bottom g q s) n x).trans
    (DFunLike.congr_fun (InputLaurentFace.diagonal_native_level g n) ((q, s), x))

/-- The span face is the original corrected boundary and its selected quotient collapse. -/
theorem top (n : ℕ) (q s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (q, (1, (s, x))) =
      (right g).level n (q, HomotopyPushout.cylinder
        (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (s, x)) :=
  (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputSpanParameterWord.parameter g)
    ![q, 1, s] (q, s) (InputCubeFaces.top g q s) n x).trans
    (DFunLike.congr_fun (InputSpanParameterWhole.native g n) ((q, s), x))

/-- The positive polynomial face is its entire original moving commuting square. -/
theorem plus (n : ℕ) (q r : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (q, (r, (0, x))) =
      (plusSquare g).level n (q, (r, (sectionMap (projection.app Y)).map n x)) := by
  rw [plusSquare_level]
  exact (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputChartSquareParameter.plusParameter g)
    ![q, r, 0] (q, r) (InputCubeFaces.plus g q r) n x).trans
    (DFunLike.congr_fun
      (InputChartSquareParameter.native g
        AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.plus
        GlobalRawBass.plus_projection n) ((q, r), x))

/-- The inverse polynomial face keeps its independent original chart route. -/
theorem minus (n : ℕ) (q r : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    level g n (q, (r, (1, x))) =
      (minusSquare g).level n (q, (r, (sectionMap (projection.app Y)).map n x)) := by
  rw [minusSquare_level]
  exact (CommonReferenceNerve.compactFamily_of_point_eq (InputMixedDesc.sourceMap g)
    (InputCubeFaces.parameter g) (InputChartSquareParameter.minusParameter g)
    ![q, r, 1] (q, r) (InputCubeFaces.minus g q r) n x).trans
    (DFunLike.congr_fun
      (InputChartSquareParameter.native g
        AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.minus
        GlobalRawBass.minus_projection n) ((q, r), x))

/-- The complete original overlap cube, including points and independent structure time. -/
def cylinder : HomotopyPushout.SquareCylinder
    (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
    (source g) (target g) (left g) (right g) (plusSquare g) (minusSquare g) where
  level := level g
  at_zero := at_zero g
  at_one := at_one g
  bottom := bottom g
  top := top g
  left := plus g
  right := minus g
  at_point n q r s := CommonReferenceNerve.compactPrespectrumFamily_point
    (InputMixedDesc.sourceMap g) (InputCubeFaces.parameter g) n ![q, r, s]
  comm n q r s x t := CommonReferenceNerve.compactPrespectrumFamily_structure
    (InputMixedDesc.sourceMap g) (InputCubeFaces.parameter g) n ![q, r, s] x t

/-- All original chart squares and the full overlap cube descend to the whole mixed square. -/
def square : (source g).Square (target g) (left g) (right g) :=
  HomotopyPushout.squareOfCylinder
    (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
    (source g) (target g) (left g) (right g) (plusSquare g) (minusSquare g) (cylinder g)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCube
