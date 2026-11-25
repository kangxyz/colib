/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterPrism
public import Colib.Topology.Path.CarrierHalfPaths
public import Colib.Topology.Path.SpanReassociation
public import Colib.Topology.Path.CarrierSquareDescent

/-!
# The original moving-span boundary word in the mixed reference

The two actual chart squares and the original evaluation-overlap product are pasted with the
native path-time halves. The literal five-piece reassociation corrects only the target path
inside the three-sided relative boundary. The final square is its original quotient descent.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterWord
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original fixed mixed Laurent reference carrier. -/
abbrev Carrier := |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|

/-- The unpaused evaluation side of an actual attached projection square. -/
def chartLeft (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    C(unitInterval, Carrier g) :=
  (InputSpanParameterNodes.parameter g k hk).comp ⟨fun r => (r, 0), by fun_prop⟩

/-- Exchange the two original square coordinates without changing either clock. -/
def chartSwap (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    (chartLeft g k hk).Homotopy (InputSpanParameterPrism.column g k hk 2) where
  toFun z := InputSpanParameterNodes.parameter g k hk (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left r := InputSpanParameterPrism.projection_column g k hk r

/-- The original split raw chart track acts on the independent evaluation coordinate. -/
def normalizationSwap (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    (InputSpanParameterPrism.column g k hk 0).Homotopy
      (InputSpanParameterPrism.column g k hk 2) where
  toFun z := InputSpanParameterPrism.parameter g k hk (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := InputSpanParameterPrism.parameter_left g k hk r
  map_one_left r := InputSpanParameterPrism.parameter_right g k hk r

/-- The actual overlap retains the reverse positive half and forward inverse half. -/
def overlapSwap :
    (InputSpanParameterPrism.column g plus GlobalRawBass.plus_projection 2).Homotopy
      (InputSpanParameterPrism.column g minus GlobalRawBass.minus_projection 2) :=
  (normalizationSwap g plus GlobalRawBass.plus_projection).symm.trans
    ((normalizationSwap g minus GlobalRawBass.minus_projection).cast
      (by
        apply ContinuousMap.ext
        exact InputSpanParameterPrism.shared_column g minus GlobalRawBass.minus_projection
          plus GlobalRawBass.plus_projection) rfl)

/-- The three native pieces retain the original outer half and inner quarter clocks. -/
def movingSwap := (chartSwap g plus GlobalRawBass.plus_projection).trans
  ((overlapSwap g).trans (chartSwap g minus GlobalRawBass.minus_projection).symm)

/-- The whole moving square before the prescribed target reassociation. -/
def movingParameter : C(unitInterval × unitInterval, Carrier g) :=
  ⟨fun z ↦ movingSwap g (z.2, z.1), by fun_prop⟩

/-- The original positive top chart, with its endpoints attached by full column equality. -/
def plusTop : Path (chartLeft g plus GlobalRawBass.plus_projection 1)
    (InputSpanParameterPrism.column g plus GlobalRawBass.plus_projection 2 1) where
  toFun s := chartSwap g plus GlobalRawBass.plus_projection (s, 1)
  continuous_toFun := by fun_prop
  source' := (chartSwap g plus GlobalRawBass.plus_projection).apply_zero 1
  target' := (chartSwap g plus GlobalRawBass.plus_projection).apply_one 1

/-- The independent inverse top chart with its unchanged original clock. -/
def minusTop : Path (chartLeft g minus GlobalRawBass.minus_projection 1)
    (InputSpanParameterPrism.column g minus GlobalRawBass.minus_projection 2 1) where
  toFun s := chartSwap g minus GlobalRawBass.minus_projection (s, 1)
  continuous_toFun := by fun_prop
  source' := (chartSwap g minus GlobalRawBass.minus_projection).apply_zero 1
  target' := (chartSwap g minus GlobalRawBass.minus_projection).apply_one 1

/-- The complete original top overlap at the evaluated input. -/
def overlapTop : Path
    (InputSpanParameterPrism.column g plus GlobalRawBass.plus_projection 2 1)
    (InputSpanParameterPrism.column g minus GlobalRawBass.minus_projection 2 1) where
  toFun s := overlapSwap g (s, 1)
  continuous_toFun := by fun_prop
  source' := (overlapSwap g).apply_zero 1
  target' := (overlapSwap g).apply_one 1

/-- The literal first half of a path, with its original source endpoint. -/
def firstHalf {Z : Type*} [TopologicalSpace Z] {a b : Z} (p : Path a b) :
    Path a (p Path.CarrierHalfPaths.middle) :=
  (Path.CarrierHalfPaths.first p.toContinuousMap).cast p.source.symm rfl

/-- The literal last half of a path, with its original target endpoint. -/
def lastHalf {Z : Type*} [TopologicalSpace Z] {a b : Z} (p : Path a b) :
    Path (p Path.CarrierHalfPaths.middle) b :=
  (Path.CarrierHalfPaths.last p.toContinuousMap).cast rfl p.target.symm

private theorem first_last {Z : Type*} [TopologicalSpace Z] {a b : Z} (p : Path a b) :
    (firstHalf p).trans (lastHalf p) = p := by
  apply Path.ext
  funext s
  exact Path.CarrierHalfPaths.trans_apply p.toContinuousMap s

/-- The original positive evaluation half of the top chart. -/
def firstPlus := firstHalf (plusTop g)
/-- The complete raw-square half of the positive top chart. -/
def lastPlus := lastHalf (plusTop g)
/-- The independent inverse top chart's original first half. -/
def firstMinus := firstHalf (minusTop g)
/-- The complete raw-square half of the inverse top chart. -/
def lastMinus := lastHalf (minusTop g)

/-- The target word of the original five-piece reassociation. -/
def pastedTop := ((firstPlus g).trans (lastPlus g)).trans
  ((overlapTop g).trans ((lastMinus g).symm.trans (firstMinus g).symm))

/-- The five exact original leaves recover the entire top of the moving square. -/
theorem pastedTop_apply (s : unitInterval) : pastedTop g s = movingParameter g (1, s) := by
  change (((firstHalf (plusTop g)).trans (lastHalf (plusTop g))).trans
    ((overlapTop g).trans ((lastHalf (minusTop g)).symm.trans (firstHalf (minusTop g)).symm))) s = _
  rw [first_last, ← Path.trans_symm, first_last]
  change ((plusTop g).trans ((overlapTop g).trans (minusTop g).symm)) s =
    ((chartSwap g plus GlobalRawBass.plus_projection).trans
      ((overlapSwap g).trans (chartSwap g minus GlobalRawBass.minus_projection).symm)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · rfl
  · rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split <;> rfl

/-- The original lower cylinder path, with its complete unchanged parameter. -/
def sourcePath : Path (chartLeft g plus GlobalRawBass.plus_projection 0)
    (chartLeft g minus GlobalRawBass.minus_projection 0) where
  toFun s := movingParameter g (0, s)
  continuous_toFun := by fun_prop
  source' := (movingSwap g).apply_zero 0
  target' := (movingSwap g).apply_one 0

/-- The whole unpaused positive chart boundary. -/
def leftPath : Path (chartLeft g plus GlobalRawBass.plus_projection 0)
    (chartLeft g plus GlobalRawBass.plus_projection 1) where
  toFun := chartLeft g plus GlobalRawBass.plus_projection
  continuous_toFun := (chartLeft g plus GlobalRawBass.plus_projection).continuous
  source' := rfl
  target' := rfl

/-- The whole unpaused inverse chart boundary. -/
def rightPath : Path (chartLeft g minus GlobalRawBass.minus_projection 0)
    (chartLeft g minus GlobalRawBass.minus_projection 1) where
  toFun := chartLeft g minus GlobalRawBass.minus_projection
  continuous_toFun := (chartLeft g minus GlobalRawBass.minus_projection).continuous
  source' := rfl
  target' := rfl

/-- The actual pasted square with all four entire scalar boundaries. -/
def movingSquare : Topology.CarrierPathSquare.Square
    (sourcePath g) (pastedTop g) (leftPath g) (rightPath g) where
  parameter := movingParameter g
  at_zero _ := rfl
  at_one s := (pastedTop_apply g s).symm
  left r := (movingSwap g).apply_zero r
  right r := (movingSwap g).apply_one r

/-- The actual-composite top retains the original five-piece nested association. -/
def actualTop := (firstPlus g).trans
  (((lastPlus g).trans ((overlapTop g).trans (lastMinus g).symm)).trans (firstMinus g).symm)

/-- Exactly the original three-stage five-piece reassociation. -/
def reassociation : (actualTop g).Homotopy (pastedTop g) :=
  Path.Homotopy.spanReassociation (firstPlus g) (lastPlus g) (overlapTop g)
    (lastMinus g).symm (firstMinus g).symm

/-- The selected full relative boundary keeps its collapse, correction, and all original clocks. -/
def boundary : (sourcePath g).Homotopy
    (((leftPath g).trans (actualTop g)).trans (rightPath g).symm) :=
  (movingSquare g).toBoundary.trans
    (((Path.Homotopy.refl (leftPath g)).hcomp (reassociation g).symm).hcomp
      (Path.Homotopy.refl (rightPath g).symm))

/-- The whole final scalar square is the original relative boundary quotient descent. -/
def square : Topology.CarrierPathSquare.Square
    (sourcePath g) (actualTop g) (leftPath g) (rightPath g) :=
  Topology.CarrierPathSquare.boundarySquare (boundary g)

/-- The exact two-time mixed-reference parameter for the selected cylinder word. -/
def parameter := (square g).parameter

/-- Collapse recovers every point of the selected full boundary comparison. -/
theorem parameter_collapse (z : unitInterval × unitInterval) :
    parameter g (Topology.ThreeSideSquare.collapse z) = boundary g z :=
  Topology.CarrierPathSquare.boundaryParameter_collapse (boundary g) z

/-- The complete source edge is the original pasted moving-source path. -/
theorem parameter_zero (s : unitInterval) :
    parameter g (0, s) = movingParameter g (0, s) :=
  (square g).at_zero s

/-- The complete target edge is the actual five-piece composite cylinder word. -/
theorem parameter_one (s : unitInterval) : parameter g (1, s) = actualTop g s :=
  (square g).at_one s

/-- The original positive chart retains its whole unpaused comparison coordinate. -/
theorem parameter_left (q : unitInterval) :
    parameter g (q, 0) = chartLeft g plus GlobalRawBass.plus_projection q :=
  (square g).left q

/-- The independent inverse chart retains the same unchanged comparison coordinate. -/
theorem parameter_right (q : unitInterval) :
    parameter g (q, 1) = chartLeft g minus GlobalRawBass.minus_projection q :=
  (square g).right q

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterWord
