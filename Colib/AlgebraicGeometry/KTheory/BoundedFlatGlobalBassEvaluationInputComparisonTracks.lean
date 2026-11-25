/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpan
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputMap
public import Colib.Topology.Prespectrum.PushoutSquareFilling
public import Colib.Topology.Prespectrum.ConeSquareMapComposition

/-!
# The four original mixed comparison tracks and their full chart squares

The strict input comparison, original pasted raw input comparison, Laurent evaluation, and
unpaused span evaluation define the four actual tracks needed for the mixed square. Original
commuting-square chart surfaces are transported only by whole-level boundary identities.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputComparisonTracks
open GlobalSectionChangeIndex
/-- Precomposition retains every level of the original endpoint-transported homotopy. -/
theorem precomp_cast_level {D E F : Topology.LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} (a : D ⟶ E) (H : Topology.LoopPrespectrum.Homotopy f g)
    (hf : f = f') (hg : g = g') (n : ℕ) :
    (Homotopy.precomp a (H.cast hf hg)).level n = (Homotopy.precomp a H).level n := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original X comparison homotopy is strictly precomposed, with endpoint associations only. -/
def source :
    Homotopy
      (StrictSquare.comparison (sectionSquare Y) ≫
        (sectionMap (laurent.map g) ≫ evaluation (laurent.obj X)))
      ((InputSpan.sectionSpanMap g ≫ spanEvaluation X) ≫ GlobalRawBass.comparison X) :=
  (Homotopy.precomp (InputSpan.sectionSpanMap g) (comparisonHomotopy X)).cast
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ evaluation (laurent.obj X)) (InputSpan.strict_comparison g)).trans
        (Category.assoc _ _ _)))
    (Category.assoc _ _ _).symm

/-- The actual Y evaluation and independent raw input tracks retain their original concatenation. -/
def target :=
  coneSquarePastedHomotopy
    (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison Y)
    (GlobalRawBass.comparison X) (spanEvaluation Y) (evaluation (laurent.obj Y))
    (GlobalRawBass.spanMap g) (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g)

/-- The left boundary is the actual Laurent evaluation on the strict comparison. -/
def left := Homotopy.precomp (StrictSquare.comparison (sectionSquare Y))
  (evaluationComparison (laurent.map g))

/-- The right boundary is the already constructed unpaused whole-span comparison. -/
def right := (inputSpanHomotopy g).postcomp (GlobalRawBass.comparison X)

/-- The complete original positive polynomial chart square, with its actual four boundaries. -/
def plusSquare :
    (Homotopy.precomp (HomotopyPushout.inl (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (source g)).Square
    (Homotopy.precomp (HomotopyPushout.inl (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (target g))
    (Homotopy.precomp (HomotopyPushout.inl (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (left g))
    (Homotopy.precomp (HomotopyPushout.inl (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (right g)) := by
  apply (InputCommutingSquare.square (laurent.map g) (plus.app Y)
    (plus.app X) (polynomial.map g) (plus.naturality g)).ofBoundaryLevels
  · intro n
    rfl
  · intro n
    unfold target coneSquarePastedHomotopy
    rw [precomp_cast_level, Homotopy.precomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rfl
  · intro n
    rfl

/-- The complete inverse chart square retains its separate original geometric route. -/
def minusSquare :
    (Homotopy.precomp (HomotopyPushout.inr (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (source g)).Square
    (Homotopy.precomp (HomotopyPushout.inr (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (target g))
    (Homotopy.precomp (HomotopyPushout.inr (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (left g))
    (Homotopy.precomp (HomotopyPushout.inr (sectionMap (projection.app Y))
      (sectionMap (projection.app Y))) (right g)) := by
  apply (InputCommutingSquare.square (laurent.map g) (minus.app Y)
    (minus.app X) (polynomial.map g) (minus.naturality g)).ofBoundaryLevels
  · intro n
    rfl
  · intro n
    unfold target coneSquarePastedHomotopy
    rw [precomp_cast_level, Homotopy.precomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rfl
  · intro n
    rfl

/-- The source retains every point of the prescribed X descent square at the strict input. -/
theorem source_cylinder (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op Y)).space n) :
    (source g).level n (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
      (sectionMap (projection.app Y)) n (s, x)) =
      (descPasting X).toSquare.level n (r, (s, (sectionMap g).map n x)) := rfl

/-- The right boundary retains the original corrected span cylinder before raw comparison. -/
theorem right_cylinder (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op Y)).space n) :
    (right g).level n (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
      (sectionMap (projection.app Y)) n (s, x)) =
      (GlobalRawBass.comparison X).map n
        ((InputSpan.cylinderSquare g).level n (r, (s, x))) := rfl

/-- Endpoint transports leave the entire original positive chart square unchanged. -/
theorem plusSquare_level (n : ℕ) :
    (plusSquare g).level n =
      (InputCommutingSquare.square (laurent.map g) (plus.app Y)
        (plus.app X) (polynomial.map g) (plus.naturality g)).level n := rfl

/-- The distinct inverse chart square retains both of its original independent times. -/
theorem minusSquare_level (n : ℕ) :
    (minusSquare g).level n =
      (InputCommutingSquare.square (laurent.map g) (minus.app Y)
        (minus.app X) (polynomial.map g) (minus.naturality g)).level n := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputComparisonTracks
