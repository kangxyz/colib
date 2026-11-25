/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareMergedLifts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareRectangleParameter
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction

/-!
# The native double-square rectangle evaluated in its merged simplex

The three transported pullback comparisons evaluate to the entire original pasting word,
including each prespectrum level and both independent times. Adapted from Quillen
`BoundedFlat/SquareTrack.lean` and `BoundedFlat/DoubleSquareRectangleNative.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace BoundedFlatPerfectDoubleSquareScalarPaths

open SimplexParameters
open BoundedFlatPerfectDoubleSquareMergedSimplex (simplex first_native middle_native last_native)
open BoundedFlatPerfectDoubleSquareTrack (firstTriple middleTriple lastTriple)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Every level and both times of the actual original three-route comparison are one common
simplex scalar homotopy. This retains the native endpoint transports and full pasting word. -/
theorem rectangle_nativeLift :
    HomotopyLift (simplex p q p' q' a b c hp hq)
      rectangleParameter
      (boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq) := by
  let S := simplex p q p' q' a b c hp hq
  have hf : HomotopyLift S firstComparison
      (firstTriple (p := p) (q := q) (c := c)) :=
    first_native p q p' q' a b c hp hq
  have hm : HomotopyLift S middleComparison
      (middleTriple p q q' b c hq) :=
    middle_native p q p' q' a b c hp hq
  have hl : HomotopyLift S lastComparison
      (lastTriple p q p' q' a b c hp hq) :=
    last_native p q p' q' a b c hp hq
  have lC := PathLift.trans_left S (HomotopyLift.source S hf)
  have lD := PathLift.trans_right S (HomotopyLift.source S hf)
  have lE := PathLift.trans_left S (HomotopyLift.target S hf)
  have lF := PathLift.trans_right S (HomotopyLift.target S hf)
  have lG := PathLift.trans_left S (HomotopyLift.source S hm)
  have lH := PathLift.trans_right S (HomotopyLift.source S hm)
  have lI := PathLift.trans_right S (HomotopyLift.target S hm)
  have lJ := PathLift.trans_left S (HomotopyLift.target S hl)
  have lK := PathLift.trans_right S (HomotopyLift.target S hl)
  have lL := PathLift.trans_right S (HomotopyLift.source S hl)
  exact HomotopyLift.threeRoutes S lC lD lE lF lG lH lI lJ lK lL hf hm hl

/-- The resulting equality has the exact native all-level rectangle as its right side. -/
theorem rectangle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (rectangleParameter (r, s), x) =
      (boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq).level n
        (r, (s, x)) :=
  rectangle_nativeLift p q p' q' a b c hp hq n r s x

end BoundedFlatPerfectDoubleSquareScalarPaths

end AlgebraicGeometry.Scheme.Modules
