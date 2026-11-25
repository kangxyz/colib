/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputCompositionSpan

/-! Whole-boundary regressions for actual global polynomial-span composition. -/

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalRawBass
open Path.CarrierHalfPaths
open scoped Topology unitInterval

universe u

noncomputable section

namespace ColibTest.BoundedFlatGlobalRawBassInputCompositionSpan

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The pilot uses the actual direct span map and actual composite, not replaced maps. -/
def originalSpanComposition : Homotopy (spanMap (f ≫ g)) (spanMap g ≫ spanMap f) :=
  InputCompositionSpan.homotopy f g

/-- The geometric lower side is precisely the original polynomial composition track. -/
theorem polynomial_bottom (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)).space n) :
    (InputCompositionPolynomial.square f g).level n (r, (0, x)) =
      (InputCompositionPolynomial.targetTrack f g).level n (r, x) :=
  (InputCompositionPolynomial.square f g).left n r x

/-- The entire first-half cylinder recovers the selected moving square. -/
theorem whole_cylinder_first (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)).space n) :
    (originalSpanComposition f g).level n
      (lower r,
        HomotopyPushout.cylinder
          (K (projection.app Z))
          (K (projection.app Z)) n (s, x)) =
      (InputCompositionSpan.movingSquare f g).level n (r, (s, x)) :=
  InputCompositionSpan.homotopy_cylinder_lower f g n r s x

/-- The second half keeps the actual five-piece cylinder reassociation in reverse. -/
theorem whole_cylinder_second (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)).space n) :
    (originalSpanComposition f g).level n
      (upper r,
        HomotopyPushout.cylinder
          (K (projection.app Z))
          (K (projection.app Z)) n (s, x)) =
      (HomotopyPushout.identicalLegCompositionPasting
        (K (projection.app Z))
        (K (projection.app Y))
        (K (projection.app X))
        (K g)
        (K (polynomial.map g))
        (K f)
        (K (polynomial.map f))
        (polynomialSquareHomotopy g) (polynomialSquareHomotopy f)).level n
          (unitInterval.symm r, (s, x)) :=
  InputCompositionSpan.homotopy_cylinder_upper f g n r s x

/-- Comparison and prespectrum structure parameters remain independent on every span point. -/
theorem independent_structure (n : ℕ) (r t : unitInterval) (x : (span Z).space n) :
    (originalSpanComposition f g).level (n + 1) (r, (span Z).structureMap n x t) =
      (span X).structureMap n ((originalSpanComposition f g).level n (r, x)) t :=
  InputCompositionSpan.homotopy_structure f g n r t x

/-- The positive chart pair has the original Laurent source map literally. -/
def positivePair (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (plus.app X)) :=
  InputCompositionSpan.positiveProjection X

/-- Every initial point of the positive pilot is the actual Laurent input span map. -/
theorem positive_source (X : Scheme.{u}) (n : ℕ) (x : (span X).space n) :
    (positivePair X).level n (0, x) = (spanMap (laurentProjection.app X)).map n x :=
  (positivePair X).at_zero n x

/-- Every final point of the positive pilot is the unchanged two-map composite. -/
theorem positive_target (X : Scheme.{u}) (n : ℕ) (x : (span X).space n) :
    (positivePair X).level n (1, x) =
      (spanMap (plus.app X)).map n ((spanMap (projection.app X)).map n x) :=
  (positivePair X).at_one n x

/-- The inverse-coordinate pair uses its own actual minus map in the same whole producer. -/
def inversePair (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (minus.app X)) :=
  (InputCompositionSpan.homotopy (minus.app X) (projection.app X)).cast
    (congrArg spanMap (minus_projection X)) rfl


/-- The same whole structure law at the actual zeroth space. -/
example (r t : unitInterval) (x : (span Z).space 0) :
    (originalSpanComposition f g).level 1 (r, (span Z).structureMap 0 x t) =
      (span X).structureMap 0 ((originalSpanComposition f g).level 0 (r, x)) t :=
  independent_structure f g 0 r t x

end ColibTest.BoundedFlatGlobalRawBassInputCompositionSpan
