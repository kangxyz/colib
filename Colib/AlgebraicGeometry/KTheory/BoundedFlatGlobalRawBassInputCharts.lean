/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputSpan
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareProjection

/-!
# The two global Bass comparisons along an arbitrary scheme map

The actual polynomial and both signed Laurent squares paste to the same outer
projection square. The comparisons specialize the original native double-square
track, with the chosen positive and inverse coordinate maps unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Paste the original plus Laurent square and the original polynomial square. -/
def plusInputLeftTrack :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquareHomotopy g).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The plus route through the common original Laurent projection square. -/
def plusInputRightTrack :=
  ((plusHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))).symm.trans
    ((laurentSquareHomotopy g).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original plus scheme-arrow tracks and common outer square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputCharts.lean:95-159"
  "adaptation" "Original scheme-arrow chart comparisons to the common Laurent projection"]
def plusInputPasting :
    (plusInputLeftTrack g).RelHomotopy
      (plusInputRightTrack g) :=
  DoubleSquareTrack.projectionComparison (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g
    (polynomial.map g) (laurent.map g)
    (projection.naturality g)
      (plus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (plus_projection Y) (plus_projection X)

/-- Paste the original minus Laurent square and the original polynomial square. -/
def minusInputLeftTrack :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (minusSquareHomotopy g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquareHomotopy g).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X)))

/-- The minus route through the common original Laurent projection square. -/
def minusInputRightTrack :=
  ((minusHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))).symm.trans
    ((laurentSquareHomotopy g).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (minusHomotopy X)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original minus scheme-arrow tracks and common outer square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputCharts.lean:95-159"
  "adaptation" "Original scheme-arrow chart comparisons to the common Laurent projection"]
def minusInputPasting :
    (minusInputLeftTrack g).RelHomotopy
      (minusInputRightTrack g) :=
  DoubleSquareTrack.projectionComparison (projection.app Y) (minus.app Y)
    (projection.app X) (minus.app X) g
    (polynomial.map g) (laurent.map g)
    (projection.naturality g)
      (minus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (minus_projection Y) (minus_projection X)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
