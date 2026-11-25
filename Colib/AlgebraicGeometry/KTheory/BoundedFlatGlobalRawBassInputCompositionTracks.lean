/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputSpan

/-!
# The actual two-arrow tracks for the raw Bass polynomial span

The source and polynomial composition tracks and the successive projection squares
retain their original order and association casts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionPolynomial
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual source geometric composition, in contravariant order. -/
def sourceComposition := boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g

/-- Polynomial composition uses the original split track and genuine functor composition. -/
def polynomialComposition :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map (f ≫ g)))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map f)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
    (polynomial.map f) (polynomial.map g)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map_comp f g)).symm rfl

/-- The two successive original polynomial squares with their unchanged associations. -/
def compositeSquare :=
  ((polynomialSquareHomotopy g).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map f))).trans
    ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
      (polynomialSquareHomotopy f)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- The original source composition followed by the actual target projection. -/
def sourceTrack :=
  (sourceComposition f g).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))

/-- The actual polynomial composition under the unchanged source projection. -/
def targetTrack :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Z))
    (polynomialComposition f g)).cast rfl (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionPolynomial
