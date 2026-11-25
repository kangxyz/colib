/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare
public import Colib.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Maps on the global raw Bass polynomial span

An arbitrary scheme morphism acts on the actual two-chart span via its polynomial
projection square. The signed Laurent and common projection tracks retain the
original composition normalization; no cone or step map is constructed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original polynomial square uses actual bounded-flat pullback for an arbitrary map. -/
def polynomialSquareHomotopy : Homotopy
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (projection.naturality g)

/-- Arbitrary scheme change supplies an actual map of the two polynomial-chart pushouts. -/
def spanMap :
    HomotopyPushout.prespectrum (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)) ⟶
      HomotopyPushout.prespectrum (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (polynomialSquareHomotopy g) (polynomialSquareHomotopy g)

/-- The original left polynomial-chart endpoint is retained literally. -/
@[simp]
theorem inl_spanMap :
    HomotopyPushout.inl _ _ ≫ spanMap g =
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
        HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right polynomial-chart endpoint is retained literally. -/
@[simp]
theorem inr_spanMap :
    HomotopyPushout.inr _ _ ≫ spanMap g =
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
        HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the original pasted geometric comparison tracks. -/
theorem spanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (spanMap g).map n
      (HomotopyPushout.cylinder (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)) n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (polynomialSquareHomotopy g) (polynomialSquareHomotopy g)).level n (s, x) := rfl

/-- The positive Laurent chart retains its actual geometric square. -/
def plusSquareHomotopy : Homotopy
    (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app Y) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (plus.naturality g)

/-- The inverse-coordinate Laurent chart retains its actual geometric square. -/
def minusSquareHomotopy : Homotopy
    (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app Y) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (minus.naturality g)

/-- The original outer Laurent projection square is common to both chart diagrams. -/
def laurentSquareHomotopy :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (laurent.map g)
    (laurentProjection.app Y) (laurentProjection.app X) g
      (laurentProjection.naturality g)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
