/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare
public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# The geometric polynomial and Laurent Bass square on an arbitrary scheme

The two polynomial legs and the Laurent overlap use the actual integer-base products and the
bounded-above flat perfect pullback. The two geometric composition tracks join along the common
Laurent projection, with the positive track reversed. The resulting comparison is objectwise:
no strict functoriality or identification with the coefficient-algebra construction is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.RingedSpace Scheme.Products Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass

/-- The projection from the actual integer-base Laurent product. -/
def laurentProjection : laurent.{u} ⟶ 𝟭 Scheme.{u} :=
  baseProductProjection (Scheme.PolynomialLaurent.laurentProjection (.of (ULift.{u} ℤ)))

/-- The positive chart has the common Laurent projection to the base. -/
theorem plus_projection (X : Scheme.{u}) :
    plus.app X ≫ projection.app X = laurentProjection.app X :=
  baseProductTransformation_projection _ _ _ _ X

/-- The inverse-coordinate chart has the same Laurent projection to the base. -/
theorem minus_projection (X : Scheme.{u}) :
    minus.app X ≫ projection.app X = laurentProjection.app X :=
  baseProductTransformation_projection _ _ _ _ X

/-- The original split geometric composition track of the positive chart. -/
def plusHomotopy (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (plus.app X) (projection.app X)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (plus_projection X)) rfl

/-- The original split geometric composition track of the inverse-coordinate chart. -/
def minusHomotopy (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (minus.app X) (projection.app X)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (minus_projection X)) rfl

/-- The signed two-chart overlap with the original concatenation times. -/
def squareHomotopy (X : Scheme.{u}) :=
  (plusHomotopy X).symm.trans (minusHomotopy X)

/-- The actual polynomial span is the reduced double cylinder of the two projections. -/
def span (X : Scheme.{u}) : LoopPrespectrum.{u+1} :=
  HomotopyPushout.prespectrum (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))

/-- Descend the two chart maps and their overlap to the actual Laurent prespectrum. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassSquare.lean:46-85"
  "adaptation" "The original integer-base span comparison and signed cylinder on every scheme"]
def comparison (X : Scheme.{u}) :
    span X ⟶
      originalPrespectrum (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace) :=
  HomotopyPushout.desc (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X)) (squareHomotopy X)

/-- The left inclusion is sent to the actual positive chart pullback. -/
theorem comparison_inl (X : Scheme.{u}) :
    HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫ comparison X =
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X) :=
  HomotopyPushout.inl_desc _ _ _ _ _

/-- The right inclusion is sent to the actual inverse-coordinate chart pullback. -/
theorem comparison_inr (X : Scheme.{u}) :
    HomotopyPushout.inr (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫ comparison X =
        boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X) :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- Every point of the overlap cylinder evaluates along the specified two-chart track. -/
theorem comparison_cylinder (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    (comparison X).map n
      (HomotopyPushout.cylinder (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) n (s, x)) =
      (squareHomotopy X).level n (s, x) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
