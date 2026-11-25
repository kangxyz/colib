/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientPolynomialComposition
public import Colib.Topology.Prespectrum.HomotopySquareComposition
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy

/-!
# Composition of the actual coefficient polynomial-span maps

The direct-to-composed span comparison uses the original moving geometrical rectangle.
The second part changes only the association of the five cylinder pieces. Both
chart inclusions retain the literal coefficient comparison followed by a pause.
Adapted from `CoefficientBassSpanComposition.lean` in the original BoundedFlat development
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (u : a ⟶ b) (v : b ⟶ c)

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

/-- Rotate the maintained rectangle to the literal moving coefficient-composition boundary. -/
def boundedAboveFlatCoefficientPolynomialCompositionBoundary :=
  BoundedFlatCoefficientTransformationComposition.boundary P (polynomialUnderCoefficient R) u v

/-- The whole square retains direct and composed geometric tracks and both actual side tracks. -/
def boundedAboveFlatCoefficientPolynomialCompositionSquare :=
  (boundedAboveFlatCoefficientPolynomialCompositionBoundary P u v).toSquare

/-- Association casts give the literal composite-vertex span-map interface. -/
def boundedAboveFlatCoefficientPolynomialCompositeDescSquare :=
  (boundedAboveFlatCoefficientPolynomialCompositeSquare P u v).cast (Category.assoc _ _ _) rfl

/-- The composed vertex maps with the original pasted two square tracks. -/
def boundedAboveFlatCoefficientPolynomialCompositeSpanMap :=
  HomotopyPushout.mapOfHomotopies
    (K (polynomialProjection P a))
    (K (polynomialProjection P a))
    (K (polynomialProjection P c))
    (K (polynomialProjection P c))
    (K (coefficientMap P u) ≫
      K (coefficientMap P v))
    (K (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (K (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)

/-- The direct original full span cylinder, without changing its parameterization. -/
def boundedAboveFlatCoefficientPolynomialDirectSpanTrack :=
  HomotopyPushout.mapSquareHomotopy
    (K (polynomialProjection P a))
    (K (polynomialProjection P a))
    (K (polynomialProjection P c))
    (K (polynomialProjection P c))
    (K (coefficientMap P (u ≫ v)))
    (K (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
    (K (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))

/-- The original composite-vertex span cylinder, retaining the two pasted square tracks. -/
def boundedAboveFlatCoefficientPolynomialComposedSpanTrack :=
  HomotopyPushout.mapSquareHomotopy
    (K (polynomialProjection P a))
    (K (polynomialProjection P a))
    (K (polynomialProjection P c))
    (K (polynomialProjection P c))
    (K (coefficientMap P u) ≫
      K (coefficientMap P v))
    (K (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (K (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)

/-- The left native polynomial chart moves through the unchanged original composition track. -/
def boundedAboveFlatCoefficientPolynomialSpanLeftCompositionTrack :=
  (boundedAboveFlatCoefficientPolynomialCompositionHomotopy P u v).postcomp
    (HomotopyPushout.inl
      (K (polynomialProjection P c))
      (K (polynomialProjection P c)))

/-- The right native polynomial chart moves through the same original composition track. -/
def boundedAboveFlatCoefficientPolynomialSpanRightCompositionTrack :=
  (boundedAboveFlatCoefficientPolynomialCompositionHomotopy P u v).postcomp
    (HomotopyPushout.inr
      (K (polynomialProjection P c))
      (K (polynomialProjection P c)))

set_option maxHeartbeats 1200000 in
-- Checking the four endpoint transports unfolds the specialized coefficient prespectrum maps.
/-- The original moving square for one leg, with the literal polynomial boundary maps. -/
def coefficientPolynomialCompositionLegSquare :=
  (boundedAboveFlatCoefficientPolynomialCompositionSquare P u v).ofBoundaryLevels
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)
    (Homotopy.precomp (K (polynomialProjection P a))
      (boundedAboveFlatCoefficientPolynomialCompositionHomotopy P u v))
    ((boundedAboveFlatCoefficientCompositionHomotopy P u v).postcomp
      (K (polynomialProjection P c)))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

set_option maxHeartbeats 1200000 in
-- Checking the literal specialized polynomial leg still unfolds coefficient maps.
/-- The actual two moving polynomial squares and original middle cylinder form a whole square. -/
def boundedAboveFlatCoefficientPolynomialSpanCompositionSquare :=
  HomotopyPushout.identicalLegMovingSquare
    (K (polynomialProjection P a))
    (K (polynomialProjection P c))
    (a₀ := K (coefficientMap P (u ≫ v)))
    (a₁ := K (coefficientMap P u) ≫ K (coefficientMap P v))
    (b₀ := K (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
    (b₁ := K (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedAboveFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedAboveFlatCoefficientCompositionHomotopy P u v)
    (boundedAboveFlatCoefficientPolynomialCompositionHomotopy P u v)
    (coefficientPolynomialCompositionLegSquare P u v)

/-- Direct coefficient composition maps to the actual span with composed vertices and tracks. -/
def boundedAboveFlatCoefficientPolynomialSpanVertexCompositionHomotopy :
    Homotopy (boundedAboveFlatCoefficientPolynomialSpanMap P (u ≫ v))
      (boundedAboveFlatCoefficientPolynomialCompositeSpanMap P u v) :=
  HomotopyPushout.descSquareHomotopy
    (K (polynomialProjection P a))
    (K (polynomialProjection P a))
    (boundedAboveFlatCoefficientPolynomialSpanLeftCompositionTrack P u v)
    (boundedAboveFlatCoefficientPolynomialSpanRightCompositionTrack P u v)
    (boundedAboveFlatCoefficientPolynomialSpanCompositionSquare P u v)

/-- The exact original span-map composite differs only by the proved five-piece
    reparameterization. -/
def boundedAboveFlatCoefficientPolynomialSpanReparameterization :
    Homotopy
      (boundedAboveFlatCoefficientPolynomialSpanMap P u ≫
        boundedAboveFlatCoefficientPolynomialSpanMap P v)
      (boundedAboveFlatCoefficientPolynomialCompositeSpanMap P u v) :=
  HomotopyPushout.identicalLegCompositionHomotopy
    (K (polynomialProjection P a))
    (K (polynomialProjection P b))
    (K (polynomialProjection P c))
    (K (coefficientMap P u))
    (K (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (K (coefficientMap P v))
    (K (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P u)
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P v)

/-- Whole composition of the actual original native coefficient polynomial-span maps.
The first stage is the existing geometric rectangle; the second retains all five original
cylinder pieces and removes only their differing parenthesization in homotopy time. -/
def boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy :
    Homotopy (boundedAboveFlatCoefficientPolynomialSpanMap P (u ≫ v))
      (boundedAboveFlatCoefficientPolynomialSpanMap P u ≫
        boundedAboveFlatCoefficientPolynomialSpanMap P v) :=
  (boundedAboveFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).trans
    (boundedAboveFlatCoefficientPolynomialSpanReparameterization P u v).symm

private theorem coefficientTransLevelAlong {D E F : LoopPrespectrum.{u}}
    {f₀ f₁ f₂ : E ⟶ F} {g₀ g₁ g₂ : D ⟶ F}
    (H : Homotopy f₀ f₁) (J : Homotopy f₁ f₂)
    (H' : Homotopy g₀ g₁) (J' : Homotopy g₁ g₂)
    (n : ℕ) (r : unitInterval) (i : D.space n → E.space n) (x : D.space n)
    (h : ∀ t : unitInterval, H.level n (t, i x) = H'.level n (t, x))
    (j : ∀ t : unitInterval, J.level n (t, i x) = J'.level n (t, x)) :
    (H.trans J).level n (r, i x) = (H'.trans J').level n (r, x) := by
  change ((H.levelHomotopy n).trans (J.levelHomotopy n)) (r, i x) =
    ((H'.levelHomotopy n).trans (J'.levelHomotopy n)) (r, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact h _
  · exact j _

/-- The original left chart follows its whole coefficient composition track, then the fixed face. -/
theorem boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy_inl
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
      (r, (HomotopyPushout.inl
        (K (polynomialProjection P a))
        (K (polynomialProjection P a))).map n x) =
      ((boundedAboveFlatCoefficientPolynomialSpanLeftCompositionTrack P u v).trans
        (Topology.LoopPrespectrum.Homotopy.refl
          ((K
              (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
            K
              (coefficientMap P ((polynomialUnderFunctor R).map v))) ≫
              HomotopyPushout.inl
                (K (polynomialProjection P c))
                (K (polynomialProjection P c))))).level n (r,
                    x) := by
  refine coefficientTransLevelAlong _ _ _ _ n r _ x ?_ ?_
  · intro t
    unfold boundedAboveFlatCoefficientPolynomialSpanVertexCompositionHomotopy
    exact HomotopyPushout.descSquareHomotopy_inl _ _
      (boundedAboveFlatCoefficientPolynomialSpanLeftCompositionTrack P u v)
      (boundedAboveFlatCoefficientPolynomialSpanRightCompositionTrack P u v)
      (boundedAboveFlatCoefficientPolynomialSpanCompositionSquare P u v) n t x
  · intro t
    unfold boundedAboveFlatCoefficientPolynomialSpanReparameterization
    rfl

/-- The distinct original right chart retains the same composition time and its own inclusion. -/
theorem boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy_inr
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
      (r, (HomotopyPushout.inr
        (K (polynomialProjection P a))
        (K (polynomialProjection P a))).map n x) =
      ((boundedAboveFlatCoefficientPolynomialSpanRightCompositionTrack P u v).trans
        (Topology.LoopPrespectrum.Homotopy.refl
          ((K
              (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
            K
              (coefficientMap P ((polynomialUnderFunctor R).map v))) ≫
              HomotopyPushout.inr
                (K (polynomialProjection P c))
                (K (polynomialProjection P c))))).level n (r,
                    x) := by
  refine coefficientTransLevelAlong _ _ _ _ n r _ x ?_ ?_
  · intro t
    unfold boundedAboveFlatCoefficientPolynomialSpanVertexCompositionHomotopy
    exact HomotopyPushout.descSquareHomotopy_inr _ _
      (boundedAboveFlatCoefficientPolynomialSpanLeftCompositionTrack P u v)
      (boundedAboveFlatCoefficientPolynomialSpanRightCompositionTrack P u v)
      (boundedAboveFlatCoefficientPolynomialSpanCompositionSquare P u v) n t x
  · intro t
    unfold boundedAboveFlatCoefficientPolynomialSpanReparameterization
    rfl

end AlgebraicGeometry.Scheme.Modules
