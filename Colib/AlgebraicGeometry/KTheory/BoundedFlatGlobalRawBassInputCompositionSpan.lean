/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputCompositionPolynomial
public import Colib.Topology.Path.CarrierHalfPaths
public import Colib.Topology.Prespectrum.HomotopySquareComposition
public import Colib.Topology.Prespectrum.PushoutHomotopySquareCells
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Util.References

/-!
# Whole composition of the original global polynomial-span maps

First move the three actual vertices by the geometric rectangle. The fixed five-piece
cylinder reassociation then recovers the literal composite of the existing span maps.
Both chart paths retain their terminal pause. No composition of the cone or looped step
is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace
open Path.CarrierHalfPaths
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionSpan

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Association casts give the literal composite-vertex span-map interface. -/
def pastedSquare :=
  (InputCompositionPolynomial.compositeSquare f g).cast (Category.assoc _ _ _) rfl

/-- The composed vertex maps with the original pasted two square tracks. -/
def pastedSpan :=
  HomotopyPushout.mapOfHomotopies
    (K (projection.app Z))
    (K (projection.app Z))
    (K (projection.app X))
    (K (projection.app X))
    (K g ≫
      K f)
    (K (polynomial.map g) ≫
      K (polynomial.map f))
    (K (polynomial.map g) ≫
      K (polynomial.map f))
    (pastedSquare f g)
    (pastedSquare f g)

/-- The direct original full span cylinder, without changing its parameterization. -/
def directTrack :=
  HomotopyPushout.mapSquareHomotopy
    (K (projection.app Z))
    (K (projection.app Z))
    (K (projection.app X))
    (K (projection.app X))
    (K (f ≫ g))
    (K (polynomial.map (f ≫ g)))
    (K (polynomial.map (f ≫ g)))
    (polynomialSquareHomotopy (f ≫ g))
    (polynomialSquareHomotopy (f ≫ g))

/-- The original composite-vertex span cylinder, retaining the two pasted square tracks. -/
def pastedTrack :=
  HomotopyPushout.mapSquareHomotopy
    (K (projection.app Z))
    (K (projection.app Z))
    (K (projection.app X))
    (K (projection.app X))
    (K g ≫
      K f)
    (K (polynomial.map g) ≫
      K (polynomial.map f))
    (K (polynomial.map g) ≫
      K (polynomial.map f))
    (pastedSquare f g)
    (pastedSquare f g)

/-- The left native polynomial chart moves through the unchanged original composition track. -/
def leftTrack :=
  (InputCompositionPolynomial.polynomialComposition f g).postcomp
    (HomotopyPushout.inl
      (K (projection.app X))
      (K (projection.app X)))

/-- The right native polynomial chart moves through the same original composition track. -/
def rightTrack :=
  (InputCompositionPolynomial.polynomialComposition f g).postcomp
    (HomotopyPushout.inr
      (K (projection.app X))
      (K (projection.app X)))

/-- The actual two moving polynomial squares and original middle cylinder form a whole square. -/
def movingSquare :
    (directTrack f g).Square
      (pastedTrack f g)
      (Homotopy.precomp (K (projection.app Z))
        (leftTrack f g))
      (Homotopy.precomp (K (projection.app Z))
        (rightTrack f g)) := by
  let S := (InputCompositionPolynomial.square f g).ofBoundaryLevels
    (polynomialSquareHomotopy (f ≫ g))
    (pastedSquare f g)
    (Homotopy.precomp (K (projection.app Z))
      (InputCompositionPolynomial.polynomialComposition f g))
    (InputCompositionPolynomial.sourceTrack f g)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact HomotopyPushout.identicalLegMovingSquare
    (K (projection.app Z))
    (K (projection.app X))
    (polynomialSquareHomotopy (f ≫ g))
    (pastedSquare f g)
    (InputCompositionPolynomial.sourceComposition f g)
    (InputCompositionPolynomial.polynomialComposition f g) S

/-- Direct scheme composition maps to the actual span with composed vertices and tracks. -/
def vertexHomotopy :
    Homotopy (spanMap (f ≫ g))
      (pastedSpan f g) :=
  HomotopyPushout.descSquareHomotopy
    (K (projection.app Z))
    (K (projection.app Z))
    (leftTrack f g)
    (rightTrack f g)
    (movingSquare f g)

/-- The exact original span-map composite differs only by the proved five-piece
    reparameterization. -/
def reparameterization :
    Homotopy
      (spanMap g ≫ spanMap f)
      (pastedSpan f g) :=
  HomotopyPushout.identicalLegCompositionHomotopy
    (K (projection.app Z))
    (K (projection.app Y))
    (K (projection.app X))
    (K g)
    (K (polynomial.map g))
    (K f)
    (K (polynomial.map f))
    (polynomialSquareHomotopy g)
    (polynomialSquareHomotopy f)

/-- Whole composition of the actual original global polynomial-span maps.
The first stage is the existing geometric rectangle; the second retains all five original
cylinder pieces and removes only their differing parenthesization in homotopy time. -/
@[colib_tag "COL-1342"]
def homotopy :
    Homotopy (spanMap (f ≫ g))
      (spanMap g ≫ spanMap f) :=
  (vertexHomotopy f g).trans
    (reparameterization f g).symm

/-- The original left chart follows its whole scheme composition track, then the fixed face. -/
theorem homotopy_inl
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj Z).toRingedSpace)).space n) :
    (homotopy f g).level n
      (r, (HomotopyPushout.inl
        (K (projection.app Z))
        (K (projection.app Z))).map n x) =
      ((leftTrack f g).trans
        (Topology.LoopPrespectrum.Homotopy.refl
          ((K
              (polynomial.map g) ≫
            K
              (polynomial.map f)) ≫
              HomotopyPushout.inl
                (K (projection.app X))
                (K (projection.app X))))).level n (r,
                    x) := by
  change (((vertexHomotopy f g).levelHomotopy
      n).trans
    (((reparameterization f g).symm).levelHomotopy n)) _ =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) _
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- The distinct original right chart retains the same composition time and its own inclusion. -/
theorem homotopy_inr
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj Z).toRingedSpace)).space n) :
    (homotopy f g).level n
      (r, (HomotopyPushout.inr
        (K (projection.app Z))
        (K (projection.app Z))).map n x) =
      ((rightTrack f g).trans
        (Topology.LoopPrespectrum.Homotopy.refl
          ((K
              (polynomial.map g) ≫
            K
              (polynomial.map f)) ≫
              HomotopyPushout.inr
                (K (projection.app X))
                (K (projection.app X))))).level n (r,
                    x) := by
  change (((vertexHomotopy f g).levelHomotopy
      n).trans
    (((reparameterization f g).symm).levelHomotopy n)) _ =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) _
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- Every first-half cylinder point is the complete original moving polynomial square. -/
theorem homotopy_cylinder_lower (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)).space n) :
    (homotopy f g).level n
      (lower r,
        HomotopyPushout.cylinder
          (K (projection.app Z))
          (K (projection.app Z)) n (s, x)) =
      (movingSquare f g).level n (r, (s, x)) :=
  Topology.LoopPrespectrum.Homotopy.trans_lower_cell (vertexHomotopy f g)
    (reparameterization f g).symm n r _

/-- The exact five-piece reassociation is retained on every second-half cylinder point. -/
theorem homotopy_cylinder_upper (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)).space n) :
    (homotopy f g).level n
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
  Topology.LoopPrespectrum.Homotopy.trans_upper_cell (vertexHomotopy f g)
    (reparameterization f g).symm n r _

/-- The complete span homotopy commutes with an independent prespectrum structure time. -/
theorem homotopy_structure (n : ℕ) (r t : unitInterval) (x : (span Z).space n) :
    (homotopy f g).level (n + 1) (r, (span Z).structureMap n x t) =
      (span X).structureMap n ((homotopy f g).level n (r, x)) t :=
  (homotopy f g).comm n r x t

/-- The positive projection pair gives a whole original span composition on its literal source. -/
def positiveProjection (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (plus.app X)) :=
  (homotopy (plus.app X) (projection.app X)).cast
    (congrArg spanMap (plus_projection X)) rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionSpan
