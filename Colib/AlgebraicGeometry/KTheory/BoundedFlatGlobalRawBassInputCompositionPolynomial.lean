/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputCompositionTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareOriginal
public import Colib.Topology.Prespectrum.HomotopySquareComposition
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# The native polynomial composition rectangle for arbitrary schemes

Specialize the whole geometric double-square comparison to the three actual projections.
Identifying its levels and rotating the relative track retains the original boundary times.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionPolynomial

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "squareTrack" => boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy

private theorem squareReverse_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (squareTrack q w p v h.symm).symm.level n = (squareTrack p v q w h).level n := by
  exact Homotopy.reverseTwoRoutes_level
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v)
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w)
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h) n

private theorem squareCongr_level {X Y Z T : Scheme.{u}}
    {p p' : X ⟶ Y} {v v' : Y ⟶ Z} {q q' : X ⟶ T} {w w' : T ⟶ Z}
    (h : p ≫ v = q ≫ w) (h' : p' ≫ v' = q' ≫ w')
    (hp : p = p') (hv : v = v') (hq : q = q') (hw : w = w') (n : ℕ) :
    (squareTrack p v q w h).level n = (squareTrack p' v' q' w' h').level n := by
  subst p'
  subst v'
  subst q'
  subst w'
  rfl

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The maintained whole geometric rectangle on the actual three polynomial projections. -/
def rectangle :=
  DoubleSquareTrack.originalComparison g f (polynomial.map g) (polynomial.map f)
    (projection.app Z) (projection.app Y) (projection.app X)
    (projection.naturality g).symm (projection.naturality f).symm

/-- Every initial rectangle value is the two original successive polynomial squares. -/
theorem rectangle_source_level (n : ℕ) :
    (compositeSquare f g).level n = (((rectangle f g).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold DoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  unfold compositeSquare
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (squareReverse_level
      (polynomial.map g) (projection.app Z) (projection.app Y) g
      (projection.naturality g) n).symm
  · change (Homotopy.precomp (K g)
      (polynomialSquareHomotopy f)).level n =
        (Homotopy.precomp (K g)
          (squareTrack
            (projection.app X) f (polynomial.map f) (projection.app Y)
            (projection.naturality f).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (squareReverse_level
      (polynomial.map f) (projection.app Y) (projection.app X) f
      (projection.naturality f) n).symm

/-- The full terminal rectangle retains the direct square and both composition tracks. -/
theorem rectangle_target_level (n : ℕ) :
    (((targetTrack f g).symm.trans (polynomialSquareHomotopy (f ≫ g))).trans
      (sourceTrack f g)).level n = (((rectangle f g).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold DoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (squareReverse_level
        (polynomial.map (f ≫ g)) (projection.app Z) (projection.app X) (f ≫ g)
        (projection.naturality (f ≫ g)) n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact squareCongr_level _ _ rfl rfl
        (polynomial.map_comp f g) rfl n
  · rfl

/-- The original geometric rectangle gives the complete polynomial composition comparison. -/
def comparison :
    (compositeSquare f g).RelHomotopy
      (((targetTrack f g).symm.trans (polynomialSquareHomotopy (f ≫ g))).trans
        (sourceTrack f g)) :=
  Homotopy.RelHomotopy.ofLevels (rectangle f g).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using rectangle_source_level f g n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using rectangle_target_level f g n)

/-- Rotate the actual rectangle to the direct-to-composite moving-square boundary. -/
def boundary :
    (polynomialSquareHomotopy (f ≫ g)).RelHomotopy
      (((targetTrack f g).trans (compositeSquare f g)).trans (sourceTrack f g).symm) := by
  let B := targetTrack f g
  let A := sourceTrack f g
  let H := polynomialSquareHomotopy (f ≫ g)
  let C := compositeSquare f g
  have J := comparison f g
  have route : (B.trans C).RelHomotopy (H.trans A) :=
    ((Homotopy.RelHomotopy.refl B).hcomp J).trans
      (((Homotopy.RelHomotopy.transAssoc B (B.symm.trans H) A).symm).trans
        ((((Homotopy.RelHomotopy.transAssoc B B.symm H).symm).hcomp
          (Homotopy.RelHomotopy.refl A)).trans
          ((((Homotopy.RelHomotopy.reflTransSymm B).symm.hcomp
            (Homotopy.RelHomotopy.refl H)).hcomp (Homotopy.RelHomotopy.refl A)).trans
            ((Homotopy.RelHomotopy.reflTrans H).hcomp (Homotopy.RelHomotopy.refl A)))))
  exact (Homotopy.RelHomotopy.transRefl H).symm.trans
    (((Homotopy.RelHomotopy.refl H).hcomp (Homotopy.RelHomotopy.reflTransSymm A)).trans
      (((Homotopy.RelHomotopy.transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (Homotopy.RelHomotopy.refl A.symm))))

/-- The actual whole polynomial composition square, with both original geometric sides. -/
def square := (boundary f g).toSquare

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputCompositionPolynomial
