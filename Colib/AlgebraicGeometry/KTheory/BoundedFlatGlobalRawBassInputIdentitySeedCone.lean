/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedCarrier
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveNull
public import Colib.Topology.Path.CarrierConeBoundary
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation

/-!
# Both original cone-interchange surfaces in the global seed carrier

Each sheet keeps its own tip. The actual polynomial movement and unchanged cone cylinder
supply the entire square. Boundary collapse and terminal-pause cancellation recover the
specified positive-support conePasting at every native level and both independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedCone
open CommonReferenceNerve InputIdentitySeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Each Boolean chooses one actual cylinder; their terminal tips remain separate. -/
def cylinder (e : Bool) : C(|nerve (Codiscrete (Node (polyRef g)))| × I, Carrier g) :=
  if e then CutOpenCarrier.cylinderPlus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)
  else CutOpenCarrier.cylinderMinus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- The tip belonging to the selected actual polynomial cylinder. -/
def tip (e : Bool) : Carrier g :=
  if e then CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)
  else CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- Every actual polynomial input ends at the selected tip at cone time one. -/
theorem cylinder_one (e : Bool) (y : |nerve (Codiscrete (Node (polyRef g)))|) :
    cylinder g e (y, 1) = tip g e := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_one _ _ _ _ _ y
  · exact CutOpenCarrier.cylinderPlus_one _ _ _ _ _ y

/-- Native evaluation retains both actual clocks on either sheet. -/
theorem cylinder_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (cylinder g e (movement g r, s)) x =
    (Homotopy.Square.interchange (polynomialSquareHomotopy g)
      (mappingConeHomotopy (InputIdentityPositive.chart X))).level n (r, (s, x)) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.cylinderMinus _ _ _ _ _ (movement g r, s)) x = _
    rw [CutOpenCarrier.nativeEval_cylinderMinus, movement_native]
    rfl
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.cylinderPlus _ _ _ _ _ (movement g r, s)) x = _
    rw [CutOpenCarrier.nativeEval_cylinderPlus, movement_native]
    rfl

/-- The entire original cylinder over any polynomial movement point. -/
def conePath (e : Bool) (r : I) : Path (cylinder g e (movement g r, 0)) (tip g e) where
  toFun s := cylinder g e (movement g r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := cylinder_one g e (movement g r)

/-- The unchanged attached movement edge of the selected cone square. -/
def movementEdge (e : Bool) : Path
    (cylinder g e (movement g 0, 0)) (cylinder g e (movement g 1, 0)) where
  toFun r := cylinder g e (movement g r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Both surfaces are the actual cone cylinder at independent movement and cone times. -/
def square (e : Bool) : CarrierPathSquare.Square
    (conePath g e 0) (conePath g e 1) (movementEdge g e) (Path.refl (tip g e)) where
  parameter := ⟨fun z ↦ cylinder g e (movement g z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := cylinder_one g e (movement g r)

/-- The original cone boundary word includes its exact terminal-pause cancellation. -/
def boundary (e : Bool) : (conePath g e 0).Homotopy
    ((movementEdge g e).trans (conePath g e 1)) := (square g e).coneBoundary

/-- The supported native square retains its original endpoint casts and whole interchange. -/
def nativeSquare (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CarrierPathSquare.Square ((InputIdentityPositiveNull.oldCone g).path n x)
      ((InputIdentityPositiveNull.newCone g).path n x)
      ((InputIdentityPositiveNull.polynomialMovement g).path n x)
      (Path.refl ((mappingCone (InputIdentityPositive.chart X)).point n)) where
  parameter := ⟨fun z ↦ (Homotopy.Square.interchange (polynomialSquareHomotopy g)
    (mappingConeHomotopy (InputIdentityPositive.chart X))).level n (z.1, (z.2, x)), by fun_prop⟩
  at_zero s := (Homotopy.Square.interchange (polynomialSquareHomotopy g)
    (mappingConeHomotopy (InputIdentityPositive.chart X))).at_zero n s x
  at_one s := (Homotopy.Square.interchange (polynomialSquareHomotopy g)
    (mappingConeHomotopy (InputIdentityPositive.chart X))).at_one n s x
  left r := (Homotopy.Square.interchange (polynomialSquareHomotopy g)
    (mappingConeHomotopy (InputIdentityPositive.chart X))).left n r x
  right r := (Homotopy.Square.interchange (polynomialSquareHomotopy g)
    (mappingConeHomotopy (InputIdentityPositive.chart X))).right n r x

/-- Entire-square evaluation retains the full collapse and cancellation of the actual boundary. -/
theorem boundary_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (boundary g e (r, s)) x =
        (nativeSquare g n x).coneBoundary (r, s) :=
  (square g e).coneBoundary_natural (nativeSquare g n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n y x) (fun r s ↦ cylinder_native g e n r s x) r s

private theorem relativeTrans_apply {E F : LoopPrespectrum.{u}}
    {f h : E ⟶ F} {H K L : Homotopy f h}
    (J : H.RelHomotopy K) (J' : K.RelHomotopy L) (n : ℕ) (r s : I) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) = ((J.level n).trans (J'.level n)) (r, (s, x)) := rfl

/-- Both original halves are exactly the specified supported conePasting, without a new recipe. -/
theorem nativeSquare_conePasting (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (nativeSquare g n x).coneBoundary (r, s) =
      (InputIdentityPositiveNull.conePasting g).level n (r, (s, x)) := by
  rw [CarrierPathSquare.Square.coneBoundary_apply]
  unfold InputIdentityPositiveNull.conePasting
  rw [relativeTrans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with h
  · rw [Homotopy.RelHomotopy.ofLevels_apply, Homotopy.Square.toBoundary_apply]
    rfl
  · rw [Homotopy.RelHomotopy.transRefl_apply_path, Homotopy.path_trans]

/-- Each whole carrier boundary recovers the specified supported comparison at all times. -/
theorem boundary_conePasting (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (boundary g e (r, s)) x =
        (InputIdentityPositiveNull.conePasting g).level n (r, (s, x)) :=
  (boundary_native g e n r s x).trans (nativeSquare_conePasting g n r s x)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedCone
