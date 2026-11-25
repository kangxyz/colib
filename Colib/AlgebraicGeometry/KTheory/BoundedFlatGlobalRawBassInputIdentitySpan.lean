/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare

/-!
# The original global raw polynomial-span identity

The actual geometric unit square supplies the identity of the whole original polynomial
double cylinder. Both chart tracks retain the original split identity homotopy, and the
cylinder retains the full unit square. This does not construct the Bass comparison identity
square or a whole raw Bass step identity.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
variable (X : Scheme.{u})

/-- The original polynomial identity includes its actual functorial identity transport. -/
def polynomialHomotopy :
    Homotopy (K (polynomial.map (𝟙 X)))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
        (polynomial.obj X).toRingedSpace))) :=
  (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy (polynomial.obj X)).cast
    (congrArg K (polynomial.map_id X)).symm rfl

/-- The original Laurent identity retains its geometric and normalization pieces. -/
def laurentHomotopy :
    Homotopy (K (laurent.map (𝟙 X)))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
        (laurent.obj X).toRingedSpace))) :=
  (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy (laurent.obj X)).cast
    (congrArg K (laurent.map_id X)).symm rfl

/-- The actual polynomial square contracts through the two original geometric identity tracks. -/
def polynomialSquare :
    (polynomialSquareHomotopy (𝟙 X)).Square
      (coneSquareIdentityTrack (K (projection.app X)))
      (Homotopy.precomp (K (projection.app X))
        (polynomialHomotopy X))
      ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).postcomp
        (K (projection.app X))) := by
  refine (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (projection.app X)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {A B : Scheme.{u}} (f : A ⟶ B) (p : A ⟶ A)
      (hp : p = 𝟙 A) (h : p ≫ f = f ≫ 𝟙 B) :
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p f f (𝟙 B) h).level n =
        (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (𝟙 A) f f (𝟙 B)
          (by simp)).level n := by
    subst p
    rfl
  exact transport (projection.app X) _ (polynomial.map_id X) _

/-- The entire original polynomial cylinder moves with both unchanged chart identity tracks. -/
def spanCylinderSquare :=
  HomotopyPushout.identicalLegIdentityCylinderSquare
    (K (projection.app X))
    (polynomialSquareHomotopy (𝟙 X))
    (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X) (polynomialHomotopy X)
    (polynomialSquare X)

/-- Descent gives the identity of the actual raw span map, without replacing its cylinder. -/
def spanHomotopy : Homotopy (spanMap (𝟙 X)) (𝟙 (span X)) :=
  HomotopyPushout.identicalLegIdentityHomotopy
    (K (projection.app X))
    (polynomialSquareHomotopy (𝟙 X))
    (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X) (polynomialHomotopy X)
    (polynomialSquare X)

/-- Every positive-chart time is exactly the original polynomial identity time. -/
theorem spanHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace)).space n) :
    (spanHomotopy X).level n
      (r, (HomotopyPushout.inl (K (projection.app X))
        (K (projection.app X))).map n x) =
      (HomotopyPushout.inl (K (projection.app X))
        (K (projection.app X))).map n
          ((polynomialHomotopy X).level n (r, x)) := rfl

/-- Every inverse-chart time is the same unchanged polynomial identity time. -/
theorem spanHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace)).space n) :
    (spanHomotopy X).level n
      (r, (HomotopyPushout.inr (K (projection.app X))
        (K (projection.app X))).map n x) =
      (HomotopyPushout.inr (K (projection.app X))
        (K (projection.app X))).map n
          ((polynomialHomotopy X).level n (r, x)) := rfl

/-- The whole original overlap keeps both independent coordinates of its constructed square. -/
theorem spanHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    (spanHomotopy X).level n
      (r, HomotopyPushout.cylinder (K (projection.app X))
        (K (projection.app X)) n (s, x)) =
      (spanCylinderSquare X).level n (r, (s, x)) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
