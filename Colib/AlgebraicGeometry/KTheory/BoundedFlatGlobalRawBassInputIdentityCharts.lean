/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySpan

/-!
# Both original global raw Bass identity chart faces

The original geometric unit squares produce both complete chart restrictions of the Bass
comparison identity square, with the actual span identity and Laurent identity tracks.
The three-parameter overlap cube needed for the whole comparison square is not asserted.
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

/-- The positive Laurent square has both entire original geometric identity tracks. -/
def plusSquare :
    (plusSquareHomotopy (𝟙 X)).Square
      (coneSquareIdentityTrack (K (plus.app X)))
      (Homotopy.precomp (K (plus.app X))
        (laurentHomotopy X))
      ((polynomialHomotopy X).postcomp (K (plus.app X))) := by
  refine (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (plus.app X)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {A B : Scheme.{u}} (f : A ⟶ B) (p : A ⟶ A) (w : B ⟶ B)
      (hp : p = 𝟙 A) (hw : w = 𝟙 B) (h : p ≫ f = f ≫ w) :
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p f f w h).level n =
        (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (𝟙 A) f f (𝟙 B)
          (by simp)).level n := by
    subst p
    subst w
    rfl
  exact transport (plus.app X) _ _
    (laurent.map_id X) (polynomial.map_id X) _

/-- The inverse-coordinate Laurent square retains its distinct original geometric unit square. -/
def minusSquare :
    (minusSquareHomotopy (𝟙 X)).Square
      (coneSquareIdentityTrack (K (minus.app X)))
      (Homotopy.precomp (K (minus.app X))
        (laurentHomotopy X))
      ((polynomialHomotopy X).postcomp (K (minus.app X))) := by
  refine (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (minus.app X)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {A B : Scheme.{u}} (f : A ⟶ B) (p : A ⟶ A) (w : B ⟶ B)
      (hp : p = 𝟙 A) (hw : w = 𝟙 B) (h : p ≫ f = f ≫ w) :
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p f f w h).level n =
        (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (𝟙 A) f f (𝟙 B)
          (by simp)).level n := by
    subst p
    subst w
    rfl
  exact transport (minus.app X) _ _
    (laurent.map_id X) (polynomial.map_id X) _

/-- The exact chart restriction of the remaining whole comparison identity square. -/
abbrev ComparisonChartSquare
    (i : originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace) ⟶ span X) :=
  (Homotopy.precomp i (inputComparisonHomotopy (𝟙 X))).Square
    (Homotopy.precomp i (coneSquareIdentityTrack (comparison X)))
    (Homotopy.precomp i (Homotopy.precomp (comparison X) (laurentHomotopy X)))
    (Homotopy.precomp i ((spanHomotopy X).postcomp (comparison X)))

/-- The full positive chart is produced for the unchanged comparison and whole span identity. -/
def comparisonPlusChart : ComparisonChartSquare X
    (HomotopyPushout.inl (K (projection.app X))
      (K (projection.app X))) :=
  (plusSquare X).ofBoundaryLevels _ _ _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The full inverse chart is produced separately with the same unchanged Laurent identity. -/
def comparisonMinusChart : ComparisonChartSquare X
    (HomotopyPushout.inr (K (projection.app X))
      (K (projection.app X))) :=
  (minusSquare X).ofBoundaryLevels _ _ _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
