/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare
public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProductNaturality

/-! # The whole original coefficient polynomial span identity

The native geometric unit square has the polynomial and ambient coefficient identity
tracks after the actual coefficient identity transports. Descending this square gives
an identity homotopy of the unchanged reduced pushout map, with both chart tracks and
all values of the two-parameter cylinder.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:53-73`,
`BoundedFlat/CoefficientBassCoherence.lean:38-50`,
`BoundedFlat/CoefficientBassConditionalLaws.lean:98-117`,
`BoundedFlat/CoefficientPolynomialUnit.lean:28-44` and
`BoundedFlat/CoefficientPolynomialSpanUnit.lean:28-81` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R))

local notation "K(" f ")" => boundedAboveFlatPerfectPullbackPrespectrumMap f

/-- The coefficient identity is the literal identity on the original fixed fiber. -/
theorem boundedAboveFlatCoefficientGeometricIdentity (a : Under R) :
    coefficientMap P (𝟙 a) = 𝟙 (space (op P, a)) := by
  change AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op P, a)) = _
  exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)

/-- The ambient coefficient identity retains the complete original geometric unit track. -/
def boundedAboveFlatCoefficientIdentityHomotopy (a : Under R) :
    Homotopy K(coefficientMap P (𝟙 a)) (𝟙 _) :=
  (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy (space (op P, a))).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap
      (boundedAboveFlatCoefficientGeometricIdentity P a)).symm rfl

/-- The polynomial identity retains the original geometric unit and polynomial-functor identity. -/
def boundedAboveFlatCoefficientPolynomialIdentityHomotopy (a : Under R) :
    Homotopy K(coefficientMap P ((polynomialUnderFunctor R).map (𝟙 a))) (𝟙 _) :=
  (boundedAboveFlatCoefficientIdentityHomotopy P ((polynomialUnderFunctor R).obj a)).cast
    (congrArg (fun k ↦ K(coefficientMap P k)) ((polynomialUnderFunctor R).map_id a)).symm rfl

/-- The original polynomial projection square uses actual arbitrary-map pullbacks. -/
def boundedAboveFlatCoefficientPolynomialSquareHomotopy {a b : Under R} (g : a ⟶ b) :
    Homotopy (K(polynomialProjection P a) ≫
      K(coefficientMap P ((polynomialUnderFunctor R).map g)))
      (K(coefficientMap P g) ≫ K(polynomialProjection P b)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (polynomialProjection_naturality P g)

/-- The map of the actual polynomial-span pushouts uses the same polynomial square twice. -/
def boundedAboveFlatCoefficientPolynomialSpanMap {a b : Under R} (g : a ⟶ b) :
    HomotopyPushout.prespectrum K(polynomialProjection P a) K(polynomialProjection P a) ⟶
      HomotopyPushout.prespectrum K(polynomialProjection P b) K(polynomialProjection P b) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ K(coefficientMap P g)
    K(coefficientMap P ((polynomialUnderFunctor R).map g))
    K(coefficientMap P ((polynomialUnderFunctor R).map g))
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P g)
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P g)

/-- The full geometric square has exactly the two original coefficient identity tracks. -/
def boundedAboveFlatCoefficientPolynomialIdentitySquare (a : Under R) :
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (𝟙 a)).Square
      (coneSquareIdentityTrack K(polynomialProjection P a))
      (Homotopy.precomp K(polynomialProjection P a)
        (boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a))
      ((boundedAboveFlatCoefficientIdentityHomotopy P a).postcomp K(polynomialProjection P a)) := by
  have S := boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (polynomialProjection P a)
  refine S.ofBoundaryLevels _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {X Y : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ X) (w : Y ⟶ Y)
      (ep : p = 𝟙 X) (ew : w = 𝟙 Y) (h : p ≫ f = f ≫ w) :
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p f f w h).level n =
        (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
          (𝟙 X) f f (𝟙 Y) (by simp only [Category.id_comp, Category.comp_id])).level n := by
    subst p
    subst w
    rfl
  exact transport (polynomialProjection P a) _ _
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedAboveFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a)))
    (boundedAboveFlatCoefficientGeometricIdentity P a) _

/-- The actual overlap square with both moving chart tracks and the unpaused identity cylinder. -/
def boundedAboveFlatCoefficientPolynomialSpanIdentityCylinderSquare (a : Under R) :=
  HomotopyPushout.identicalLegIdentityCylinderSquare K(polynomialProjection P a)
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
    (boundedAboveFlatCoefficientIdentityHomotopy P a)
    (boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a)
    (boundedAboveFlatCoefficientPolynomialIdentitySquare P a)

/-- The whole original polynomial-span map is homotopic to the literal identity. -/
def boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy (a : Under R) :
    Homotopy (boundedAboveFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        K(polynomialProjection P a) K(polynomialProjection P a))) :=
  HomotopyPushout.identicalLegIdentityHomotopy K(polynomialProjection P a)
    (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
    (boundedAboveFlatCoefficientIdentityHomotopy P a)
    (boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a)
    (boundedAboveFlatCoefficientPolynomialIdentitySquare P a)

/-- At every level and time, the left chart is the original polynomial unit track. -/
theorem boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_inl (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, (HomotopyPushout.inl K(polynomialProjection P a) K(polynomialProjection P a)).map n x) =
    (HomotopyPushout.inl K(polynomialProjection P a) K(polynomialProjection P a)).map n
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).level n (r, x)) := rfl

/-- At every level and time, the right chart is the same original polynomial unit track. -/
theorem boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_inr (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, (HomotopyPushout.inr K(polynomialProjection P a) K(polynomialProjection P a)).map n x) =
    (HomotopyPushout.inr K(polynomialProjection P a) K(polynomialProjection P a)).map n
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).level n (r, x)) := rfl

/-- Every point of the original cylinder evaluates the square at both independent parameters. -/
theorem boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_cylinder (a : Under R)
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, HomotopyPushout.cylinder K(polynomialProjection P a) K(polynomialProjection P a) n
        (s, x)) =
      (boundedAboveFlatCoefficientPolynomialSpanIdentityCylinderSquare P a).level n (r, (s, x)) :=
  rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientPolynomialUnit.lean:28-44"
  "adaptation" "Actual polynomial coefficient unit square with both original identity tracks."]
  boundedAboveFlatCoefficientPolynomialIdentitySquare

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientPolynomialSpanUnit.lean:28-81"
  "adaptation" "Original polynomial span identity, both charts and every two-parameter value."]
  boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy
  boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_inl
  boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_inr
  boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy_cylinder

end AlgebraicGeometry.Scheme.Modules
