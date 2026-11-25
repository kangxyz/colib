/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientPolynomialSpanUnit

/-! # The original Laurent coefficient tracks and the chart unit squares

Both actual Laurent charts retain their distinct geometric pullback squares. At the
coefficient identity, the original chosen-zero unit and the polynomial unit are their
full boundary tracks. This does not identify the chart squares with restrictions of a
whole comparison on the pushout.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:105-132`,
`BoundedFlat/CoefficientBassConeFaces.lean:31-40`, and
`BoundedFlat/CoefficientBassUnitCharts.lean:27-69` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R))

local notation "K(" f ")" => boundedAboveFlatPerfectPullbackPrespectrumMap f

/-- Contravariant coefficient pullback retains the square of the actual natural transformation. -/
theorem coefficientMap_naturality_of_natTrans {F G : Under R ⥤ Under R} (α : F ⟶ G)
    {a b : Under R} (g : a ⟶ b) :
    coefficientMap P (G.map g) ≫ coefficientMap P (α.app a) =
      coefficientMap P (α.app b) ≫ coefficientMap P (F.map g) := by
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  exact congrArg (coefficientMap P) (α.naturality g).symm

/-- The positive Laurent chart retains its actual geometric square. -/
def boundedAboveFlatCoefficientPlusSquareHomotopy {a b : Under R} (g : a ⟶ b) :
    Homotopy (K(laurentPlus P a) ≫ K(coefficientMap P ((laurentUnderFunctor R).map g)))
      (K(coefficientMap P ((polynomialUnderFunctor R).map g)) ≫ K(laurentPlus P b)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (coefficientMap_naturality_of_natTrans P (underToLaurent R) g)

/-- The inverse-coordinate Laurent chart retains its actual geometric square. -/
def boundedAboveFlatCoefficientMinusSquareHomotopy {a b : Under R} (g : a ⟶ b) :
    Homotopy (K(laurentMinus P a) ≫ K(coefficientMap P ((laurentUnderFunctor R).map g)))
      (K(coefficientMap P ((polynomialUnderFunctor R).map g)) ≫ K(laurentMinus P b)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (coefficientMap_naturality_of_natTrans P (underToLaurentInvert R) g)

/-- The original outer Laurent projection square is common to both chart diagrams. -/
def boundedAboveFlatCoefficientLaurentSquareHomotopy {a b : Under R} (g : a ⟶ b) :
    Homotopy (K(laurentProjection P a) ≫ K(coefficientMap P ((laurentUnderFunctor R).map g)))
      (K(coefficientMap P g) ≫ K(laurentProjection P b)) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy _ _ _ _
    (laurentProjection_naturality P g)

/-- The Laurent identity retains the actual geometric and normalization comparison. -/
def boundedAboveFlatCoefficientLaurentIdentityHomotopy (a : Under R) :
    Homotopy K(coefficientMap P ((laurentUnderFunctor R).map (𝟙 a))) (𝟙 _) :=
  (boundedAboveFlatCoefficientIdentityHomotopy P ((laurentUnderFunctor R).obj a)).cast
    (congrArg (fun k ↦ K(coefficientMap P k)) ((laurentUnderFunctor R).map_id a)).symm rfl

/-- Transporting both coefficient identities retains each level of the original square track. -/
theorem boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_identity_level
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : X ⟶ X) (w : Y ⟶ Y) (ep : p = 𝟙 X) (ew : w = 𝟙 Y)
    (h : p ≫ f = f ≫ w) (n : ℕ) :
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p f f w h).level n =
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
        (𝟙 X) f f (𝟙 Y) (by simp only [Category.id_comp, Category.comp_id])).level n := by
  subst p
  subst w
  rfl

/-- The positive chart's entire original unit square with both coefficient units as its sides. -/
def boundedAboveFlatCoefficientPlusIdentitySquare (a : Under R) :
    (boundedAboveFlatCoefficientPlusSquareHomotopy P (𝟙 a)).Square
      (coneSquareIdentityTrack K(laurentPlus P a))
      (Homotopy.precomp K(laurentPlus P a)
        (boundedAboveFlatCoefficientLaurentIdentityHomotopy P a))
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        K(laurentPlus P a)) := by
  refine (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (laurentPlus P a)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  exact boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_identity_level
    (laurentPlus P a) _ _
    ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
      (boundedAboveFlatCoefficientGeometricIdentity P ((laurentUnderFunctor R).obj a)))
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedAboveFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a))) _ n

/-- The inverse chart's separate original unit square with the same two coefficient units. -/
def boundedAboveFlatCoefficientMinusIdentitySquare (a : Under R) :
    (boundedAboveFlatCoefficientMinusSquareHomotopy P (𝟙 a)).Square
      (coneSquareIdentityTrack K(laurentMinus P a))
      (Homotopy.precomp K(laurentMinus P a)
        (boundedAboveFlatCoefficientLaurentIdentityHomotopy P a))
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        K(laurentMinus P a)) := by
  refine (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare (laurentMinus P a)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  exact boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_identity_level
    (laurentMinus P a) _ _
    ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
      (boundedAboveFlatCoefficientGeometricIdentity P ((laurentUnderFunctor R).obj a)))
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedAboveFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a))) _ n

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassUnitCharts.lean:27-69"
  "adaptation" "Both actual Laurent chart unit squares with full coefficient identity tracks."]
  boundedAboveFlatCoefficientPlusIdentitySquare
  boundedAboveFlatCoefficientMinusIdentitySquare

end AlgebraicGeometry.Scheme.Modules
