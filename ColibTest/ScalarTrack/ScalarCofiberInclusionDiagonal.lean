/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberInclusionDiagonal


/-! The entire original inclusion cylinder, its ordinary realization, and subdivision input. -/
public section
open Topology SSet
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry MonoidalCategory Topology AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.Additivity Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace ColibTest.ScalarTrack.ScalarCofiberInclusionDiagonal
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The entire original simplicial cylinder, with the actual endpoint normalizations. -/
theorem original_whole_cylinder :
    (normalizedMiddleTransformationHomotopy V W
      (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))))) (perfectScalarInclusionNat X r)
      (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
      (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
      (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq)).h ≫
        (bisimplicialDiagonalIso W).hom =
      (bisimplicialDiagonalIso V).hom ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W (hF).rebase (hM).rebase
          (normalizedWeakTransformation hF hM (perfectScalarInclusionNat X r))
          (normalizedWeakTransformation_weak hF hM (perfectScalarInclusionNat X r)
            (perfectScalarInclusionNat_openWeak j r q hq)) :=
  perfectOpenScalarInclusionDiagonalCylinder j r q hq

/-- Every ordinary input and the full inclusion time survive the actual diagonal maps. -/
theorem original_ordinary_cylinder
    (t : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (normalizedMiddleTransformationHomotopy V W
            (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))))) (perfectScalarInclusionNat X r)
            (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
            (perfectOpenScalarIdentityCofibrationSequence j)
            (perfectOpenScalarCofibrationSequence j r)
            (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq))
          (t, x)) =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, SSet.toTop.map (bisimplicialDiagonalIso V).hom x) :=
  perfectOpenScalarInclusionDiagonalRealization j r q hq t x

/-- The actual subdivided diagonal inclusion face retains its complete ordinary cylinder. -/
theorem original_diagonal_subdivided (t : unitInterval)
    (x : |SSet.diagonalSSet
      (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))|) :
    SSet.toTop.map (bisimplicialDiagonalIso (perfectOpenNested j).coarse).hom
        (realizationSimplicialHomotopy
          (normalizedMiddleTransformationHomotopy (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (perfectOpenNested j).coarse
            (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))))) (perfectScalarInclusionNat X r)
            (QuotientRows.oneIdToZero (perfectOpenNested j).coarse)
            (perfectScalarConeProjectionNat X r)
            (perfectOpenScalarIdentityCofibrationSequence j)
            (perfectOpenScalarCofibrationSequence j r)
            (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq))
          (t, realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) x)) =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)).hom
          (realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) x)) :=
  perfectOpenScalarInclusionDiagonalRealization j r q hq t _

end ColibTest.ScalarTrack.ScalarCofiberInclusionDiagonal
