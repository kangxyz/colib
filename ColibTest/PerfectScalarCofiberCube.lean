/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineCubeEdges

/-! # Regression for the original scalar cube, fine edges and coherent boundary routes -/
set_option autoImplicit false
set_option warningAsError true
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open CategoryTheory.Waldhausen.Fibration SSet Topology
open scoped Simplicial Topology
universe u
namespace ColibTest.ScalarCofiberCube
local instance (X : Scheme.{u}) : HasBinaryCoproducts (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_apply (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarBasedAdditivitySquare j r q hq (t, (s, p z))) :=
  perfectOpenScalarCofiberCubeSquare_apply j r q hq n p t s z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_boundary (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z = (W).kBasepoint :=
  perfectOpenScalarCofiberCubeSquare_boundary j r q hq n p t s z hz

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_transformation_zero (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (0, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          W
          (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
            X.toRingedSpace))))) (QuotientRows.oneIdToZero W)
          (perfectOpenScalarIdentityCofibrationSequence j) (s, p z)) :=
  perfectOpenScalarCofiberCubeSquare_transformation_zero j r q hq n p s z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_transformation_one (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (1, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          W
          (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
          (perfectOpenScalarCofibrationSequence j r) (s, p z)) :=
  perfectOpenScalarCofiberCubeSquare_transformation_one j r q hq n p s z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_additivity_zero (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 0) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
          (t, realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
              (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
            (p z))) :=
  perfectOpenScalarCofiberCubeSquare_additivity_zero j r q hq n p t z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeSquare_additivity_one (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 1) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq)
          (t, p z)) :=
  perfectOpenScalarCofiberCubeSquare_additivity_one j r q hq n p t z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarCofiberCubeBoundaryHomotopy_eq :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p =
      (squareBoundaryPathHomotopy
        (perfectOpenScalarCofiberCubeSquare j r q hq n p)).symm :=
  perfectOpenScalarCofiberCubeBoundaryHomotopy_eq j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarIdentityFineCubePath_changeWeak (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarIdentityFineCubePath n p t) =
      perfectOpenScalarCofiberCubeIdentityPath j r q hq n p t :=
  perfectOpenScalarIdentityFineCubePath_changeWeak j r q hq n p t

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarSequenceFineCubePath_changeWeak (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarSequenceFineCubePath r n p t) =
      perfectOpenScalarCofiberCubeScalarPath j r q hq n p t :=
  perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq n p t

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCorner00 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 0) :=
  perfectOpenScalarFineCorner00 j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCorner01 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 1) :=
  perfectOpenScalarFineCorner01 j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCorner10 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 0) :=
  perfectOpenScalarFineCorner10 j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCorner11 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 1) :=
  perfectOpenScalarFineCorner11 j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarIdentityFineCubePath_cast :
    (perfectOpenScalarCofiberCubeIdentityPath j r q hq n p).cast
        (perfectOpenScalarFineCorner00 j r q hq n p)
        (perfectOpenScalarFineCorner01 j r q hq n p) =
      (perfectOpenScalarIdentityFineCubePath n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous :=
  perfectOpenScalarIdentityFineCubePath_cast j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarSequenceFineCubePath_cast :
    (perfectOpenScalarCofiberCubeScalarPath j r q hq n p).cast
        (perfectOpenScalarFineCorner10 j r q hq n p)
        (perfectOpenScalarFineCorner11 j r q hq n p) =
      (perfectOpenScalarSequenceFineCubePath r n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous :=
  perfectOpenScalarSequenceFineCubePath_cast j r q hq n p

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCubeBoundaryHomotopy_apply (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z =
      perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t) z :=
  perfectOpenScalarFineCubeBoundaryHomotopy_apply j r q hq n p a t z

/-- Regression for the original whole construction, with no additional hypotheses. -/
theorem original_perfectOpenScalarFineCubeBoundaryHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  perfectOpenScalarFineCubeBoundaryHomotopy_boundary j r q hq n p a t z hz

end ColibTest.ScalarCofiberCube
