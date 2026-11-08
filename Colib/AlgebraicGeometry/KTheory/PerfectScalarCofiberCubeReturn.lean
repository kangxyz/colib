/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineProjectionCubePath
public import Colib.Topology.Path.Homotopy.SquareProjectionReturn

/-! # The literal signed scalar cube return word

The original fine return and the two reversed boundary edges give an actual homotopy to the
inverse inclusion/projection composition. The terminal endpoint remains the moving original
cube. The identity additivity track and quotient-first sum edge remain whole paths.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeReturn.lean:27-86`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
endpoint casts, cancellations and path orientations are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarReturnCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
  (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "af" => scalarFineAdditivitySourceCube X
  (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "df" => scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
  (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p

/-- The exact fine return is the reversed original projection followed by the scalar edge. -/
def perfectOpenScalarFineCubeReturn : Path af df :=
  (perfectOpenScalarFineProjectionCubePath j r n p).symm.trans
    (perfectOpenScalarSequenceFineCubePath r n p)

/-- The two reversed original edges end at the moving change-weak image of the initial cube. -/
def perfectOpenScalarFineCubeTerminalWord :
    Path (perfectOpenScalarCubeChangeWeak j n df) (perfectOpenScalarCubeChangeWeak j n af) :=
  (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.trans
    ((perfectOpenScalarIdentityFineCubePath n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous).symm

/-- No reassociation or altered parameterization is hidden in the fine return word. -/
theorem perfectOpenScalarFineCubeReturn_eq :
    perfectOpenScalarFineCubeReturn j r n p =
      (perfectOpenScalarFineProjectionCubePath j r n p).symm.trans
        (perfectOpenScalarSequenceFineCubePath r n p) := rfl

/-- The original quotient-first edge and complete identity track retain their exact parentheses. -/
theorem perfectOpenScalarFineCubeTerminalWord_eq :
    perfectOpenScalarFineCubeTerminalWord j r q hq n p =
      (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.trans
        ((perfectOpenScalarIdentityFineCubePath n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).symm := rfl

/-- The whole mapped fine return word is homotopic to the inverse original composition. -/
def perfectOpenScalarCubeReturnHomotopy :
    (((perfectOpenScalarFineCubeReturn j r n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarFineCubeTerminalWord j r q hq n p)).Homotopy
      ((perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
        ((perfectOpenScalarFineProjectionCubePath j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous)).symm :=
  Path.Homotopy.squareProjectionReturnMap (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarSequenceFineCubePath r n p)
    (perfectOpenScalarFineProjectionCubePath j r n p)
    (perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p)

/-- Both independent homotopy/path times retain the entire original spatial boundary. -/
theorem perfectOpenScalarCubeReturnHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCubeReturnHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  (perfectOpenScalarCubeReturnHomotopy j r q hq n p (a, t)).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0320",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeReturn.lean:27-86"
    "adaptation"
    "Actual prescribed scalar return and reversed original composition on each subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeReturn
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeTerminalWord
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeReturn_eq
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeTerminalWord_eq
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturnHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturnHomotopy_boundary
