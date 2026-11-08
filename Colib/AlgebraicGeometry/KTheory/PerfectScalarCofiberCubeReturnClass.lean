/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeReturn
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackTimeOperations

/-! # The prescribed scalar return class and its inverse composition

The actual signed return is compared with the inverse of the full inclusion/projection loop.
Its homotopy and both times are already constructed from the original scalar square. This is
an equality in the actual coarse K-group, including n = 0. It does not yet identify that class
with a prespectrum scalar operation or descend the subdivision input to arbitrary K-classes.

Implementation provenance: the composition loop and first two steps of the return-class proof
in `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is a stated intermediate comparison,
not the original theorem identifying the class with the prespectrum scalar operation.
-/
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
local instance scalarReturnClassCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
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

local notation "b" => perfectOpenScalarCubeChangeWeak j n af

/-- The whole original inclusion followed by the mapped same-rebase fine projection. -/
def perfectOpenScalarCubeCompositionPath : Path b b :=
  (perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
    ((perfectOpenScalarFineProjectionCubePath j r n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous)

/-- The prescribed signed return has the inverse class of the actual whole composition loop. -/
theorem perfectOpenScalarCubeReturn_inverseCompositionClass :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      (genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ := by
  calc
    _ = genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p).symm :=
      (genLoopSelfTrackClass_eq_iff n b _ _).mpr
        ⟨perfectOpenScalarCubeReturnHomotopy j r q hq n p⟩
    _ = _ := genLoopSelfTrackClass_symm n b _

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0320", colib_ref "quillen"
  "Spectrum/ScalarCofiberCubeReturnClass.lean:99-103, 210-224"
  "adaptation" "The actual composition loop and inverse-class part of the prescribed return proof"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeCompositionPath
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_inverseCompositionClass
