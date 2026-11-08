/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFiberComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberReturnOperation

/-!
# The scalar K-operation has the positive cone connecting image

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberFiberComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarOperationFiberCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "f" => changeWeakMap N
local notation "h" => changeWeakMap_basepoint N
local notation "F" => perfectOpenScalarCubeChangeWeak j n
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "df" => scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
  (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p
local notation "R" => perfectOpenScalarFineCubeReturn j r n p
local notation "lambda" => perfectOpenScalarFineCubeTerminalWord j r q hq n p
local notation "iota" => HomotopyFiber.loopInclusion f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h
local notation "hiota" => HomotopyFiber.loopInclusion_refl f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h

/-- The actual scalar operation has positive cone sign under the original connecting map. -/
theorem perfectOpenScalarKOperation_connecting_cube :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) := by
  rw [← perfectOpenScalarCubeReturn_class j r q hq n p]
  exact perfectOpenScalarNormalizedCube_connecting j r q hq n p

/-- The raw original scalar track has the same positive cone sign through its actual rebase. -/
theorem perfectOpenScalarOriginalKOperation_connecting_cube :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) := by
  rw [← perfectOpenScalarCubeReturn_originalClass j r q hq n p]
  exact perfectOpenScalarNormalizedCube_connecting j r q hq n p

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarCofiberFiberComparison.lean:1-183"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_connecting_cube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalKOperation_connecting_cube

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_connecting_cube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalKOperation_connecting_cube
