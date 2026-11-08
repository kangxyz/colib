/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberReturnOperation
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrackOperation

/-!
# The prescribed return restricts to the actual flat-unit operation

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean`
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
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u v
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarReturnRestrictionCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
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
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "b" => perfectOpenScalarCubeChangeWeak j n af
local notation "pSmall" => GenLoop.postcomp
  (ContinuousMap.HomotopyEquiv.toFun (Homeomorph.toHomotopyEquiv
    (Structure.asSmallDeloopingHomeomorph (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))))
  (Structure.asSmallDeloopingHomeomorph_basepoint (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))
  (perfectScalarProjectionInputCube n p)

/-- Restriction gives the actual flat-unit operation through its proved whole track comparison. -/
theorem perfectOpenScalarCubeReturn_class_restrict :
    KMap (perfectOpenRestrict_isExact j) (n + 1)
        (genLoopSelfTrackClass n b
          (((perfectOpenScalarFineCubeReturn j r n p).map
            (perfectOpenScalarCubeChangeWeak j n).continuous).trans
              (perfectOpenScalarFineCubeTerminalWord j r q hq n p))) =
      originalKSelfTrackOperation V (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectFlatUnitHomotopy j q) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  rw [perfectOpenScalarCubeReturn_class]
  exact congrArg (fun f => f (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n))
    (perfectOpenScalarKOperation_restrict j r q hq n)

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean:1-257"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_class_restrict

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_class_restrict
