/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalSumCube
public import Colib.Topology.HomotopyFiber.GenLoopPathTransport

/-! # The actual scalar cone cube in the original homotopy fiber

The evaluated lift uses the public acyclic cone, its original fine inclusion and the entire
canonical null path with its explicit source cast. Its two coordinates agree with the old
canonical acyclic-to-fiber map at every spatial point and every stored path time. Extensionality
then identifies the whole based cube, including one-coordinate inputs. No fiber equivalence or
connecting-map formula is asserted here.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCanonicalFiberCube.lean:34-76`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N

/-- Evaluate the original cone cube together with its complete source-cast canonical null. -/
def perfectOpenScalarCanonicalFiberCube :
    GenLoop (Fin (n + 1)) (HomotopyFiber (changeWeakMap N) (W).kBasepoint)
      (HomotopyFiber.basepoint (changeWeakMap N) (W).kBasepoint (V).kBasepoint
        (changeWeakMap_basepoint N)) :=
  HomotopyFiber.genLoopNullLift (changeWeakMap N) (W).kBasepoint (V).kBasepoint
    (changeWeakMap_basepoint N) n
    (perfectOpenScalarCanonicalConeCube j r q hq n p)
    (perfectOpenScalarCanonicalNullPath j r q hq n p)

/-- The first coordinate is exactly the old fine inclusion of the actual acyclic cone. -/
theorem perfectOpenScalarCanonicalFiberCube_source (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.1 =
      acyclicInclusionMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) := rfl

/-- Every stored null time is the original reversed zero-to-inclusion cylinder. -/
theorem perfectOpenScalarCanonicalFiberCube_path (z : Fin (n + 1) → unitInterval)
    (t : unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) := by
  change perfectOpenScalarCanonicalNullPath j r q hq n p t z = _
  exact perfectOpenScalarCanonicalNullPath_apply j r q hq n p t z

/-- The full based cube is the original canonical fiber map on the public acyclic cone cube. -/
theorem perfectOpenScalarCanonicalFiberCube_eq :
    perfectOpenScalarCanonicalFiberCube j r q hq n p =
      GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p) := by
  apply GenLoop.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.1 =
      acyclicInclusionMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z)
    exact perfectOpenScalarCanonicalFiberCube_source j r q hq n p z
  · apply ContinuousMap.ext
    intro t
    change (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z)
    exact perfectOpenScalarCanonicalFiberCube_path j r q hq n p z t

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCanonicalFiberCube.lean:34-76"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalFiberCube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalFiberCube_source
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalFiberCube_path
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalFiberCube_eq
