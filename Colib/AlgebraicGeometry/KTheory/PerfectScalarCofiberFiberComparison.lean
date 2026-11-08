/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumCubeNormalization
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalFiberCube
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeReturn
public import Colib.Topology.HomotopyFiber.GenLoopNormalizedReturn
public import Colib.Topology.HomotopyFiber.LES

/-! # The original scalar cube in the canonical homotopy fiber

The actual geometric normalization square, complete canonical null and original fine return
construct a homotopy from the coordinate-zero loop inclusion of the normalized scalar cube to
the original canonical fiber map on the public acyclic cone. Both inverse-prefix cancellations,
the moving source transport and every spatial boundary remain in the construction.

The original topological connecting homomorphism sends the prescribed return class on each
subdivision cube to the canonical fiber image of its actual acyclic cone, with positive sign.
No filler, null comparison, fiber equivalence or subdivision coverage is assumed. Comparison
with the prespectrum scalar operation and descent to arbitrary K-classes remain separate.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberFiberComparison.lean:35-159`
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
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarFiberCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
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
local notation "af" => scalarFineAdditivitySourceCube X
  (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "df" => scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
  (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p
local notation "R" => perfectOpenScalarFineCubeReturn j r n p
local notation "lambda" => perfectOpenScalarFineCubeTerminalWord j r q hq n p
local notation "iota" => HomotopyFiber.loopInclusion f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h
local notation "hiota" => HomotopyFiber.loopInclusion_refl f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h

/-- The original signed scalar return retains the exact mapped fine path and terminal word. -/
def perfectOpenScalarFiberReturnLoop : Path (F af) (F af) :=
  ((R).map (F).continuous).trans lambda

/-- The actual normalized cube uses coordinate zero for the original scalar track time. -/
def perfectOpenScalarFiberNormalizedCube :
    GenLoop (Fin (n + 2)) (W).Delooping (W).kBasepoint :=
  genLoopNormalizedSelfTrackCube n (F af) (perfectOpenScalarFiberReturnLoop j r q hq n p)

/-- The geometric terminal null is the same full inverse-prefix null, including its source cast. -/
theorem perfectOpenScalarNormalizedTerminalNull_prefix :
    perfectOpenScalarNormalizedTerminalNull j r q hq n p =
      HomotopyFiber.genLoopPrefixNull f (W).kBasepoint (V).kBasepoint h n lambda := rfl

/-- The old normalization and original returned loop agree through constructive associators. -/
def perfectOpenScalarNormalizedReturnHomotopy :
    (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p)).val.HomotopyRel
      (genLoopOfBasedPath
        (HomotopyFiber.genLoopReturnedLoop f (W).kBasepoint (V).kBasepoint h n
          (GenLoopPrefix.inversePrefix n af df)
          (perfectOpenScalarNormalizedTerminalNull j r q hq n p)
          (HomotopyFiber.genLoopPrefixReturn n R))).val
      (Cube.boundary (Fin (n + 1))) :=
  (genLoopOfBasedPathHomotopy
    (HomotopyFiber.genLoopNormalizedReturnHomotopy f (W).kBasepoint (V).kBasepoint h n
      R lambda)).cast
        (congrArg Subtype.val (loopCurry_genLoopNormalizedSelfTrackCube n (F af)
          (perfectOpenScalarFiberReturnLoop j r q hq n p))).symm rfl

/-- Actual geometric normalization, source sliding and unpadding reach the original cone fiber. -/
def perfectOpenScalarNormalizedFiberHomotopy :
    (GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p))).val.HomotopyRel
      (GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)).val
      (Cube.boundary (Fin (n + 1))) := by
  let H0 := (perfectOpenScalarNormalizedReturnHomotopy j r q hq n p).compContinuousMap iota
  let H1 := HomotopyFiber.genLoopReturnComparison f (W).kBasepoint (V).kBasepoint h n
    (perfectOpenScalarNormalizedFineDelta j r q hq n p)
    (perfectOpenScalarNormalizedTerminalNull j r q hq n p)
    (perfectOpenScalarCanonicalNullPath j r q hq n p)
    (HomotopyFiber.genLoopPrefixReturn n R)
    (perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p)
  exact (H0.trans H1).cast rfl
    (congrArg Subtype.val (perfectOpenScalarCanonicalFiberCube_eq j r q hq n p))

/-- The complete normalized scalar cube is retained on the initial fiber face. -/
theorem perfectOpenScalarNormalizedFiberHomotopy_zero (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z) =
      iota (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p) z) :=
  (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p).apply_zero z

/-- The final face is the original canonical fiber map on the public acyclic cone. -/
theorem perfectOpenScalarNormalizedFiberHomotopy_one (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z) =
      canonicalFiberMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p).apply_one z

/-- Every homotopy time fixes the entire original spatial boundary, also when n is zero. -/
theorem perfectOpenScalarNormalizedFiberHomotopy_boundary (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (s, z) =
      HomotopyFiber.basepoint f (W).kBasepoint (V).kBasepoint h :=
  ((perfectOpenScalarNormalizedFiberHomotopy j r q hq n p).eq_fst s hz).trans
    ((GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p))).property z hz)

/-- At the initial face, coordinate zero is exactly the original normalized path time. -/
theorem perfectOpenScalarNormalizedFiberHomotopy_zero_path
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z)).val.2 t =
      genLoopNormalizedSelfTrackPath n (F af)
        (perfectOpenScalarFiberReturnLoop j r q hq n p) t z := by
  rw [perfectOpenScalarNormalizedFiberHomotopy_zero]
  rfl

/-- The final stored path retains every original canonical null time. -/
theorem perfectOpenScalarNormalizedFiberHomotopy_one_path
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z)).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) := by
  rw [perfectOpenScalarNormalizedFiberHomotopy_one]
  rfl

/-- The original coordinate-zero connecting map sends the normalized scalar cube to its cone. -/
theorem perfectOpenScalarNormalizedCube_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (genLoopSelfTrackClass n (F af) (perfectOpenScalarFiberReturnLoop j r q hq n p)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) := by
  rw [← genLoopNormalizedSelfTrackCube_class, KMap_eq_piMap]
  change (⟦GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p))⟧ :
      HomotopyGroup.Pi (n + 1) (HomotopyFiber f (W).kBasepoint)
        (HomotopyFiber.basepoint f (W).kBasepoint (V).kBasepoint h)) =
    ⟦GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
      (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)⟧
  exact Quotient.sound ⟨perfectOpenScalarNormalizedFiberHomotopy j r q hq n p⟩


end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0320",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberFiberComparison.lean:35-159"
    "adaptation"
    "Whole prescribed scalar return comparison with the canonical fiber and connecting map"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFiberReturnLoop
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFiberNormalizedCube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedTerminalNull_prefix
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedReturnHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy_boundary
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy_zero_path
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedFiberHomotopy_one_path
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedCube_connecting
