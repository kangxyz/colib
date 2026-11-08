/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumCubeNormalization
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalFiberCube

/-! # Full-signature checks of actual scalar normalization and canonical fiber evaluation -/
set_option autoImplicit false
set_option warningAsError true
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.Product SSet Topology
open scoped Simplicial Topology
universe u v
namespace ColibTest.ScalarFiberNormalization

section General
variable {C : Type u} [Category.{v} C] (V : Structure C)
/-- Check the entire original signature and displayed construction. -/
theorem original_separatedPairDeloopingMap_projection
    (x : |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V x) =
      (separatedFirstDeloopingMap V x, separatedRightDeloopingMap V x) :=
  separatedPairDeloopingMap_projection V x

/-- Check the entire original signature and displayed construction. -/
theorem original_separatedPairMap_fst :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (fst_exact V V) =
      OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V) :=
  separatedPairMap_fst V

/-- Check the entire original signature and displayed construction. -/
theorem original_separatedPairMap_snd :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (snd_exact V V) = rightRestrictionMap V :=
  separatedPairMap_snd V

end General

section Fiber
variable {Y : Type v} {Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(Z, Y)) (y : Y) (x : Z) (h : f x = y) (n : ℕ)
local notation "E" => GenLoop (Fin (n + 1)) Z x
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)
open Topology.HomotopyFiber
/-- Check the entire original signature and displayed construction. -/
theorem original_genLoopNullLift_path (p : E) (P : Path (F p) B)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (genLoopNullLift f y x h n p P z).val.2 t = P t z :=
  genLoopNullLift_path f y x h n p P z t

/-- Check the entire original signature and displayed construction. -/
theorem original_genLoopEvaluation_boundary (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopEvaluation f y x h n w z = basepoint f y x h :=
  genLoopEvaluation_boundary f y x h n w z hz

end Fiber

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
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarFineProjectionCubePath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineProjectionCubePath j r n p t z =
      perfectOpenScalarProjectionFineRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarFineProjectionCubePath_apply j r n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarFineProjectionCubePath_changeWeak (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarFineProjectionCubePath j r n p t) z =
      perfectOpenScalarProjectionRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarFineProjectionCubePath_changeWeak j r n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarFineProjectionCubePath_boundary (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineProjectionCubePath j r n p t z = (V).kBasepoint :=
  perfectOpenScalarFineProjectionCubePath_boundary j r n p t z hz

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_apply (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p z))) :=
  perfectOpenScalarSumNormalizationCubeSquare_apply j r q hq n p t s z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_boundary (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s) z = (W).kBasepoint :=
  perfectOpenScalarSumNormalizationCubeSquare_boundary j r q hq n p t s z hz

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_vertical_zero (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, s) z =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p s z :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_zero j r q hq n p s z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_vertical_one (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (s, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_one j r q hq n p s z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 0) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
          (t, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero j r q hq n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarSumNormalizationCubeSquare_horizontal_one (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 1) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
          hq) (t, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_horizontal_one j r q hq n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarZeroPairTargetCube_compact :
    perfectOpenScalarZeroPairTargetCube j n p =
      coproductCube V n GenLoop.const (perfectOpenScalarCanonicalRightCube j n p) :=
  perfectOpenScalarZeroPairTargetCube_compact j n p

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarConePairTargetCube_compact :
    perfectOpenScalarConePairTargetCube j r q hq n p =
      coproductCube V n (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalRightCube j n p) :=
  perfectOpenScalarConePairTargetCube_compact j r q hq n p

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalNullPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalNullPath j r q hq n p t z =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalNullPath_apply j r q hq n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p z)) =
      coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
        (Path.refl (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarCanonicalRightCube j n p))) t z :=
  perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact j r q hq n p t z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalSumDiagonalRealization_reversed_boundary
    (t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p z)) = (W).kBasepoint :=
  perfectOpenScalarCanonicalSumDiagonalRealization_reversed_boundary j r q hq n p t z hz

/-- Check the entire original signature and displayed construction. -/
def original_perfectOpenScalarNormalizedEndpointHomotopy :
    (perfectOpenScalarNormalizedTerminalNull j r q hq n p).Homotopy
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
          (perfectOpenScalarCanonicalNullPath j r q hq n p)) :=
  perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarNormalizedEndpointHomotopy_zero (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (0, t) =
      perfectOpenScalarNormalizedTerminalNull j r q hq n p t :=
  perfectOpenScalarNormalizedEndpointHomotopy_zero j r q hq n p t

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarNormalizedEndpointHomotopy_one (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (1, t) =
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
          (perfectOpenScalarCanonicalNullPath j r q hq n p)) t :=
  perfectOpenScalarNormalizedEndpointHomotopy_one j r q hq n p t

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarNormalizedEndpointHomotopy_boundary (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (s, t) z = (W).kBasepoint :=
  perfectOpenScalarNormalizedEndpointHomotopy_boundary j r q hq n p s t z hz

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalFiberCube_source (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.1 =
      acyclicInclusionMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalFiberCube_source j r q hq n p z

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalFiberCube_path (z : Fin (n + 1) → unitInterval)
    (t : unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalFiberCube_path j r q hq n p z t

/-- Check the entire original signature and displayed construction. -/
theorem original_perfectOpenScalarCanonicalFiberCube_eq :
    perfectOpenScalarCanonicalFiberCube j r q hq n p =
      GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p) :=
  perfectOpenScalarCanonicalFiberCube_eq j r q hq n p

end ColibTest.ScalarFiberNormalization
