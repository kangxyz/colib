/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumNormalizationSquare
public import Colib.Topology.Homotopy.SquareBoundaryPaths
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalSumCube
public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductNormalizedEndpoint
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-! # Original scalar normalization square on unchanged subdivision cubes

The two square times and every spatial coordinate remain the actual normalization square.
The boundary interpolation keeps the old sum path, both Theta paths and the canonical product
cylinder. Actual product projections and the complete reversed canonical cylinder provide both
compact targets and the canonical null. The resulting whole normalized endpoint uses only the
original open immersion, scalar/unit data and subdivision cube, retaining both inverse-prefix
cancellations.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumCubeNormalization.lean:34-609`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
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

local instance scalarSumCubeCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
  (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- The entire actual square evaluated on the unchanged original subdivision cube. -/
def perfectOpenScalarSumNormalizationCubeSquare :
    C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) (W).Delooping (W).kBasepoint) where
  toFun ts := ⟨⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
    (perfectOpenScalarSumNormalizationRealizationSquare j r q hq
      (ts.1, (ts.2, p z))), by fun_prop⟩, by
      intro z hz
      change SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq
          (ts.1, (ts.2, p z))) = (W).kBasepoint
      exact (congrArg (fun x ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (ts.1, (ts.2, x))))
        (p.property z hz)).trans
          ((congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y)
            (perfectOpenScalarSumNormalizationRealizationSquare_fixed_zero
              j r q hq ts.1 ts.2)).trans
              (diagonalRealization_basepoint W))⟩
  continuous_toFun := by
    have hc : Continuous (fun ts : unitInterval × unitInterval ↦
        (⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
          (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (ts.1, (ts.2, p z))),
          by fun_prop⟩ : C((Fin (n + 1) → unitInterval), (W).Delooping))) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × unitInterval) ×
          (Fin (n + 1) → unitInterval) ↦
        SSet.toTop.map (bisimplicialDiagonalIso W).hom
          (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (z.1.1, (z.1.2, p z.2))))
      fun_prop
    exact hc.subtype_mk _

/-- Normalization time, sum time and every original cube coordinate remain unchanged. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_apply (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p z))) := rfl

/-- The entire spatial boundary is fixed at independently varying square times. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_boundary (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s) z = (W).kBasepoint :=
  (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s)).property z hz

/-- At normalization time zero the full original quotient-first sum path remains. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_vertical_zero (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, s) z =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p s z := by
  rw [perfectOpenScalarSumNormalizationCubeSquare_apply,
    perfectOpenScalarSumNormalizationRealizationSquare_vertical_zero,
    perfectOpenScalarCofiberCubeSumPath_apply,
    perfectOpenScalarCofiberCubeSquare_additivity_one]

/-- At normalization time one the full canonical product cylinder remains. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_vertical_one (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (s, p z)) := by
  rw [perfectOpenScalarSumNormalizationCubeSquare_apply,
    perfectOpenScalarSumNormalizationRealizationSquare_vertical_one]

/-- The whole initial Theta face retains the original zero normalization cylinder. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 0) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
          (t, p z)) := by
  rw [perfectOpenScalarSumNormalizationCubeSquare_apply,
    perfectOpenScalarSumNormalizationRealizationSquare_horizontal_zero]

/-- The whole terminal Theta face retains the original cone normalization cylinder. -/
theorem perfectOpenScalarSumNormalizationCubeSquare_horizontal_one (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 1) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
          hq) (t, p z)) := by
  rw [perfectOpenScalarSumNormalizationCubeSquare_apply,
    perfectOpenScalarSumNormalizationRealizationSquare_horizontal_one]

/-- The entire old sum edge with its exact displayed square endpoints. -/
def perfectOpenScalarSumNormalizationOriginalPath :
    Path (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 0))
      (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 1)) :=
  ((Path.refl (0 : unitInterval)).prod Path.id).map
    (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p).continuous

/-- The original sum coordinate has not been reparametrized. -/
theorem perfectOpenScalarSumNormalizationOriginalPath_apply (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationOriginalPath j r q hq n p s z =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p s z :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_zero j r q hq n p s z

/-- The canonical sum edge retains its own whole original parameter. -/
def perfectOpenScalarSumNormalizationCanonicalPath :
    Path (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 0))
      (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 1)) :=
  ((Path.refl (1 : unitInterval)).prod Path.id).map
    (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p).continuous

/-- Every canonical path slice is the actual original diagonal cylinder. -/
theorem perfectOpenScalarSumNormalizationCanonicalPath_apply (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCanonicalPath j r q hq n p s z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (s, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_one j r q hq n p s z

/-- The first original Theta path retains the entire zero normalization. -/
def perfectOpenScalarSumNormalizationZeroThetaPath :
    Path (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 0))
      (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 0)) :=
  (Path.id.prod (Path.refl (0 : unitInterval))).map
    (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p).continuous

/-- The second original Theta path retains the entire cone normalization. -/
def perfectOpenScalarSumNormalizationConeThetaPath :
    Path (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 1))
      (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 1)) :=
  (Path.id.prod (Path.refl (1 : unitInterval))).map
    (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p).continuous

/-- The actual boundary interpolation has Z then Theta1 on its first route, with no reversal. -/
def perfectOpenScalarSumNormalizationCubeBoundaryHomotopy :
    ((perfectOpenScalarSumNormalizationOriginalPath j r q hq n p).trans
      (perfectOpenScalarSumNormalizationConeThetaPath j r q hq n p)).Homotopy
      ((perfectOpenScalarSumNormalizationZeroThetaPath j r q hq n p).trans
        (perfectOpenScalarSumNormalizationCanonicalPath j r q hq n p)) :=
  squareBoundaryPathHomotopy (perfectOpenScalarSumNormalizationCubeSquare j r q hq n p)

/-- Every intermediate comparison fixes the entire spatial boundary at both independent times. -/
theorem perfectOpenScalarSumNormalizationCubeBoundaryHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationCubeBoundaryHomotopy j r q hq n p (a, t) z =
      (W).kBasepoint :=
  (perfectOpenScalarSumNormalizationCubeBoundaryHomotopy j r q hq n p (a, t)).property z hz

/-- The whole fine zero normalization cylinder on the unchanged original cube. -/
def perfectOpenScalarZeroThetaFineCubeFamily :
    C(unitInterval, GenLoop (Fin (n + 1)) (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).Delooping
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint) where
  toFun t := ⟨⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom
    (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
      (t, p z)), by fun_prop⟩, by
      intro z hz
      change SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
          (t, p z)) = (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
      exact (congrArg (fun x ↦ SSet.toTop.map
        (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom
          (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
            (t, x))) (p.property z hz)).trans
              ((congrArg (fun y ↦ SSet.toTop.map
                (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
                  X.toRingedSpace)).hom y)
                  (perfectOpenScalarZeroThetaDiagonalHomotopy_fixed_zero j t)).trans
                    (diagonalRealization_basepoint (RingedSpace.perfectComplexesWaldhausen
                      X.toRingedSpace)))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (Fin (n + 1) → unitInterval) ↦
      SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
          (z.1, p z.2)))
    fun_prop

/-- Time zero is exactly the original fine separated endpoint, before compact target transport. -/
theorem perfectOpenScalarZeroThetaFineCubeFamily_source :
    perfectOpenScalarZeroThetaFineCubeFamily j n p 0 =
      scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
        (QuotientRows.oneIdToZero (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))
          (perfectScalarIdentityFineCofibrationSequence (X := X)) n p := by
  apply GenLoop.ext
  intro z
  exact congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom y)
    ((realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)).apply_zero
      (p z))

/-- The fine zero path keeps its actual original source and full normalization time. -/
def perfectOpenScalarZeroThetaFineCubePath :
    Path (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
        (QuotientRows.oneIdToZero (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))
          (perfectScalarIdentityFineCofibrationSequence (X := X)) n p)
      (perfectOpenScalarZeroThetaFineCubeFamily j n p 1) :=
  (Path.id.map (perfectOpenScalarZeroThetaFineCubeFamily j n p).continuous).cast
    (perfectOpenScalarZeroThetaFineCubeFamily_source j n p).symm rfl

/-- Every fine path time is mapped through the original change-weak cylinder identity. -/
theorem perfectOpenScalarZeroThetaFineCubePath_changeWeak (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarZeroThetaFineCubePath j n p t) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
          (t, p z)) :=
  perfectOpenScalarZeroThetaRealization_changeWeak j t (p z)

/-- The whole fine cone normalization cylinder on the unchanged original cube. -/
def perfectOpenScalarConeThetaFineCubeFamily :
    C(unitInterval, GenLoop (Fin (n + 1)) (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).Delooping
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint) where
  toFun t := ⟨⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom
    (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
      (t, p z)), by fun_prop⟩, by
      intro z hz
      change SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
          (t, p z)) = (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
      exact (congrArg (fun x ↦ SSet.toTop.map
        (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom
          (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
            (t, x))) (p.property z hz)).trans
              ((congrArg (fun y ↦ SSet.toTop.map
                (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
                  X.toRingedSpace)).hom y)
                  (perfectOpenScalarConeThetaDiagonalHomotopy_fixed_zero j r q hq t)).trans
                    (diagonalRealization_basepoint (RingedSpace.perfectComplexesWaldhausen
                      X.toRingedSpace)))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (Fin (n + 1) → unitInterval) ↦
      SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
          (z.1, p z.2)))
    fun_prop

/-- Time zero is exactly the original fine separated endpoint, before compact target transport. -/
theorem perfectOpenScalarConeThetaFineCubeFamily_source :
    perfectOpenScalarConeThetaFineCubeFamily j r q hq n p 0 =
      scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
        (perfectScalarConeProjectionNat X r)
          (perfectScalarCofibrationSequence X r) n p := by
  apply GenLoop.ext
  intro z
  exact congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom y)
    ((realizationSimplicialHomotopy
      (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)).apply_zero (p z))

/-- The fine cone path keeps its actual original source and full normalization time. -/
def perfectOpenScalarConeThetaFineCubePath :
    Path (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
        (perfectScalarConeProjectionNat X r)
          (perfectScalarCofibrationSequence X r) n p)
      (perfectOpenScalarConeThetaFineCubeFamily j r q hq n p 1) :=
  (Path.id.map (perfectOpenScalarConeThetaFineCubeFamily j r q hq n p).continuous).cast
    (perfectOpenScalarConeThetaFineCubeFamily_source j r q hq n p).symm rfl

/-- Every fine path time is mapped through the original change-weak cylinder identity. -/
theorem perfectOpenScalarConeThetaFineCubePath_changeWeak (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarConeThetaFineCubePath j r q hq n p t) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq)
          (t, p z)) :=
  perfectOpenScalarConeThetaRealization_changeWeak j r q hq t (p z)

/-- The first square corner is the original mapped fine identity-sequence target. -/
theorem perfectOpenScalarSumNormalizationCorner00 :
    perfectOpenScalarCubeChangeWeak j n
        (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
          (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
          (QuotientRows.oneIdToZero (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))
          (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 0) := by
  have h : perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 0) =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p 0 := by
    ext z
    exact perfectOpenScalarSumNormalizationCubeSquare_vertical_zero j r q hq n p 0 z
  exact (perfectOpenScalarFineCorner01 j r q hq n p).trans
    (h.trans (perfectOpenScalarCofiberCubeSumPath j r q hq n p).source).symm

/-- The second square corner is the original mapped fine scalar-sequence target. -/
theorem perfectOpenScalarSumNormalizationCorner01 :
    perfectOpenScalarCubeChangeWeak j n
        (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
          (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 1) := by
  have h : perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, 1) =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p 1 := by
    ext z
    exact perfectOpenScalarSumNormalizationCubeSquare_vertical_zero j r q hq n p 1 z
  exact (perfectOpenScalarFineCorner11 j r q hq n p).trans
    (h.trans (perfectOpenScalarCofiberCubeSumPath j r q hq n p).target).symm

/-- The zero Theta target is obtained from the complete original change-weak cylinder. -/
theorem perfectOpenScalarSumNormalizationCorner10 :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarZeroThetaFineCubeFamily j n p 1) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 0) := by
  have h : perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarZeroThetaFineCubePath j n p 1) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 0) := by
    ext z
    exact (perfectOpenScalarZeroThetaFineCubePath_changeWeak j n p 1 z).trans
      (perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero j r q hq n p 1 z).symm
  exact (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarZeroThetaFineCubePath j n p).target).symm.trans h

/-- The cone Theta target is obtained from the complete original change-weak cylinder. -/
theorem perfectOpenScalarSumNormalizationCorner11 :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarConeThetaFineCubeFamily j r q hq n p 1) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 1) := by
  have h : perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarConeThetaFineCubePath j r q hq n p 1) =
      perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, 1) := by
    ext z
    exact (perfectOpenScalarConeThetaFineCubePath_changeWeak j r q hq n p 1 z).trans
      (perfectOpenScalarSumNormalizationCubeSquare_horizontal_one j r q hq n p 1 z).symm
  exact (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarConeThetaFineCubePath j r q hq n p).target).symm.trans h

/-- Casting the original sum edge retains the already constructed fine-endpoint sum path. -/
theorem perfectOpenScalarSumNormalizationOriginalPath_cast :
    (perfectOpenScalarSumNormalizationOriginalPath j r q hq n p).cast
        (perfectOpenScalarSumNormalizationCorner00 j r q hq n p)
        (perfectOpenScalarSumNormalizationCorner01 j r q hq n p) =
      perfectOpenScalarFineCubeSumPath j r q hq n p := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  exact perfectOpenScalarSumNormalizationOriginalPath_apply j r q hq n p t z

/-- Casting the entire zero Theta edge gives the unchanged mapped fine path. -/
theorem perfectOpenScalarSumNormalizationZeroThetaPath_cast :
    (perfectOpenScalarSumNormalizationZeroThetaPath j r q hq n p).cast
        (perfectOpenScalarSumNormalizationCorner00 j r q hq n p)
        (perfectOpenScalarSumNormalizationCorner10 j r q hq n p) =
      (perfectOpenScalarZeroThetaFineCubePath j n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  exact (perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero j r q hq n p t z).trans
    (perfectOpenScalarZeroThetaFineCubePath_changeWeak j n p t z).symm

/-- Casting the entire cone Theta edge gives the unchanged mapped fine path. -/
theorem perfectOpenScalarSumNormalizationConeThetaPath_cast :
    (perfectOpenScalarSumNormalizationConeThetaPath j r q hq n p).cast
        (perfectOpenScalarSumNormalizationCorner01 j r q hq n p)
        (perfectOpenScalarSumNormalizationCorner11 j r q hq n p) =
      (perfectOpenScalarConeThetaFineCubePath j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  exact (perfectOpenScalarSumNormalizationCubeSquare_horizontal_one j r q hq n p t z).trans
    (perfectOpenScalarConeThetaFineCubePath_changeWeak j r q hq n p t z).symm

/-- The entire canonical path retains the same mapped fine normalization endpoints. -/
def perfectOpenScalarSumNormalizationCanonicalFinePath :=
  (perfectOpenScalarSumNormalizationCanonicalPath j r q hq n p).cast
    (perfectOpenScalarSumNormalizationCorner10 j r q hq n p)
    (perfectOpenScalarSumNormalizationCorner11 j r q hq n p)

/-- The actual square now has the original fine target types on all four corners. -/
def perfectOpenScalarSumNormalizationFineBoundaryHomotopy :
    ((perfectOpenScalarFineCubeSumPath j r q hq n p).trans
      ((perfectOpenScalarConeThetaFineCubePath j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous)).Homotopy
      (((perfectOpenScalarZeroThetaFineCubePath j n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarSumNormalizationCanonicalFinePath j r q hq n p)) := by
  let J := (perfectOpenScalarSumNormalizationCubeBoundaryHomotopy j r q hq n p).pathCast
    (perfectOpenScalarSumNormalizationCorner00 j r q hq n p)
    (perfectOpenScalarSumNormalizationCorner11 j r q hq n p)
  refine J.cast ?_ ?_
  · rw [Path.cast_trans _ _ _ (perfectOpenScalarSumNormalizationCorner01 j r q hq n p) _,
      perfectOpenScalarSumNormalizationOriginalPath_cast,
      perfectOpenScalarSumNormalizationConeThetaPath_cast]
  · rw [Path.cast_trans _ _ _ (perfectOpenScalarSumNormalizationCorner10 j r q hq n p) _,
      perfectOpenScalarSumNormalizationZeroThetaPath_cast]
    rfl

/-- Rotation reverses only the canonical edge and removes the actual final zero Theta path. -/
def perfectOpenScalarSumNormalizationReversedHomotopy :
    (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.Homotopy
      (((perfectOpenScalarConeThetaFineCubePath j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        ((perfectOpenScalarSumNormalizationCanonicalFinePath j r q hq n p).symm.trans
          ((perfectOpenScalarZeroThetaFineCubePath j n p).map
            (perfectOpenScalarCubeChangeWeak j n).continuous).symm)) := by
  let T0 := (perfectOpenScalarZeroThetaFineCubePath j n p).map
    (perfectOpenScalarCubeChangeWeak j n).continuous
  let T1 := (perfectOpenScalarConeThetaFineCubePath j r q hq n p).map
    (perfectOpenScalarCubeChangeWeak j n).continuous
  let K := perfectOpenScalarSumNormalizationCanonicalFinePath j r q hq n p
  exact (Path.Homotopy.removeSuffix _ T0 (T1.trans K.symm)
    (perfectOpenScalarSumNormalizationFineBoundaryHomotopy j r q hq n p).rotate).trans
      (Path.Homotopy.transAssoc T1 K.symm T0.symm)

/-- The fine zero Theta target is the actual original pair-target cube at every input. -/
theorem perfectOpenScalarZeroThetaFineCubeFamily_target :
    perfectOpenScalarZeroThetaFineCubeFamily j n p 1 =
      perfectOpenScalarZeroPairTargetCube j n p := by
  apply GenLoop.ext
  intro z
  exact (congrArg (fun y ↦ SSet.toTop.map
    (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom y)
      ((realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)).apply_one
        (p z))).trans (perfectOpenScalarZeroPairTargetCube_diagonal j n p z).symm

/-- The fine cone Theta target is the actual public-cone/right pair on the same input. -/
theorem perfectOpenScalarConeThetaFineCubeFamily_target :
    perfectOpenScalarConeThetaFineCubeFamily j r q hq n p 1 =
      perfectOpenScalarConePairTargetCube j r q hq n p := by
  apply GenLoop.ext
  intro z
  exact (congrArg (fun y ↦ SSet.toTop.map
    (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).hom y)
      ((realizationSimplicialHomotopy
        (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)).apply_one (p z))).trans
          (perfectOpenScalarConePairTargetCube_diagonal j r q hq n p z).symm

/-- Actual product projections give the zero Theta target, with the distinct right cube. -/
theorem perfectOpenScalarZeroThetaFineCubeFamily_compact :
    perfectOpenScalarZeroThetaFineCubeFamily j n p 1 =
      coproductCube (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n GenLoop.const
        (perfectOpenScalarCanonicalRightCube j n p) :=
  (perfectOpenScalarZeroThetaFineCubeFamily_target j n p).trans
    (perfectOpenScalarZeroPairTargetCube_compact j n p)

/-- Actual product projections give the quotient-first public-cone/right Theta target. -/
theorem perfectOpenScalarConeThetaFineCubeFamily_compact :
    perfectOpenScalarConeThetaFineCubeFamily j r q hq n p 1 =
      coproductCube (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
        (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalRightCube j n p) :=
  (perfectOpenScalarConeThetaFineCubeFamily_target j r q hq n p).trans
    (perfectOpenScalarConePairTargetCube_compact j r q hq n p)

/-- The original fine zero cylinder has only its target presentation transported. -/
def perfectOpenScalarZeroThetaCompactPath :
    Path (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (QuotientRows.oneIdToZero (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p)
      (coproductCube (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n GenLoop.const
        (perfectOpenScalarCanonicalRightCube j n p)) :=
  (perfectOpenScalarZeroThetaFineCubePath j n p).cast rfl
    (perfectOpenScalarZeroThetaFineCubeFamily_compact j n p).symm

/-- The original fine cone cylinder has the actual compact quotient-first target. -/
def perfectOpenScalarConeThetaCompactPath :
    Path (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p)
      (coproductCube (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
        (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalRightCube j n p)) :=
  (perfectOpenScalarConeThetaFineCubePath j r q hq n p).cast rfl
    (perfectOpenScalarConeThetaFineCubeFamily_compact j r q hq n p).symm

/-- The target transport leaves every original zero-cylinder time and spatial point unchanged. -/
theorem perfectOpenScalarZeroThetaCompactPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarZeroThetaCompactPath j n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
          (t, p z)) := rfl

/-- The target transport leaves every original cone-cylinder time and spatial point unchanged. -/
theorem perfectOpenScalarConeThetaCompactPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarConeThetaCompactPath j r q hq n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace)).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
          (t, p z)) := rfl

/-- The actual square and whole reversed canonical cylinder construct the geometric Theta word. -/
def perfectOpenScalarSumNormalizationThetaHomotopy :
    (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.Homotopy
      ((CompactCoproductEndpoint.thetaOne (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j) n
        (perfectOpenScalarConeThetaCompactPath j r q hq n p)).trans
        ((coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
          (Path.refl (perfectOpenScalarCubeChangeWeak j n
            (perfectOpenScalarCanonicalRightCube j n p)))).trans
            (CompactCoproductEndpoint.thetaZero (RingedSpace.perfectComplexesWaldhausen
              X.toRingedSpace) (perfectOpenNested j) n
              (perfectOpenScalarZeroThetaCompactPath j n p)).symm)) := by
  refine (perfectOpenScalarSumNormalizationReversedHomotopy j r q hq n p).cast rfl ?_
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  have hc (s : unitInterval) :
      (perfectOpenScalarSumNormalizationCanonicalFinePath j r q hq n p).symm s z =
        coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
          (Path.refl (perfectOpenScalarCubeChangeWeak j n
            (perfectOpenScalarCanonicalRightCube j n p))) s z := by
    change perfectOpenScalarSumNormalizationCanonicalPath j r q hq n p
      (unitInterval.symm s) z = _
    rw [perfectOpenScalarSumNormalizationCanonicalPath_apply]
    exact perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact
      j r q hq n p s z
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · rfl
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hc _
    · rfl

/-- Every geometric Theta interpolation keeps the entire original spatial boundary. -/
theorem perfectOpenScalarSumNormalizationThetaHomotopy_boundary (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationThetaHomotopy j r q hq n p (s, t) z =
      (W).kBasepoint :=
  (perfectOpenScalarSumNormalizationThetaHomotopy j r q hq n p (s, t)).property z hz

/-- The fine return retains the original identity additivity path, actual Theta and left unit. -/
def perfectOpenScalarNormalizationGamma :=
  CompactCoproductEndpoint.gamma (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)

/-- The original fine inverse-prefix return includes the complete identity path and cancellation. -/
def perfectOpenScalarNormalizationNu :=
  CompactCoproductEndpoint.nu (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)

/-- The actual fine endpoint retains q-first separation and the original inverse-prefix tail. -/
def perfectOpenScalarNormalizedFineDelta :=
  CompactCoproductEndpoint.delta (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)
    (perfectOpenScalarConeThetaCompactPath j r q hq n p)

/-- The moving coarse null retains both reversed old edges, cancellation and exact source cast. -/
def perfectOpenScalarNormalizedTerminalNull :=
  CompactCoproductEndpoint.normalizedNull (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j) n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarFineCubeSumPath j r q hq n p)

/-- The actual geometric data construct the whole normalized endpoint for the original cube. -/
def perfectOpenScalarNormalizedEndpointHomotopy :
    (perfectOpenScalarNormalizedTerminalNull j r q hq n p).Homotopy
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
          (perfectOpenScalarCanonicalNullPath j r q hq n p)) :=
  CompactCoproductEndpoint.normalizedNullHomotopy (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (perfectOpenNested j) n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)
    (perfectOpenScalarConeThetaCompactPath j r q hq n p)
    (perfectOpenScalarCanonicalNullPath j r q hq n p)
    (perfectOpenScalarFineCubeSumPath j r q hq n p)
    (perfectOpenScalarSumNormalizationThetaHomotopy j r q hq n p)

/-- The entire original terminal null is the initial side of the constructed comparison. -/
theorem perfectOpenScalarNormalizedEndpointHomotopy_zero (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (0, t) =
      perfectOpenScalarNormalizedTerminalNull j r q hq n p t :=
  (perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p).apply_zero t

/-- The entire canonical null follows the actual mapped fine delta, with its original speed. -/
theorem perfectOpenScalarNormalizedEndpointHomotopy_one (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (1, t) =
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
          (perfectOpenScalarCanonicalNullPath j r q hq n p)) t :=
  (perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p).apply_one t

/-- Both comparison times preserve every original spatial boundary, including degree zero. -/
theorem perfectOpenScalarNormalizedEndpointHomotopy_boundary (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (s, t) z = (W).kBasepoint :=
  (perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (s, t)).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumCubeNormalization.lean:34-609"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedEndpointHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedEndpointHomotopy_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedEndpointHomotopy_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedEndpointHomotopy_boundary
