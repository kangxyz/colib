/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberAdditivitySquare
public import Colib.KTheory.Waldhausen.Additivity.DiagonalKMap
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrack
public import Colib.Topology.Homotopy.SquareBoundaryPaths

/-! # The actual scalar additivity square on original subdivision cubes

Both continuous times and every spatial coordinate remain literal. The four old edge paths
in the original generalized-loop space give the exact oriented boundary-route homotopy.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeSquare.lean:40-193`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open SSet
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance scalarCubeCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
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
def perfectOpenScalarCofiberCubeSquare :
    C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) (W).Delooping (W).kBasepoint) where
  toFun ts := ⟨⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
    (perfectOpenScalarBasedAdditivitySquare j r q hq (ts.1, (ts.2, p z))), by fun_prop⟩, by
      intro z hz
      change SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarBasedAdditivitySquare j r q hq (ts.1, (ts.2, p z))) = (W).kBasepoint
      exact (congrArg (fun x ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarBasedAdditivitySquare j r q hq (ts.1, (ts.2, x))))
        (p.property z hz)).trans
          ((congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y)
            (perfectOpenScalarBasedAdditivitySquare_fixed_zero j r q hq ts.1 ts.2)).trans
              (diagonalRealization_basepoint W))⟩
  continuous_toFun := by
    have hc : Continuous (fun ts : unitInterval × unitInterval ↦
        (⟨fun z ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom
          (perfectOpenScalarBasedAdditivitySquare j r q hq (ts.1, (ts.2, p z))),
          by fun_prop⟩ : C((Fin (n + 1) → unitInterval), (W).Delooping))) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × unitInterval) ×
          (Fin (n + 1) → unitInterval) ↦
        SSet.toTop.map (bisimplicialDiagonalIso W).hom
          (perfectOpenScalarBasedAdditivitySquare j r q hq (z.1.1, (z.1.2, p z.2))))
      fun_prop
    exact hc.subtype_mk _

/-- Transformation time, additivity time and every original cube coordinate remain unchanged. -/
theorem perfectOpenScalarCofiberCubeSquare_apply (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarBasedAdditivitySquare j r q hq (t, (s, p z))) := rfl

/-- The entire spatial boundary is fixed at independently varying square times. -/
theorem perfectOpenScalarCofiberCubeSquare_boundary (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z = (W).kBasepoint :=
  (perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s)).property z hz

/-- The whole original transformation zero face survives actual diagonal realization. -/
theorem perfectOpenScalarCofiberCubeSquare_transformation_zero (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (0, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          W
          (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
            X.toRingedSpace))))) (QuotientRows.oneIdToZero W)
          (perfectOpenScalarIdentityCofibrationSequence j) (s, p z)) := by
  rw [perfectOpenScalarCofiberCubeSquare_apply,
    perfectOpenScalarBasedAdditivitySquare_transformation_zero]

/-- The whole original transformation one face survives actual diagonal realization. -/
theorem perfectOpenScalarCofiberCubeSquare_transformation_one (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (1, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          W
          (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
          (perfectOpenScalarCofibrationSequence j r) (s, p z)) := by
  rw [perfectOpenScalarCofiberCubeSquare_apply,
    perfectOpenScalarBasedAdditivitySquare_transformation_one]

/-- The whole original additivity zero face survives actual diagonal realization. -/
theorem perfectOpenScalarCofiberCubeSquare_additivity_zero (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 0) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
          (t, realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
              (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
            (p z))) := by
  rw [perfectOpenScalarCofiberCubeSquare_apply,
    perfectOpenScalarBasedAdditivitySquare_additivity_zero]

/-- The whole original additivity one face survives actual diagonal realization. -/
theorem perfectOpenScalarCofiberCubeSquare_additivity_one (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 1) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq)
          (t, p z)) := by
  rw [perfectOpenScalarCofiberCubeSquare_apply,
    perfectOpenScalarBasedAdditivitySquare_additivity_one]

/-- The literal inclusion edge path of the displayed generalized-loop square. -/
def perfectOpenScalarCofiberCubeInclusionPath :
    Path (perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 0))
      (perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 0)) :=
  (Path.id.prod (Path.refl (0 : unitInterval))).map
    (perfectOpenScalarCofiberCubeSquare j r q hq n p).continuous

/-- The original edge parameter is not changed. -/
theorem perfectOpenScalarCofiberCubeInclusionPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeInclusionPath j r q hq n p t z =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 0) z := rfl

/-- The literal identity edge path of the displayed generalized-loop square. -/
def perfectOpenScalarCofiberCubeIdentityPath :
    Path (perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 0))
      (perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 1)) :=
  ((Path.refl (0 : unitInterval)).prod Path.id).map
    (perfectOpenScalarCofiberCubeSquare j r q hq n p).continuous

/-- The original edge parameter is not changed. -/
theorem perfectOpenScalarCofiberCubeIdentityPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeIdentityPath j r q hq n p t z =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, t) z := rfl

/-- The literal scalar edge path of the displayed generalized-loop square. -/
def perfectOpenScalarCofiberCubeScalarPath :
    Path (perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 0))
      (perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 1)) :=
  ((Path.refl (1 : unitInterval)).prod Path.id).map
    (perfectOpenScalarCofiberCubeSquare j r q hq n p).continuous

/-- The original edge parameter is not changed. -/
theorem perfectOpenScalarCofiberCubeScalarPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeScalarPath j r q hq n p t z =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, t) z := rfl

/-- The literal sum edge path of the displayed generalized-loop square. -/
def perfectOpenScalarCofiberCubeSumPath :
    Path (perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 1))
      (perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 1)) :=
  (Path.id.prod (Path.refl (1 : unitInterval))).map
    (perfectOpenScalarCofiberCubeSquare j r q hq n p).continuous

/-- The original edge parameter is not changed. -/
theorem perfectOpenScalarCofiberCubeSumPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSumPath j r q hq n p t z =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 1) z := rfl

/-- Exactly one reversal of the existing square interpolation gives the oriented boundary route. -/
def perfectOpenScalarCofiberCubeBoundaryHomotopy :
    ((perfectOpenScalarCofiberCubeInclusionPath j r q hq n p).trans
      (perfectOpenScalarCofiberCubeScalarPath j r q hq n p)).Homotopy
      ((perfectOpenScalarCofiberCubeIdentityPath j r q hq n p).trans
        (perfectOpenScalarCofiberCubeSumPath j r q hq n p)) :=
  (squareBoundaryPathHomotopy (perfectOpenScalarCofiberCubeSquare j r q hq n p)).symm

/-- The constructive boundary homotopy is the specified original interpolation, reversed once. -/
theorem perfectOpenScalarCofiberCubeBoundaryHomotopy_eq :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p =
      (squareBoundaryPathHomotopy
        (perfectOpenScalarCofiberCubeSquare j r q hq n p)).symm := rfl

/-- Every intermediate path remains fixed on the entire original spatial cube boundary. -/
theorem perfectOpenScalarCofiberCubeBoundaryHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  (perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t)).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0316",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeSquare.lean:40-193"
    "adaptation" "The actual scalar cube square with all faces and its oriented boundary homotopy"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare_boundary
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare_transformation_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare_transformation_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare_additivity_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeSquare_additivity_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeBoundaryHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberCubeBoundaryHomotopy_boundary
