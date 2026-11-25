/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitBottom

/-!
# The original moving middle cell of the raw Bass identity top

Unlike the bottom face, this product puts the base coefficient identity before
the five-node Bass projection. Both original times and the original common
reference survive. Adapted from `CoefficientPolynomialSpanUnitNodes.lean` and
`CoefficientPolynomialSpanUnitSimplex.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopMiddle

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "idRefs" => BoundedFlatPerfectIdentitySimplex.identityReferences
local notation "idSimplex" => BoundedFlatPerfectIdentitySimplex.identitySimplex
local notation "idVertices" => BoundedFlatPerfectIdentitySimplex.identityVertices
local notation "idNative" => BoundedFlatPerfectIdentitySimplex.identity_native
local notation "idSource" => BoundedFlatPerfectIdentitySimplex.source
local notation "bassProjNative" => BoundedFlatCoefficientBassProjectionPath.native
local notation "bassProjNodes" => BoundedFlatCoefficientBassProjectionPath.nodes
local notation "bassProjParameter" => BoundedFlatCoefficientBassProjectionPath.parameter
local notation "bassProjSimplex" => BoundedFlatCoefficientBassProjectionPath.simplex
local notation "bassProjSource" => BoundedFlatCoefficientBassProjectionPath.source
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

local notation "A" => space (op P, a)
local notation "L" => space (op P, Functor.obj (laurentUnderFunctor R) a)

/-- All fifteen original top-middle nodes, with their full product reference isomorphisms. -/
def nodes (i : Fin 15) : Σ F : asSmallCategory (W A) ⟶ asSmallCategory (W L),
    (bottomSrc P a).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨CommonReferenceProduct.vertices (idVertices A) (fun j ↦ (bassProjNodes P a j).1) i,
    CommonReferenceProduct.references (idSource A) (idVertices A)
      (idRefs A) (bassProjSource P a) (fun j ↦ (bassProjNodes P a j).1)
      (fun j ↦ (bassProjNodes P a j).2) i⟩

/-- Its common reference is exactly the original raw identity anchor. -/
def simplex : ModelSimplex (asSmallCategory (W A)) (asSmallCategory (W L)) 14 :=
  ModelSimplex.ofIsos (bottomSrc P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

/-- The literal full node diagram is the actual identity-by-projection product. -/
theorem middle_family : simplex P a =
    CommonReferenceProduct.simplex (idSource A) (idVertices A) (idRefs A)
      (bassProjSource P a) (fun j ↦ (bassProjNodes P a j).1)
      (fun j ↦ (bassProjNodes P a j).2) := rfl

/-- The original top-middle parameter retains identity time first and projection time second. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, bassProjParameter z.2), by fun_prop⟩

/-- The first product factor is the actual coefficient identity, with its original endpoint cast. -/
theorem identity_native (n : ℕ) (r : unitInterval) (x : (originalPrespectrum (W A)).space n) :
    prespectrumSimplexFamily (idSimplex A) n (binaryPath (k := 2) 0 1 2 r, x) =
      (boundedAboveFlatCoefficientIdentityHomotopy P a).level n (r, x) := by
  rw [boundedAboveFlatCoefficientIdentityHomotopy, Homotopy.cast_level]
  exact idNative A n r x

/-- The moving middle overlap is the base identity followed by the original Bass cylinder. -/
theorem native (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum (W A)).space n) :
    prespectrumSimplexFamily (simplex P a) n (parameter.{u} (r, s), x) =
      (boundedAboveFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder (K (polynomialProjection P a)) (K (polynomialProjection P a)) n
          (s, (boundedAboveFlatCoefficientIdentityHomotopy P a).level n (r, x))) := by
  rw [middle_family]
  refine (CommonReferenceProduct.prespectrum_comp (idSource A) (idVertices A)
    (idRefs A) (bassProjSource P a) (fun j ↦ (bassProjNodes P a j).1)
    (fun j ↦ (bassProjNodes P a j).2) n x
    (binaryPath (k := 2) 0 1 2 r) (bassProjParameter s)).trans ?_
  change prespectrumSimplexFamily (bassProjSimplex P a) n (bassProjParameter s,
    prespectrumSimplexFamily (idSimplex A) n (binaryPath (k := 2) 0 1 2 r, x)) = _
  rw [identity_native, bassProjNative P a n s _]
  rfl

/-- The original initial projection row, before gluing the raw identity top. -/
theorem parameter_zero (s : unitInterval) :
    parameter.{u} (0, s) =
      StdSimplex.map (SimplexGrid.rowFace 2 4 0).toOrderHom (bassProjParameter s) := by
  change SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 0, bassProjParameter s) = _
  rw [Path.source, SimplexGrid.parameter_row]

/-- The original terminal projection row, with the projection clock unchanged. -/
theorem parameter_one (s : unitInterval) :
    parameter.{u} (1, s) =
      StdSimplex.map (SimplexGrid.rowFace 2 4 2).toOrderHom (bassProjParameter s) := by
  change SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 1, bassProjParameter s) = _
  rw [Path.target, SimplexGrid.parameter_row]

/-- The chart-positive projection column has the original labels [2, 7, 12]. -/
theorem parameter_left (r : unitInterval) :
    parameter.{u} (r, 0) = binaryPath (k := 14) 2 7 12 r := by
  change SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r, bassProjParameter 0) = _
  rw [Path.source, SimplexGrid.parameter_column]
  exact map_binaryPath (SimplexGrid.columnFace 2 4 2) 0 1 2 r

/-- The inverse projection column has the different original labels [4, 9, 14]. -/
theorem parameter_right (r : unitInterval) :
    parameter.{u} (r, 1) = binaryPath (k := 14) 4 9 14 r := by
  change SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r, bassProjParameter 1) = _
  rw [Path.target, SimplexGrid.parameter_column]
  exact map_binaryPath (SimplexGrid.columnFace 2 4 4) 0 1 2 r

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopMiddle
