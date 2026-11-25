/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentUnitSquares
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassProjectionPath
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumIdentitySimplex
public import Colib.KTheory.Waldhausen.Iterated.RealizationSimplexComposition
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# The bottom face of the raw Bass identity cube

The original projection-by-Laurent-identity product uses two independent parameters and the
literal base identity anchor. Adapted from `CoefficientBassUnitBoundaryNodes.lean` and
`CoefficientBassUnitBottom.lean` at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This is the identity bottom face, not the bottom face of a coefficient-composition cube.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitBottom

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
open BoundedFlatPerfectIdentitySimplex
  (identityVertices identityReferences identitySimplex identity_native)
local notation "identitySource" => BoundedFlatPerfectIdentitySimplex.source
local notation "identityFirst" => BoundedFlatPerfectIdentitySimplex.first
local notation "identitySecond" => BoundedFlatPerfectIdentitySimplex.second
local notation "projectionSource" => BoundedFlatCoefficientBassProjectionPath.source
local notation "projectionNodes" => BoundedFlatCoefficientBassProjectionPath.nodes
local notation "projectionParameter" => BoundedFlatCoefficientBassProjectionPath.parameter

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

local notation "A" => space (op P, a)
local notation "L" => space (op P, Functor.obj (laurentUnderFunctor R) a)

/-- The unchanged top reference: original coefficient identity, then the Bass projection. -/
abbrev source := identitySource A ≫ projectionSource P a

/-- The actual bottom product's own reference in its original factor order. -/
abbrev bottomSource := projectionSource P a ≫ identitySource L

/-- The original unit isomorphism from the fixed top anchor to the Bass projection. -/
def sourceToProjection :
    (source P a).hom.toFunctor ≅ (projectionSource P a).hom.toFunctor :=
  isoWhiskerRight (identityFirst A ≪≫ identitySecond A) (projectionSource P a).hom.toFunctor

/-- Both complete unit isomorphisms give the original reanchoring of the bottom product. -/
def bottomSourceIso : (source P a).hom.toFunctor ≅ (bottomSource P a).hom.toFunctor :=
  sourceToProjection P a ≪≫
    (isoWhiskerLeft (projectionSource P a).hom.toFunctor
      (identityFirst L ≪≫ identitySecond L)).symm

/-- Each of the fifteen original product vertices and its complete reference isomorphism. -/
def nodes (i : Fin 15) : Σ F : asSmallCategory (W A) ⟶ asSmallCategory (W L),
    (source P a).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (projectionNodes P a j).1) (identityVertices L) i,
    bottomSourceIso P a ≪≫ CommonReferenceProduct.references (projectionSource P a)
      (fun j ↦ (projectionNodes P a j).1) (fun j ↦ (projectionNodes P a j).2)
      (identitySource L) (identityVertices L) (identityReferences L) i⟩

/-- The native bottom form of the exact common-reference identity product. -/
def simplex : ModelSimplex (asSmallCategory (W A)) (asSmallCategory (W L)) 14 :=
  ModelSimplex.ofIsos (source P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

/-- Reanchoring the fifteen nodes preserves their entire original model simplex. -/
theorem bottom_family : simplex P a =
    CommonReferenceProduct.simplex (projectionSource P a)
      (fun j ↦ (projectionNodes P a j).1) (fun j ↦ (projectionNodes P a j).2)
      (identitySource L) (identityVertices L) (identityReferences L) :=
  ModelSimplex.ofIsos_change_reference (bottomSourceIso P a) _ _

/-- Follow the unchanged Bass projection and then the literal two-step Laurent identity. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 2
    (projectionParameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The native identity family includes the same Laurent-functor and coefficient unit casts. -/
theorem laurent_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (W L)).space n) :
    prespectrumSimplexFamily (identitySimplex L) n (binaryPath (k := 2) 0 1 2 r, x) =
      (boundedAboveFlatCoefficientLaurentIdentityHomotopy P a).level n (r, x) := by
  rw [boundedAboveFlatCoefficientLaurentIdentityHomotopy, Homotopy.cast_level,
    boundedAboveFlatCoefficientIdentityHomotopy, Homotopy.cast_level]
  exact identity_native L n r x

/-- The entire bottom is the native Laurent identity after the unchanged Bass map, even at level
zero. -/
theorem native (n : ℕ) (r t : unitInterval) (x : (originalPrespectrum (W A)).space n) :
    prespectrumSimplexFamily (simplex P a) n (parameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
        (boundedAboveFlatCoefficientLaurentIdentityHomotopy P a)).level n
        (r, HomotopyPushout.cylinder (K (polynomialProjection P a))
          (K (polynomialProjection P a)) n (t, x)) := by
  rw [bottom_family]
  refine (CommonReferenceProduct.prespectrum_comp (projectionSource P a)
    (fun j ↦ (projectionNodes P a j).1) (fun j ↦ (projectionNodes P a j).2)
    (identitySource L) (identityVertices L) (identityReferences L) n x
    (projectionParameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  change prespectrumSimplexFamily (identitySimplex L) n
    (binaryPath (k := 2) 0 1 2 r,
      prespectrumSimplexFamily (BoundedFlatCoefficientBassProjectionPath.simplex P a) n
        (projectionParameter t, x)) = _
  rw [BoundedFlatCoefficientBassProjectionPath.native P a n t x, laurent_native]
  rfl

/-- The lower comparison face retains the full initial projection column. -/
theorem parameter_zero (t : unitInterval) :
    parameter.{u} (0, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 0).toOrderHom (projectionParameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2 (projectionParameter t, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, SimplexGrid.parameter_column]

/-- The upper comparison face is the terminal projection column. -/
theorem parameter_one (t : unitInterval) :
    parameter.{u} (1, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 2).toOrderHom (projectionParameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2 (projectionParameter t, binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target, SimplexGrid.parameter_column]

/-- The full positive side retains both Laurent identity normalization edges. -/
theorem parameter_left (r : unitInterval) :
    parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (projectionParameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The inverse side keeps its distinct terminal row and original identity speed. -/
theorem parameter_right (r : unitInterval) :
    parameter.{u} (r, 1) = binaryPath (k := 14) 12 13 14 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (projectionParameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 4) 0 1 2 r

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitBottom
