/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityProjection
public import Colib.KTheory.Waldhausen.Iterated.SimplexProductDiagram

/-!
# The actual Laurent identity bottom face for arbitrary schemes

The original projection path and Laurent identity trace form an actual independent-time
product. All fifteen dependent nodes are transported only by the original base and Laurent
unit isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity Topology
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierBottom

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable (X : Scheme.{u})

/-- The actual bottom product's own reference in its original factor order. -/
abbrev productSource := InputIdentityProjection.source X ≫
  BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)

/-- Both complete unit isomorphisms give the original reanchoring of the bottom product. -/
def sourceIso : (InputIdentityNodes.source X).hom.toFunctor ≅ (productSource X).hom.toFunctor :=
  InputIdentityNodes.sourceToProjection X ≪≫
    (isoWhiskerLeft (InputIdentityProjection.source X).hom.toFunctor
      (BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
      BoundedFlatPerfectIdentitySimplex.second (laurent.obj X))).symm

/-- Each of the fifteen original product vertices and its complete reference isomorphism. -/
def nodes (i : Fin 15) : Σ F : asSmallCategory (W X) ⟶ asSmallCategory (W (laurent.obj X)),
    (InputIdentityNodes.source X).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (InputIdentityProjection.nodes X j).1)
    (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X)) i,
    sourceIso X ≪≫ CommonReferenceProduct.references (InputIdentityProjection.source X)
      (fun j ↦ (InputIdentityProjection.nodes X j).1) (fun j ↦
        (InputIdentityProjection.nodes X j).2)
      (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
        (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
        (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) i⟩

/-- The native bottom form of the exact common-reference identity product. -/
def simplex : ModelSimplex (asSmallCategory (W X)) (asSmallCategory (W (laurent.obj X))) 14 :=
  ModelSimplex.ofIsos (InputIdentityNodes.source X) (fun i ↦ (nodes X i).1) (fun i ↦ (nodes X i).2)

/-- Reanchoring the fifteen nodes preserves their entire original model simplex. -/
theorem product_family : simplex X =
    CommonReferenceProduct.simplex (InputIdentityProjection.source X)
      (fun j ↦ (InputIdentityProjection.nodes X j).1) (fun j ↦
        (InputIdentityProjection.nodes X j).2)
      (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
        (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
        (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) :=
  ModelSimplex.ofIsos_change_reference (sourceIso X) _ _

/-- Follow the unchanged Bass projection and then the literal two-step Laurent identity. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The native identity family includes the actual Laurent functor identity cast. -/
theorem laurent_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (W (laurent.obj X))).space n) :
    prespectrumSimplexFamily (BoundedFlatPerfectIdentitySimplex.identitySimplex
      (laurent.obj X)) n (binaryPath (k := 2) 0 1 2 r, x) =
      (InputIdentity.laurentHomotopy X).level n (r, x) := by
  rw [InputIdentity.laurentHomotopy, Homotopy.cast_level]
  exact BoundedFlatPerfectIdentitySimplex.identity_native (laurent.obj X) n r x

/-- The entire bottom is the native Laurent identity after the unchanged Bass map, even at level
zero. -/
theorem native (n : ℕ) (r t : unitInterval) (x : (originalPrespectrum (W X)).space n) :
    prespectrumSimplexFamily (simplex X) n (parameter.{u} (r, t), x) =
      (Homotopy.precomp (comparison X)
        (InputIdentity.laurentHomotopy X)).level n
        (r, HomotopyPushout.cylinder (K (projection.app X))
          (K (projection.app X)) n (t, x)) := by
  rw [product_family]
  refine (CommonReferenceProduct.prespectrum_comp (InputIdentityProjection.source X)
    (fun j ↦ (InputIdentityProjection.nodes X j).1) (fun j ↦ (InputIdentityProjection.nodes X j).2)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
      (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
      (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) n x
    (InputIdentityProjection.parameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  change prespectrumSimplexFamily (BoundedFlatPerfectIdentitySimplex.identitySimplex
    (laurent.obj X)) n
    (binaryPath (k := 2) 0 1 2 r,
      prespectrumSimplexFamily (InputIdentityProjection.simplex X) n
        (InputIdentityProjection.parameter t, x)) = _
  rw [InputIdentityProjection.native X n t x, laurent_native]
  rfl

/-- The lower comparison face retains the full initial projection column. -/
theorem parameter_zero (t : unitInterval) :
    parameter.{u} (0, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 0).toOrderHom
        (InputIdentityProjection.parameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2 (InputIdentityProjection.parameter t, binaryPath
    (k := 2) 0 1 2 0) = _
  rw [Path.source, SimplexGrid.parameter_column]

/-- The upper comparison face is the terminal projection column. -/
theorem parameter_one (t : unitInterval) :
    parameter.{u} (1, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 2).toOrderHom
        (InputIdentityProjection.parameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2 (InputIdentityProjection.parameter t, binaryPath
    (k := 2) 0 1 2 1) = _
  rw [Path.target, SimplexGrid.parameter_column]

/-- The full positive side retains both Laurent identity normalization edges. -/
theorem parameter_left (r : unitInterval) :
    parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change SimplexGrid.parameter.{u + 1} 4 2 (InputIdentityProjection.parameter 0, binaryPath
    (k := 2) 0 1 2 r) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The inverse side keeps its distinct terminal row and original identity speed. -/
theorem parameter_right (r : unitInterval) :
    parameter.{u} (r, 1) = binaryPath (k := 14) 12 13 14 r := by
  change SimplexGrid.parameter.{u + 1} 4 2 (InputIdentityProjection.parameter 1, binaryPath
    (k := 2) 0 1 2 r) = _
  rw [Path.target, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 4) 0 1 2 r


/-- The actual product gives the complete bottom in the fixed reference carrier. -/
def face : C(unitInterval × unitInterval, InputIdentityCarrierCharts.Carrier X) :=
  (CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)).comp (parameter.{u})

/-- The native bottom face retains every point of the Laurent identity and the original cylinder. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X) (face X)
      n ((r, t), x) =
      (Homotopy.precomp (comparison X) (InputIdentity.laurentHomotopy X)).level n
        (r, HomotopyPushout.cylinder (K (projection.app X))
          (K (projection.app X)) n (t, x)) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (InputIdentityNodes.source X)
    (face X) (nodes X) (r, t) (parameter.{u} (r, t)) rfl n x).trans (native X n r t x)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierBottom
