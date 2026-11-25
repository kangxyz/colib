/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinaryPath
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrumFaceEvaluation

/-!
# The actual global Bass projection path for the identity boundary

The five original projection nodes and their full reference isomorphisms are built directly
from the global scheme arrows. Both normalization paths and the entire comparison cylinder
retain their original coordinates. No coefficient model identification is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityProjection

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable (X : Scheme.{u})

/-- The shared source of the positive and inverse-coordinate projection normalization triangles. -/
abbrev source := BoundedFlatPerfectBinarySimplex.sourceMap (plus.app X) (projection.app X)

/-- The two actual binary composites have precisely the same geometric projection. -/
theorem source_eq : (source X).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (minus.app X) (projection.app X)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback
      ((plus_projection X).trans (minus_projection X).symm))

/-- Transport between the two actual geometric source functors, with no chosen new homotopy. -/
def sourceIso := eqToIso (source_eq X)

/-- A model map equipped with an isomorphism from the shared projection-normalization source. -/
abbrev Node := Σ F : asSmallCategory (W X) ⟶
    asSmallCategory (W (laurent.obj X)), (source X).hom.toFunctor ≅ F.hom.toFunctor

/-- Both old binary normalization intermediates and endpoints; only the equal source is shared. -/
def nodes : Fin 5 → Node X :=
  ![⟨source X, Iso.refl _⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap (plus.app X) (projection.app X),
      BoundedFlatPerfectBinarySimplex.first (plus.app X) (projection.app X)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap (plus.app X) (projection.app X),
      BoundedFlatPerfectBinarySimplex.total (plus.app X) (projection.app X)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap (minus.app X) (projection.app X),
      sourceIso X ≪≫
        BoundedFlatPerfectBinarySimplex.first (minus.app X) (projection.app X)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap (minus.app X) (projection.app X),
      sourceIso X ≪≫
        BoundedFlatPerfectBinarySimplex.total (minus.app X) (projection.app X)⟩]

/-- The 4-simplex containing both projection normalization triangles with their common source
shared. -/
def simplex : ModelSimplex
    (asSmallCategory (W X))
    (asSmallCategory (W (laurent.obj X))) 4 :=
  ModelSimplex.ofIsos (source X) (fun i ↦ (nodes X i).1) (fun i ↦ (nodes X i).2)

/-- The face inclusion selecting the positive normalization triangle on vertices `0, 1, 2`. -/
def plusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The face inclusion selecting the inverse-coordinate normalization triangle on vertices `0,
3, 4`. -/
def minusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The entire positive original triangle is a face, with both native transformations. -/
theorem plus_face : (simplex X).face plusFace =
    BoundedFlatPerfectBinarySimplex.simplex (plus.app X) (projection.app X) := by
  unfold simplex BoundedFlatPerfectBinarySimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    fin_cases i <;> fin_cases j <;> rfl

/-- The unchanged vertices of the negative binary normalization triangle. -/
def minusVertices : Fin 3 →
    (asSmallCategory (W X) ⟶
      asSmallCategory (W (laurent.obj X))) :=
  ![BoundedFlatPerfectBinarySimplex.sourceMap (minus.app X) (projection.app X),
    BoundedFlatPerfectBinarySimplex.intermediateMap (minus.app X) (projection.app X),
    BoundedFlatPerfectBinarySimplex.targetMap (minus.app X) (projection.app X)]

/-- The source-to-vertex references of the inverse-coordinate normalization triangle. -/
def minusReferences : ∀ i,
    (BoundedFlatPerfectBinarySimplex.sourceMap (minus.app X) (projection.app X)).hom.toFunctor ≅
      (minusVertices X i).hom.toFunctor :=
  Fin.cases (Iso.refl _)
    (Fin.cases (BoundedFlatPerfectBinarySimplex.first (minus.app X) (projection.app X))
      (Fin.cases
        (BoundedFlatPerfectBinarySimplex.total (minus.app X) (projection.app X))
        (fun i ↦ Fin.elim0 i)))

/-- The inverse-coordinate triangle nodes transported to the positive triangle's source
reference. -/
def minusNodes (i : Fin 3) : Node X :=
  ⟨minusVertices X i, sourceIso X ≪≫ minusReferences X i⟩

/-- Change only the common reference of the entire negative triangle. -/
theorem minus_reference :
    ModelSimplex.ofIsos (source X) (fun i ↦ (minusNodes X i).1)
      (fun i ↦ (minusNodes X i).2) =
      BoundedFlatPerfectBinarySimplex.simplex (minus.app X) (projection.app X) :=
  ModelSimplex.ofIsos_change_reference (sourceIso X) (minusVertices X) (minusReferences X)

/-- The inverse-coordinate triangle keeps its original full functors and reference isomorphisms. -/
theorem minus_face : (simplex X).face minusFace =
    BoundedFlatPerfectBinarySimplex.simplex (minus.app X) (projection.app X) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  refine (ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes X (minusFace.toOrderHom i)) (minusNodes X) ?_).trans
    (minus_reference X)
  intro i
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq X)
    simp [sourceIso, minusReferences]
  · rfl
  · rfl

/-- The exact positive split path, before the Bass reversal. -/
theorem plus_native : PathLift (simplex X) (binaryPath 0 1 2)
    (plusHomotopy X) := by
  intro n t x
  have hmap := map_binaryPath plusFace 0 1 2 t
  change StdSimplex.map plusFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 1 2 t at hmap
  rw [← hmap, prespectrumSimplexFamily_face, plus_face]
  exact BoundedFlatPerfectBinarySimplex.native_path _ _ n t x

/-- The exact inverse split path, including its distinct native normalization intermediate. -/
theorem minus_native : PathLift (simplex X) (binaryPath 0 3 4)
    (minusHomotopy X) := by
  intro n t x
  have hmap := map_binaryPath minusFace 0 1 2 t
  change StdSimplex.map minusFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 3 4 t at hmap
  rw [← hmap, prespectrumSimplexFamily_face, minus_face]
  exact BoundedFlatPerfectBinarySimplex.native_path _ _ n t x

/-- Retain the literal reversed positive path followed by the original negative path. -/
def parameter : Path (StdSimplex.single 2 : StdSimplex ℝ (Fin 5)) (StdSimplex.single 4) :=
  (binaryPath 0 1 2).symm.trans (binaryPath 0 3 4)

/-- The whole original Bass cylinder path has this one scalar lift. -/
theorem native : PathLift (simplex X) parameter
    (squareHomotopy X) :=
  PathLift.trans _ (PathLift.symm _ (plus_native X)) (minus_native X)


end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityProjection
