/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinaryPath
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassSquareComparison
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations

/-! The original two-chart Bass cylinder path in one actual five-vertex simplex. -/
/-! Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionPath.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassProjectionPath
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The shared source of the positive and inverse-coordinate projection normalization triangles. -/
abbrev source :=
  BoundedFlatPerfectBinarySimplex.sourceMap (laurentPlus P a) (polynomialProjection P a)

/-- The two actual binary composites have precisely the same geometric projection. -/
theorem source_eq : (source P a).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a)
      (polynomialProjection P a)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm))

/-- Transport between the two actual geometric source functors, with no chosen new homotopy. -/
def sourceIso := eqToIso (source_eq P a)

/-- A model map equipped with an isomorphism from the shared projection-normalization source. -/
abbrev Node :=
  Σ F : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn (space (op P, a))) ⟶
    asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn
      (space (op P, (laurentUnderFunctor R).obj a))), (source P a).hom.toFunctor ≅ F.hom.toFunctor

/-- Both old binary normalization intermediates and endpoints; only the equal source is shared. -/
def nodes : Fin 5 → Node P a :=
  ![⟨source P a, Iso.refl _⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap (laurentPlus P a) (polynomialProjection P a),
      BoundedFlatPerfectBinarySimplex.first (laurentPlus P a) (polynomialProjection P a)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap (laurentPlus P a) (polynomialProjection P a),
      BoundedFlatPerfectBinarySimplex.total (laurentPlus P a) (polynomialProjection P a)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap (laurentMinus P a) (polynomialProjection P a),
      sourceIso P a ≪≫
        BoundedFlatPerfectBinarySimplex.first (laurentMinus P a) (polynomialProjection P a)⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap (laurentMinus P a) (polynomialProjection P a),
      sourceIso P a ≪≫
        BoundedFlatPerfectBinarySimplex.total (laurentMinus P a) (polynomialProjection P a)⟩]

/-- The 4-simplex containing both projection normalization triangles with their common source
shared. -/
def simplex : ModelSimplex
    (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn (space (op P, a))))
    (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn
      (space (op P, (laurentUnderFunctor R).obj a)))) 4 :=
  ModelSimplex.ofIsos (source P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

/-- The face inclusion selecting the positive normalization triangle on vertices `0, 1, 2`. -/
def plusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The face inclusion selecting the inverse-coordinate normalization triangle on vertices `0,
3, 4`. -/
def minusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The entire positive original triangle is a face, with both native transformations. -/
theorem plus_face : (simplex P a).face plusFace =
    BoundedFlatPerfectBinarySimplex.simplex (laurentPlus P a) (polynomialProjection P a) := by
  unfold simplex BoundedFlatPerfectBinarySimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    fin_cases i <;> fin_cases j <;> rfl

/-- The unchanged vertices of the negative binary normalization triangle. -/
def minusVertices : Fin 3 →
    (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn (space (op P, a))) ⟶
      asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn
        (space (op P, (laurentUnderFunctor R).obj a)))) :=
  ![BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a) (polynomialProjection P a),
    BoundedFlatPerfectBinarySimplex.intermediateMap (laurentMinus P a) (polynomialProjection P a),
    BoundedFlatPerfectBinarySimplex.targetMap (laurentMinus P a) (polynomialProjection P a)]

/-- The source-to-vertex references of the inverse-coordinate normalization triangle. -/
def minusReferences : ∀ i,
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a)
      (polynomialProjection P a)).hom.toFunctor ≅
      (minusVertices P a i).hom.toFunctor :=
  Fin.cases (Iso.refl _)
    (Fin.cases (BoundedFlatPerfectBinarySimplex.first (laurentMinus P a) (polynomialProjection P a))
      (Fin.cases
        (BoundedFlatPerfectBinarySimplex.total (laurentMinus P a) (polynomialProjection P a))
        (fun i ↦ Fin.elim0 i)))

/-- The inverse-coordinate triangle nodes transported to the positive triangle's source
reference. -/
def minusNodes (i : Fin 3) : Node P a :=
  ⟨minusVertices P a i, sourceIso P a ≪≫ minusReferences P a i⟩

/-- The inverse face retains every complete node, including its transported source. -/
theorem minus_face_nodes (i : Fin 3) :
    nodes P a (minusFace.toOrderHom i) = minusNodes P a i := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq P a)
    simp [sourceIso, minusReferences]
  · rfl
  · rfl

/-- Change only the common reference of the entire negative triangle. -/
theorem minus_reference :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (minusNodes P a i).1)
      (fun i ↦ (minusNodes P a i).2) =
      BoundedFlatPerfectBinarySimplex.simplex (laurentMinus P a) (polynomialProjection P a) :=
  ModelSimplex.ofIsos_change_reference (sourceIso P a) (minusVertices P a) (minusReferences P a)

/-- The inverse-coordinate triangle keeps its original full functors and reference isomorphisms. -/
theorem minus_face : (simplex P a).face minusFace =
    BoundedFlatPerfectBinarySimplex.simplex (laurentMinus P a) (polynomialProjection P a) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes P a (minusFace.toOrderHom i)) (minusNodes P a) (minus_face_nodes P a)).trans
    (minus_reference P a)

/-- The exact positive split path, before the Bass reversal. -/
theorem plus_native : PathLift (simplex P a) (binaryPath 0 1 2)
    (boundedAboveFlatCoefficientLaurentPlusHomotopy P a) := by
  intro n t x
  have hmap := map_binaryPath plusFace 0 1 2 t
  change StdSimplex.map plusFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 1 2 t at hmap
  rw [← hmap, prespectrumSimplexFamily_face, plus_face]
  exact BoundedFlatPerfectBinarySimplex.native_path _ _ n t x

/-- The exact inverse split path, including its distinct native normalization intermediate. -/
theorem minus_native : PathLift (simplex P a) (binaryPath 0 3 4)
    (boundedAboveFlatCoefficientLaurentMinusHomotopy P a) := by
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
theorem native : PathLift (simplex P a) parameter
    (boundedAboveFlatCoefficientBassSquareHomotopy P a) :=
  PathLift.trans _ (PathLift.symm _ (plus_native P a)) (minus_native P a)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassProjectionPath
