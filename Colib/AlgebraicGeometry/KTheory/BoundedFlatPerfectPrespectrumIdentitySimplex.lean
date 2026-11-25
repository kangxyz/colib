/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitTracks
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex
public import Mathlib.CategoryTheory.Functor.Category

/-!
# The three-node simplex of the original bounded-flat identity track

The vertices are the actual normalized identity pullback, the rebased identity intermediate,
and the literal identity functor. The two original normalization isomorphisms give the
native triangle at every stage and at every loop, comparison, and path time.

Adapted from Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`:
`OriginalUnitSquareSimplex.lean:29-50,509-560` and
`CoefficientPolynomialSpanUnitSimplex.lean:30-99` under
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
  CategoryTheory.Waldhausen.IteratedS
open Convexity Topology
open scoped Simplicial Topology unitInterval
universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectIdentitySimplex

open AlgebraicGeometry.RingedSpace

/-- The original Waldhausen structure of bounded-flat perfect complexes on the scheme. -/
abbrev structureOn (X : Scheme.{u}) := boundedAboveFlatPerfectWaldhausen X.toRingedSpace

/-- The chosen-zero rebasing of the original identity functor. -/
def rebasedIdentityIso (X : Scheme.{u}) :=
  CategoryTheory.rebaseFunctorIso
    (𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (structureOn X).zero (structureOn X).zero
    (((IsExact.id (structureOn X).cof (structureOn X).weq).zero
      (structureOn X).isZero).iso (structureOn X).isZero)

/-- The actual normalized identity pullback as an exact small-model map. -/
def source (X : Scheme.{u}) : asSmallCategory (structureOn X) ⟶
    asSmallCategory (structureOn X) :=
  asSmallCategoryMap (structureOn X) (structureOn X)
    (boundedAboveFlatPerfectNormalizedPullback_exact (𝟙 X))
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero _)

/-- The actual intermediate chosen-zero rebasing of the identity. -/
def intermediate (X : Scheme.{u}) : asSmallCategory (structureOn X) ⟶
    asSmallCategory (structureOn X) :=
  asSmallCategoryMap (structureOn X) (structureOn X)
    (IsExact.id (structureOn X).cof (structureOn X).weq).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The literal identity on complexes, lifted through the same small-model equivalence. -/
def target (X : Scheme.{u}) : asSmallCategory (structureOn X) ⟶
    asSmallCategory (structureOn X) :=
  asSmallCategoryMap (structureOn X) (structureOn X) (IsExact.id _ _) rfl

/-- The original geometric identity isomorphism with its chosen-zero normalization. -/
def first (X : Scheme.{u}) : (source X).hom.toFunctor ≅ (intermediate X).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedAboveFlatPerfectPullbackNormalizationIso (𝟙 X)).symm ≪≫
      boundedAboveFlatPerfectPullbackIdIso X ≪≫ rebasedIdentityIso X) AsSmall.up)

/-- The original inverse chosen-zero rebasing of the identity functor. -/
def second (X : Scheme.{u}) : (intermediate X).hom.toFunctor ≅ (target X).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (rebasedIdentityIso X).symm AsSmall.up)

/-- The three literal maps in the original identity track. -/
def identityVertices (X : Scheme.{u}) : Fin 3 →
    (asSmallCategory (structureOn X) ⟶ asSmallCategory (structureOn X)) :=
  ![source X, intermediate X, target X]

/-- The original comparison isomorphisms anchored at the identity pullback. -/
def identityReferences (X : Scheme.{u}) : ∀ i,
    (source X).hom.toFunctor ≅ (identityVertices X i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (first X)
    (Fin.cases (first X ≪≫ second X) (fun i ↦ Fin.elim0 i)))

/-- The exact common-reference identity triangle. -/
def identitySimplex (X : Scheme.{u}) :
    ModelSimplex (asSmallCategory (structureOn X)) (asSmallCategory (structureOn X)) 2 :=
  ModelSimplex.ofIsos (source X) (identityVertices X) (identityReferences X)

/-- The two adjacent components are the original geometric and rebasing transformations. -/
theorem identitySimplex_triangle (X : Scheme.{u}) : identitySimplex X =
    ModelSimplex.triangle (first X).hom (second X).hom
      (fun _ ↦ (structureOn X).asSmall.weq_iso _ inferInstance)
      (fun _ ↦ (structureOn X).asSmall.weq_iso _ inferInstance) := by
  have h : identitySimplex X = (identitySimplex X).face (𝟙 ⦋2⦌) :=
    ModelSimplex.ext_diagram (by rfl)
  rw [h]
  unfold identitySimplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The existing normalized unit comparison evaluates to the native split triangle. -/
theorem identity_comparison_level (X : Scheme.{u}) (n : ℕ) :
    ((boundedAboveFlatPerfectNormalizedIdTrackComparison X).level n).toContinuousMap =
      ((prespectrumTransformationCompositionHomotopy (first X).hom (second X).hom
        (fun _ ↦ (structureOn X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (structureOn X).asSmall.weq_iso _ inferInstance)).level n).toContinuousMap := by
  exact boundedAboveFlatPerfectNormalizedIdTrackComparison_level X n

/-- The actual barycentric unit triangle agrees with the original prespectrum comparison. -/
theorem identity_triangle_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (structureOn X)).space n) :
    prespectrumSimplexFamily (identitySimplex X) n
      (TheoremB.compositionTriangleHomotopy (r, s), x) =
      (boundedAboveFlatPerfectNormalizedIdTrackComparison X).level n (r, (s, x)) := by
  let y : (prespectrum (asSmallCategory (structureOn X))).space n := x
  let z : StdSimplex ℝ (Fin 3) := TheoremB.compositionTriangleHomotopy (r, s)
  have hη (A : (asSmallCategory (structureOn X)).obj.Obj) :
      (structureOn X).asSmall.weq ((first X).hom.app A) :=
    (structureOn X).asSmall.weq_iso _ inferInstance
  have hθ (A : (asSmallCategory (structureOn X)).obj.Obj) :
      (structureOn X).asSmall.weq ((second X).hom.app A) :=
    (structureOn X).asSmall.weq_iso _ inferInstance
  have hface := congrArg
    (fun M : ModelSimplex (asSmallCategory (structureOn X))
      (asSmallCategory (structureOn X)) 2 ↦ prespectrumSimplexFamily M n (z, y))
    (identitySimplex_triangle X)
  have htriangle :=
    prespectrumSimplexFamily_triangle (first X).hom (second X).hom hη hθ n r s y
  have hlevel := DFunLike.congr_fun (identity_comparison_level X n) (r, (s, y))
  exact hface.trans (htriangle.trans hlevel.symm)

/-- Both original unit steps retain their actual concatenation and speed at every level. -/
theorem identity_native (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (structureOn X)).space n) :
    prespectrumSimplexFamily (identitySimplex X) n
      (((TheoremB.triangleEdgePath 0 1).trans (TheoremB.triangleEdgePath 1 2)) s, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (s, x) := by
  let y : (prespectrum (asSmallCategory (structureOn X))).space n := x
  have hp : TheoremB.compositionTriangleHomotopy (1, s) =
      ((TheoremB.triangleEdgePath 0 1).trans (TheoremB.triangleEdgePath 1 2)) s :=
    TheoremB.compositionTriangleHomotopy.apply_one s
  have harg := congrArg
    (fun z : StdSimplex ℝ (Fin 3) ↦ prespectrumSimplexFamily (identitySimplex X) n (z, y))
    hp.symm
  exact harg.trans ((identity_triangle_native X n 1 s x).trans
    (((boundedAboveFlatPerfectNormalizedIdTrackComparison X).level n).apply_one (s, x)))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectIdentitySimplex
