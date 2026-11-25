/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationComposition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinarySimplex

/-!
# The five original evaluation-input reference nodes

The original total, geometric-normalization, and evaluation-cut triangles sit in one
native small-model simplex. The chosen-zero maps and their actual reference isomorphisms
are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSimplex
open GlobalSectionChangeIndex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Evaluation after the original strict composite. -/
def sourceMap := boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op ≫ evaluationModel (op X)

/-- Evaluation followed by the original total raw map. -/
def totalMap := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g)

/-- Evaluation followed by the actual rebased unnormalized composite. -/
def intermediateMap := evaluationModel (op Z) ≫ BoundedFlatPerfectBinarySimplex.intermediateMap f g

/-- The intermediate evaluation cut uses the actual raw final factor. -/
def cutMap :=
  (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f

/-- The original raw composite with the evaluation cut at its source. -/
def targetMap := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f

/-- The full original geometric-normalization intermediate edge. -/
def geometricIso : (totalMap f g).hom.toFunctor ≅ (intermediateMap f g).hom.toFunctor :=
  isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor (BoundedFlatPerfectBinarySimplex.first f g)

/-- The original binary normalization isomorphism retains its actual final raw factor. -/
def normalizationIso : (intermediateMap f g).hom.toFunctor ≅ (targetMap f g).hom.toFunctor :=
  isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor (BoundedFlatPerfectBinarySimplex.second f g)

/-- Both original binary pieces compose to the exact target isomorphism of evaluation. -/
theorem normalization_composite :
    (geometricIso f g).hom ≫ (normalizationIso f g).hom =
      (evaluationCompositionTargetIso f g).hom := by
  apply NatTrans.ext
  funext x
  change (BoundedFlatPerfectBinarySimplex.first f g).hom.app _ ≫
    (BoundedFlatPerfectBinarySimplex.second f g).hom.app _ = _
  rw [← NatTrans.comp_app, BoundedFlatPerfectBinarySimplex.small_composite_hom]
  simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id]
  rfl

/-- All five vertices are the original zero-preserving Model arrows. -/
def vertices : Fin 5 → (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  ![sourceMap f g, totalMap f g, intermediateMap f g, cutMap f g, targetMap f g]

/-- Original evaluation and geometric isomorphisms anchor every vertex. -/
def anchors : ∀ i, (sourceMap f g).hom.toFunctor ≅ (vertices f g i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (evaluationComparisonIso (f ≫ g))
    (Fin.cases (evaluationComparisonIso (f ≫ g) ≪≫ geometricIso f g)
      (Fin.cases (evaluationCompositionFirstIso f g)
        (Fin.cases (evaluationComparisonIso (f ≫ g) ≪≫ evaluationCompositionTargetIso f g)
          (fun i => Fin.elim0 i)))))

/-- One actual finite diagram contains all original global composition faces. -/
def simplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) 4 :=
  ModelSimplex.ofIsos (sourceMap f g) (vertices f g) (anchors f g)

/-- The specified ordered triple of vertices in the global evaluation simplex. -/
def triangleFace (i j k : Fin 5) (hij : i ≤ j) (hjk : j ≤ k) : ⦋2⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![i, j, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [le_trans hij hjk]⟩

/-- The first selected face is exactly the original total-evaluation triangle. -/
theorem total_face :
    (simplex f g).face (triangleFace 0 1 4 (by decide) (by decide)) =
      ModelSimplex.triangle (evaluationComparisonIso (f ≫ g)).hom
        (evaluationCompositionTargetIso f g).hom
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The second selected face is exactly the original two-cut evaluation triangle. -/
theorem cut_face :
    (simplex f g).face (triangleFace 0 3 4 (by decide) (by decide)) =
      ModelSimplex.triangle (evaluationCompositionFirstIso f g).hom
        (evaluationCompositionSecondIso f g).hom
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (evaluationComposition_pasting f g).symm

/-- The whole third face is the original binary normalization triangle after evaluation. -/
theorem normalization_face :
    (simplex f g).face (triangleFace 1 2 4 (by decide) (by decide)) =
      (BoundedFlatPerfectBinarySimplex.simplex f g).precomp (evaluationModel (op Z)) := by
  have h : (simplex f g).face (triangleFace 1 2 4 (by decide) (by decide)) =
      ModelSimplex.triangle (geometricIso f g).hom (normalizationIso f g).hom
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
        (fun _ =>
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance) := by
    apply ModelSimplex.ofIsos_face_triangle
    · rfl
    · change ((evaluationComparisonIso (f ≫ g)).hom ≫ (geometricIso f g).hom) ≫
        (normalizationIso f g).hom =
          (evaluationComparisonIso (f ≫ g)).hom ≫ (evaluationCompositionTargetIso f g).hom
      rw [Category.assoc, normalization_composite]
  rw [h, BoundedFlatPerfectBinarySimplex.simplex_eq_triangle, ModelSimplex.triangle_precomp]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSimplex
