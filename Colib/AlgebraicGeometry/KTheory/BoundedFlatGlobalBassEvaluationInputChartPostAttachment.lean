/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference

/-!
# Complete postcomposed chart attachments

The actual chart projection equation transports the original first evaluation comparison.
All five postcomposed chart nodes then agree with their complete mixed descent references.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex

private theorem post_reference_transport
    {V W Z : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {ι : Type v}
    (S : ι → (V ⟶ Z)) (T : ι → (V ⟶ W)) (J : W ⟶ Z)
    (e : ∀ i, (S i).hom.toFunctor ≅ (T i ≫ J).hom.toFunctor) {i j : ι} (h : i = j) :
    eqToIso (congrArg (fun a => (S a).hom.toFunctor) h) ≪≫ e j =
      e i ≪≫ isoWhiskerRight
        (eqToIso (congrArg (fun a => (T a).hom.toFunctor) h)) J.hom.toFunctor := by
  subst j
  simp only [eqToIso_refl, Iso.refl_trans, isoWhiskerRight_refl]
  exact (Iso.trans_refl (e i)).symm

private theorem post_attachment_assoc
    {A B C : Type*} [Category A] [Category B] [Category C]
    {P Q R : A ⥤ B} (J : B ⥤ C) (e : P ≅ Q) (a : Q ≅ R)
    {G H : A ⥤ C} (l : G ≅ H) (m : H ≅ Q ⋙ J) (r : G ≅ P ⋙ J)
    (h : l ≪≫ m = r ≪≫ isoWhiskerRight e J) :
    l ≪≫ (m ≪≫ isoWhiskerRight a J) = r ≪≫ isoWhiskerRight (e ≪≫ a) J := by
  rw [← Iso.trans_assoc, h, isoWhiskerRight_trans, Iso.trans_assoc]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The entire original first comparison is natural under the actual chart equality. -/
theorem post_source_iso :
    chartSourceIso g k hk ≪≫
        evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y) =
      InputMixedDesc.postSourceIso g ≪≫
        isoWhiskerRight
          (eqToIso (congrArg (fun F ↦ F.hom.toFunctor)
            (InputChartSimplex.source_eq Y (k.app Y) (hk Y)).symm))
          (evaluationRawMap (laurent.map g)).hom.toFunctor := by
  exact post_reference_transport
    (fun j : laurent.obj Y ⟶ Y =>
      boundedAboveFlatGlobalSectionModelFunctor.map (laurent.map g ≫ j).op ≫
        evaluationModel (op (laurent.obj X)))
    (fun j : laurent.obj Y ⟶ Y =>
      boundedAboveFlatGlobalSectionModelFunctor.map j.op ≫ evaluationModel (op (laurent.obj Y)))
    (evaluationRawMap (laurent.map g))
    (fun j => evaluationCompositionFirstIso (laurent.map g) j) (hk Y).symm

set_option maxHeartbeats 800000 in
-- The specialized dependent node conversion compares the actual chart attachment functors.
/-- All five original Y nodes have exactly the full attached descent anchors. -/
theorem post_nodes (i : Fin 5) : postNode g k hk i =
    InputMixedDesc.postNode g (InputChartSimplex.chartNodes Y (k.app Y) (hk Y) i) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change chartSourceIso g k hk ≪≫
      (evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y) ≪≫
        isoWhiskerRight (InputSimplex.anchors (k.app Y) (projection.app Y) i)
          (evaluationRawMap (laurent.map g)).hom.toFunctor) =
      InputMixedDesc.postSourceIso g ≪≫
        isoWhiskerRight
          (eqToIso (congrArg (fun F ↦ F.hom.toFunctor)
            (InputChartSimplex.source_eq Y (k.app Y) (hk Y)).symm) ≪≫
              InputSimplex.anchors (k.app Y) (projection.app Y) i)
          (evaluationRawMap (laurent.map g)).hom.toFunctor
  have h := post_attachment_assoc
    (P := (InputChartSimplex.sourceMap Y).hom.toFunctor)
    (Q := (InputSimplex.sourceMap (k.app Y) (projection.app Y)).hom.toFunctor)
    (R := (InputSimplex.vertices (k.app Y) (projection.app Y) i).hom.toFunctor)
    (G := (InputMixedDesc.sourceMap g).hom.toFunctor)
    (H := (InputTripleNodes.sourceMap (laurent.map g) (k.app Y) (projection.app Y)).hom.toFunctor)
    (evaluationRawMap (laurent.map g)).hom.toFunctor
    (eqToIso (congrArg (fun F ↦ F.hom.toFunctor)
      (InputChartSimplex.source_eq Y (k.app Y) (hk Y)).symm))
    (InputSimplex.anchors (k.app Y) (projection.app Y) i)
    (chartSourceIso g k hk)
    (evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y))
    (InputMixedDesc.postSourceIso g) (post_source_iso g k hk)
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
