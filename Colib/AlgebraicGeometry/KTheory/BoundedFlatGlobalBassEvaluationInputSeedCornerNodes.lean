/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedUnitNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawDesc
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPrism
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPreAttachment

/-!
# Complete corner joins of the original mixed evaluation seed

The Laurent square's original postcomposition, strict-precomposition, and raw target corners
are the complete positive-chart nodes. Each equality retains the zero-preserving Model arrow
and the full original anchor, including the actual scheme-square and strict composition
transports. The two strict-precomposition corners also meet their original prism columns.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedCornerNodes
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem functorAssoc {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) := rfl

private theorem reassociate_node
    {V W T U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (J : V ⟶ W) (E : W ⟶ T) (R : T ⟶ U) (F : V ⟶ U)
    (a : F.hom.toFunctor ≅ (J ≫ (E ≫ R)).hom.toFunctor) :
    (⟨(J ≫ E) ≫ R,
      a ≪≫ (Functor.associator J.hom.toFunctor E.hom.toFunctor R.hom.toFunctor).symm⟩ : Node F) =
      ⟨J ≫ (E ≫ R), a⟩ := by
  apply ModelSimplex.reference_node_eq (functorAssoc J.hom.toFunctor E.hom.toFunctor
    R.hom.toFunctor)
  change (a.hom ≫ (Functor.associator J.hom.toFunctor E.hom.toFunctor R.hom.toFunctor).inv) ≫
    (Functor.associator J.hom.toFunctor E.hom.toFunctor R.hom.toFunctor).hom = a.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem reassociate_anchor
    {V W T U Z : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (J : V ⟶ W) (K : W ⟶ T) (E : T ⟶ U) (D : W ⟶ Z) (R : Z ⟶ U)
    (F M : V ⟶ U) (a : F.hom.toFunctor ≅ M.hom.toFunctor)
    (b : M.hom.toFunctor ≅ ((J ≫ K) ≫ E).hom.toFunctor)
    (i : (K ≫ E).hom.toFunctor ≅ (D ≫ R).hom.toFunctor)
    (p : F.hom.toFunctor ≅ (J ≫ (K ≫ E)).hom.toFunctor)
    (q : M.hom.toFunctor ≅ ((J ≫ D) ≫ R).hom.toFunctor)
    (hp : p = a ≪≫ b ≪≫ Functor.associator J.hom.toFunctor K.hom.toFunctor E.hom.toFunctor)
    (hq : q = b ≪≫ Functor.associator J.hom.toFunctor K.hom.toFunctor E.hom.toFunctor ≪≫
      isoWhiskerLeft J.hom.toFunctor i ≪≫
        (Functor.associator J.hom.toFunctor D.hom.toFunctor R.hom.toFunctor).symm) :
    a ≪≫ q = (p ≪≫ isoWhiskerLeft J.hom.toFunctor i) ≪≫
      (Functor.associator J.hom.toFunctor D.hom.toFunctor R.hom.toFunctor).symm := by
  rw [hp, hq]
  simp only [Iso.trans_assoc]

private theorem source_transport {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C) (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.sourceIso p v q w h =
      eqToIso (congrArg (fun k : A ⟶ C =>
        (boundedAboveFlatGlobalSectionModelFunctor.map k.op ≫ evaluationModel
          (op A)).hom.toFunctor) h) := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem pre_source_anchor :
    InputMixedDesc.preSourceIso g =
      InputCommutingSimplex.sourceIso (laurent.map g)
          (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
          (GlobalRawBass.laurentProjection.naturality g) ≪≫
        eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).hom.toFunctor)
          (evaluationReindexComp (GlobalRawBass.laurentProjection.app X) g)) ≪≫
        Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
          (boundedAboveFlatGlobalSectionModelFunctor.map
            (GlobalRawBass.laurentProjection.app X).op).hom.toFunctor
          (evaluationModel (op (laurent.obj X))).hom.toFunctor := by
  unfold InputMixedDesc.preSourceIso
  rw [source_transport]

private theorem raw_shared (i : Fin 5) :
    GlobalRawBass.InputDescSimplex.chartNodes g plus GlobalRawBass.plus_projection
      (BoundedFlatPerfectProjectionReference.sharedIndex i) =
      BoundedFlatPerfectNativeSquareFiveSimplex.nodes (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) i :=
  (BoundedFlatPerfectProjectionReference.shared_nodes (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (plus.naturality g)
    (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X)
    (GlobalRawBass.plus_projection Y) (GlobalRawBass.plus_projection X) i).trans
      (show BoundedFlatPerfectProjectionReference.sharedNodes (projection.app Y) (plus.app Y)
          (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
          (projection.naturality g) (plus.naturality g)
          (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X)
          (GlobalRawBass.plus_projection Y) (GlobalRawBass.plus_projection X) i = _ from rfl)

/-- All five raw square nodes meet their original complete positive-chart rectangle nodes. -/
theorem raw_nodes (i : Fin 5) :
    InputSeedUnitNodes.lower g (InputSeedUnitNodes.rawIndex i) =
      InputChartReference.rawNode g plus GlobalRawBass.plus_projection
        (BoundedFlatPerfectProjectionReference.sharedIndex i) := by
  exact (InputSeedUnitNodes.raw_lower_nodes g i).trans
    ((congrArg (InputRawDesc.evaluateNode g) (raw_shared g i).symm).trans
      (InputRawDesc.chart_node g plus GlobalRawBass.plus_projection
        (BoundedFlatPerfectProjectionReference.sharedIndex i)).symm)

/-- The first raw target is the original postcomposed total corner, with its full anchor. -/
theorem post_total : InputSeedUnitNodes.lower g 4 =
    InputChartReference.postNode g plus GlobalRawBass.plus_projection 1 :=
  (raw_nodes g 2).trans
    (InputChartReference.post_total_node g plus GlobalRawBass.plus_projection).symm

/-- The postcomposed total corner is also the unchanged original raw rectangle node two. -/
theorem post_raw : InputSeedUnitNodes.lower g 4 =
    InputChartReference.rawNode g plus GlobalRawBass.plus_projection 2 :=
  raw_nodes g 2

private theorem composition_first_explicit {A B C : Scheme.{u}} (f : A ⟶ B) (h : B ⟶ C) :
    evaluationCompositionFirstIso f h =
      eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op A)).hom.toFunctor)
        (evaluationReindexComp f h)) ≪≫
      Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
        (evaluationModel (op A)).hom.toFunctor ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso f) ≪≫
      (Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationModel (op B)).hom.toFunctor (evaluationRawMap f).hom.toFunctor).symm := rfl

set_option maxHeartbeats 400000 in
-- Comparing the fixed Model-arrow and functor presentations of this anchor is conversion-heavy.
private theorem pre_total_anchor :
    InputCommutingSimplex.sourceIso (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) ≪≫
      evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g =
    (InputMixedDesc.preSourceIso g ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
        (evaluationComparisonIso (GlobalRawBass.laurentProjection.app X))) ≪≫
      (Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
        (evaluationModel (op X)).hom.toFunctor
        (evaluationRawMap (GlobalRawBass.laurentProjection.app X)).hom.toFunctor).symm := by
  refine reassociate_anchor
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
      (boundedAboveFlatGlobalSectionModelFunctor.map (GlobalRawBass.laurentProjection.app X).op)
    (evaluationModel (op (laurent.obj X))) (evaluationModel (op X))
    (evaluationRawMap (GlobalRawBass.laurentProjection.app X))
    (InputMixedDesc.sourceMap g)
    (InputSimplex.sourceMap (GlobalRawBass.laurentProjection.app X) g)
    (InputCommutingSimplex.sourceIso (laurent.map g)
      (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g))
    (eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).hom.toFunctor)
      (evaluationReindexComp (GlobalRawBass.laurentProjection.app X) g)))
    (evaluationComparisonIso (GlobalRawBass.laurentProjection.app X))
    (InputMixedDesc.preSourceIso g)
    (evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g) ?_ ?_
  · exact pre_source_anchor g
  · exact composition_first_explicit (GlobalRawBass.laurentProjection.app X) g

/-- The second Laurent cut is the actual strict-precomposed X total evaluation corner. -/
theorem pre_total : InputSeedUnitNodes.lower g 6 =
    InputChartReference.preNode g plus GlobalRawBass.plus_projection 1 := by
  rw [InputChartReference.pre_nodes, InputChartSimplex.chartNodes_one]
  change (⟨((boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op X)) ≫
      evaluationRawMap (GlobalRawBass.laurentProjection.app X)),
    InputCommutingSimplex.sourceIso (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) ≪≫
      evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g⟩ :
        Node (InputSeedCarrier.laurentRef g)) = _
  rw [pre_total_anchor]
  exact reassociate_node (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (evaluationModel (op X))
    (evaluationRawMap (GlobalRawBass.laurentProjection.app X))
    (InputSeedCarrier.laurentRef g) _

/-- The strict-precomposed total corner is precisely the original prism source. -/
theorem pre_prism : InputSeedUnitNodes.lower g 6 =
    InputChartReference.prismNode g plus GlobalRawBass.plus_projection 0 :=
  (pre_total g).trans
    (InputChartReference.prism_pre_nodes g plus GlobalRawBass.plus_projection 0).symm

/-- The second raw target is the complete original rectangle node fifteen. -/
theorem target_raw : InputSeedUnitNodes.lower g 7 =
    InputChartReference.rawNode g plus GlobalRawBass.plus_projection 15 :=
  raw_nodes g 4

/-- The raw target is precisely the original converted prism source. -/
theorem target_prism : InputSeedUnitNodes.lower g 7 =
    InputChartReference.prismNode g plus GlobalRawBass.plus_projection 3 :=
  (target_raw g).trans
    (InputChartReference.prism_raw_nodes g plus GlobalRawBass.plus_projection 0).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedCornerNodes
