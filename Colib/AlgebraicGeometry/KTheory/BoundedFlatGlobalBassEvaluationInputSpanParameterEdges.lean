/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterNodes

/-!
# Full evaluation endpoints of the chart-postcomposed projection square

The original evaluation bridges identify the complete projection-square source with the
strict-precomposed chart cut. The original scheme-square equation supplies only equality
transport of the source; the actual evaluation isomorphism is retained and cancelled.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterEdges
open GlobalSectionChangeIndex SmallWaldhausenCategory

attribute [local irreducible] evaluationComparisonIso evaluationCompositionTargetIso

private theorem whisker_transport {V W U₀ U₁ U T : Type*}
    [Category V] [Category W] [Category U₀] [Category U₁] [Category U] [Category T]
    {F G : V ⥤ U} {L : V ⥤ W} {M : W ⥤ U₀} {N : U₀ ⥤ U}
    {E : W ⥤ U₁} {K : U₁ ⥤ U}
    (J : U ⥤ T) (e₁ : F = G) (e₂ : G = (L ⋙ M) ⋙ N)
    (η : M ⋙ N ≅ E ⋙ K) (e : F ⋙ J = L ⋙ ((M ⋙ N) ⋙ J)) :
    (isoWhiskerRight (eqToIso e₁ ≪≫ (eqToIso e₂ ≪≫
      Functor.associator L M N ≪≫ isoWhiskerLeft L η ≪≫
      (Functor.associator L E K).symm)) J).hom =
      eqToHom e ≫ (isoWhiskerLeft L (isoWhiskerRight η J)).hom := by
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, CategoryTheory.Functor.map_comp,
    eqToIso.hom, eqToHom_app, eqToHom_map,
    ← Category.assoc, eqToHom_trans]

private theorem commuting_post_hom {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) {T : WideSubcategory preservesZero.{u + 1}}
    (J : asSmallCategory (boundedAboveFlatPerfectWaldhausen A.toRingedSpace) ⟶ T)
    (e : (InputCommutingSimplex.sourceMap p v ≫ J).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map w.op ≫
        ((boundedAboveFlatGlobalSectionModelFunctor.map q.op ≫
          evaluationModel (op A)) ≫ J)).hom.toFunctor) :
    (isoWhiskerRight (InputCommutingSimplex.sourceIso p v q w h ≪≫
      evaluationCompositionFirstIso q w) J.hom.toFunctor).hom =
      eqToHom e ≫
        (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map w.op).hom.toFunctor
          (isoWhiskerRight (evaluationComparisonIso q) J.hom.toFunctor)).hom := by
  have h' := whisker_transport
    (L := (boundedAboveFlatGlobalSectionModelFunctor.map w.op).hom.toFunctor)
    (M := (boundedAboveFlatGlobalSectionModelFunctor.map q.op).hom.toFunctor)
    (N := (evaluationModel (op A)).hom.toFunctor)
    (E := (evaluationModel (op D)).hom.toFunctor)
    (K := (evaluationRawMap q).hom.toFunctor) J.hom.toFunctor
    (congrArg (fun f ↦ f.hom.toFunctor) (InputCommutingSimplex.source_eq p v q w h))
    (congrArg (fun S ↦ S ⋙ (evaluationModel (op A)).hom.toFunctor)
      (evaluationReindexComp q w)) (evaluationComparisonIso q) e
  exact h'

private theorem pre_cut_bridge {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (InputTripleNodes.preNode f g h 3).2 ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationCompositionSecondIso f g) =
      (InputTripleNodes.preNode f g h 4).2 := by
  change (InputTripleNodes.preSourceIso f g h ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
      (evaluationCompositionFirstIso f g)) ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
      (evaluationCompositionSecondIso f g) =
    InputTripleNodes.preSourceIso f g h ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g) ≪≫ evaluationCompositionTargetIso f g)
  rw [Iso.trans_assoc, ← isoWhiskerLeft_trans]
  exact congrArg (fun e ↦ InputTripleNodes.preSourceIso f g h ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor e)
      (Iso.ext (evaluationComposition_pasting f g).symm)

private theorem twice_reanchor_bridge {C : Type*} [Category C] {A B D E T : C}
    (ρ : A ≅ B) (σ : B ≅ D) (a : D ≅ E) (b : E ≅ T) (c : D ≅ T)
    (h : a ≪≫ b = c) :
    (ρ ≪≫ (σ ≪≫ a)) ≪≫ b = ρ ≪≫ (σ ≪≫ c) := by
  rw [Iso.trans_assoc, Iso.trans_assoc, h]

private theorem pinned_initial {V W T : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (J : W ⟶ T) (R : V ⟶ T) (N : CommonReferenceNerve.Node F)
    (e : R.hom.toFunctor ≅ (N.1 ≫ J).hom.toFunctor) :
    ((e ≪≫ isoWhiskerRight N.2.symm J.hom.toFunctor) ≪≫
      isoWhiskerRight (Iso.refl F.hom.toFunctor) J.hom.toFunctor) ≪≫
        isoWhiskerRight N.2 J.hom.toFunctor = e := by
  rw [isoWhiskerRight_refl, Iso.trans_refl, Iso.trans_assoc,
    ← isoWhiskerRight_trans, Iso.symm_self_id, isoWhiskerRight_refl]
  exact Iso.trans_refl e

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem source_arrow : (InputSpanParameterNodes.nodes g k hk 0).1 =
    (InputChartReference.preNode g k hk 3).1 := by
  change (boundedAboveFlatGlobalSectionModelFunctor.map
    ((polynomial.map g) ≫ projection.app Y).op ≫
    evaluationModel (op (polynomial.obj X))) ≫
      evaluationRawMap (k.app X) =
    boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
      ((boundedAboveFlatGlobalSectionModelFunctor.map (projection.app X).op ≫
      evaluationModel (op (polynomial.obj X))) ≫ evaluationRawMap (k.app X))
  rw [projection.naturality g]
  change (boundedAboveFlatGlobalSectionModelFunctor.map (g.op ≫ (projection.app X).op) ≫
    evaluationModel (op (polynomial.obj X))) ≫
      evaluationRawMap (k.app X) = _
  rw [boundedAboveFlatGlobalSectionModelFunctor.map_comp]
  simp only [Category.assoc]

set_option maxHeartbeats 800000 in
-- Matching the concrete whiskering endpoints reduces the two finite chart nodes.
private def evaluationBridge :
    (InputChartReference.preNode g k hk 3).1.hom.toFunctor ≅
      (InputChartReference.preNode g k hk 4).1.hom.toFunctor := by
  let e := isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
    (evaluationCompositionSecondIso (k.app X) (projection.app X))
  exact e

set_option backward.isDefEq.respectTransparency true in
private theorem chart_bridge :
    (InputChartReference.preNode g k hk 3).2 ≪≫ evaluationBridge g k hk =
      (InputChartReference.preNode g k hk 4).2 := by
  exact twice_reanchor_bridge (InputChartReference.chartSourceIso g k hk)
    (InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputTripleNodes.preNode (k.app X) (projection.app X) g 3).2
    (evaluationBridge g k hk)
    (InputTripleNodes.preNode (k.app X) (projection.app X) g 4).2
    (pre_cut_bridge (k.app X) (projection.app X) g)

private def projectionBridge :
    (InputSpanParameterNodes.nodes g k hk 0).1.hom.toFunctor ≅
      (InputChartReference.preNode g k hk 4).1.hom.toFunctor :=
  isoWhiskerRight (InputSpanParameterNodes.projectionNodes g 6).2
    (evaluationRawMap (k.app X)).hom.toFunctor

set_option backward.isDefEq.respectTransparency true in
private theorem projection_bridge_transport :
    (projectionBridge g k hk).hom =
      eqToHom (congrArg (fun h ↦ h.hom.toFunctor) (source_arrow g k hk)) ≫
        (evaluationBridge g k hk).hom := by
  exact commuting_post_hom (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) (evaluationRawMap (k.app X))
    (congrArg (fun h ↦ h.hom.toFunctor) (source_arrow g k hk))

set_option backward.isDefEq.respectTransparency true in
private theorem projection_bridge :
    (InputSpanParameterNodes.nodes g k hk 0).2 ≪≫ projectionBridge g k hk =
      (InputChartReference.preNode g k hk 4).2 := by
  exact pinned_initial (InputSpanParameterNodes.projectionSource g)
    (evaluationRawMap (k.app X)) (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.projectionNodes g 6) (InputSpanParameterNodes.terminalIso g k hk)

set_option backward.isDefEq.respectTransparency true in
/-- The source is the complete original strict-precomposed chart evaluation cut. -/
theorem projection_pre_source : InputSpanParameterNodes.nodes g k hk 0 =
    InputChartReference.preNode g k hk 3 := by
  apply ModelSimplex.reference_node_eq (congrArg (fun h ↦ h.hom.toFunctor) (source_arrow g k hk))
  change (InputSpanParameterNodes.nodes g k hk 0).2.hom ≫
    eqToHom (congrArg (fun h ↦ h.hom.toFunctor) (source_arrow g k hk)) =
      (InputChartReference.preNode g k hk 3).2.hom
  apply (Iso.cancel_iso_hom_right _ _ (evaluationBridge g k hk)).mp
  calc
    _ = (InputSpanParameterNodes.nodes g k hk 0).2.hom ≫
        (projectionBridge g k hk).hom := by
      rw [projection_bridge_transport, Category.assoc]
    _ = (InputChartReference.preNode g k hk 4).2.hom :=
      congrArg Iso.hom (projection_bridge g k hk)
    _ = (InputChartReference.preNode g k hk 3).2.hom ≫
        (evaluationBridge g k hk).hom :=
      congrArg Iso.hom (chart_bridge g k hk).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterEdges
