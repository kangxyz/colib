/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartSquareParameter
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartParameters
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartSourceNode
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCutAssociation

/-!
# Complete original chart-edge nodes in the mixed reference

The source and target evaluation edges of the attached commuting square are compared as
complete Model arrows with their original reference isomorphisms, before scalar realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartFaceNodes
open GlobalSectionChangeIndex

attribute [local irreducible] evaluationComparisonIso evaluationCompositionFirstIso
  evaluationCompositionTargetIso

private theorem associator_eqToIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    Functor.associator F G H = eqToIso (Functor.assoc F G H) := rfl

private theorem whisker_eqToIso {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F : A ⥤ B) {G H : B ⥤ C} (e : G = H) :
    isoWhiskerLeft F (eqToIso e) = eqToIso (congrArg (fun K => F ⋙ K) e) := by
  cases e
  rfl

/-- Strict source association preserves the full original first evaluation-cut node. -/
theorem pre_post_source {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    InputTripleNodes.preNode f g h 3 = InputTripleNodes.postNode f g h 0 :=
  InputCutAssociation.pre_post_source f g h

private theorem post_cut_anchor {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (InputTripleNodes.postNode f g h 3).2 ≪≫
      isoWhiskerRight (evaluationComparisonIso h)
        (evaluationRawMap g ≫ evaluationRawMap f).hom.toFunctor =
      (InputTripleNodes.postNode f g h 4).2 := by
  apply Iso.ext
  change ((evaluationCompositionFirstIso f (g ≫ h)).hom ≫
      whiskerRight (evaluationCompositionFirstIso g h).hom (evaluationRawMap f).hom.toFunctor) ≫
      whiskerRight (evaluationCompositionSecondIso g h).hom (evaluationRawMap f).hom.toFunctor =
    (evaluationCompositionFirstIso f (g ≫ h)).hom ≫
      whiskerRight ((evaluationComparisonIso (g ≫ h)).hom ≫
        (evaluationCompositionTargetIso g h).hom) (evaluationRawMap f).hom.toFunctor
  exact (Category.assoc _ _ _).trans
    (congrArg ((evaluationCompositionFirstIso f (g ≫ h)).hom ≫ ·)
      ((whiskerRight_comp _ _ _).symm.trans
        (congrArg (fun a => whiskerRight a (evaluationRawMap f).hom.toFunctor)
          (evaluationComposition_pasting g h).symm)))

/-- The two original evaluation-cut routes have the same complete target reference. -/
theorem pre_post_target {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    InputTripleNodes.preNode f g h 4 = InputTripleNodes.postNode f g h 3 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  have he := (InputTripleNodes.pre_target_node f g h).trans
    (InputTripleNodes.post_target_node f g h).symm
  have ht : (InputTripleNodes.preTargetNode f g h).2 =
      (InputTripleNodes.postNode f g h 4).2 := eq_of_heq (Sigma.mk.inj he).2
  apply (Iso.cancel_iso_hom_right _ _
    (isoWhiskerRight (evaluationComparisonIso h)
      (evaluationRawMap g ≫ evaluationRawMap f).hom.toFunctor)).mp
  exact congrArg Iso.hom (ht.trans (post_cut_anchor f g h).symm)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- Each attached first chart node retains the complete original triple precomposition. -/
theorem first_nodes (i : Fin 5) :
    InputChartSquareParameter.nodes g k hk (InputCommutingSimplex.firstFace.toOrderHom i) =
      ModelSimplex.reanchorNodes (InputChartReference.chartSourceIso g k hk)
        (InputTripleNodes.preNode (laurent.map g) (k.app Y) (projection.app Y)) i := by
  unfold InputChartSquareParameter.nodes
  rw [InputCommutingSimplex.first_nodes]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact Iso.trans_assoc _ _ _

/-- The attached target evaluation begins at the full original postcomposed source node. -/
theorem post_source_node :
    InputChartSquareParameter.nodes g k hk 3 = InputChartReference.postNode g k hk 0 :=
  (first_nodes g k hk 3).trans
    (congrArg (fun N => ModelSimplex.reanchorNodes
      (InputChartReference.chartSourceIso g k hk) (fun _ : Fin 1 => N) 0)
      (pre_post_source (laurent.map g) (k.app Y) (projection.app Y)))

/-- The attached target evaluation ends at the unchanged postcomposed evaluation cut. -/
theorem post_target_node :
    InputChartSquareParameter.nodes g k hk 4 = InputChartReference.postNode g k hk 3 :=
  (first_nodes g k hk 4).trans
    (congrArg (fun N => ModelSimplex.reanchorNodes
      (InputChartReference.chartSourceIso g k hk) (fun _ : Fin 1 => N) 0)
      (pre_post_target (laurent.map g) (k.app Y) (projection.app Y)))

private theorem cut_transport {A B C C' D : Scheme.{u}}
    (f : A ⟶ B) (v : B ⟶ C) (h : C ⟶ D) (v' : B ⟶ C') (h' : C' ⟶ D)
    (e : v ≫ h = v' ≫ h')
    (S : boundedAboveFlatGlobalSectionModelFunctor.obj (op D) ⟶ asSmallCategory
      (boundedAboveFlatPerfectWaldhausen A.toRingedSpace))
    (e₀ : S.hom.toFunctor = (InputTripleNodes.sourceMap f v h).hom.toFunctor)
    (e₁ : S.hom.toFunctor = (InputTripleNodes.sourceMap f v' h').hom.toFunctor) :
    ModelSimplex.reanchorNodes (eqToIso e₀) (InputTripleNodes.preNode f v h) 3 =
      ModelSimplex.reanchorNodes (eqToIso e₁) (InputTripleNodes.preNode f v' h') 3 := by
  change (⟨(InputTripleNodes.preNode f v h 3).1,
    eqToIso e₀ ≪≫ (InputTripleNodes.preNode f v h 3).2⟩ : CommonReferenceNerve.Node S) =
    ⟨(InputTripleNodes.preNode f v' h' 3).1,
      eqToIso e₁ ≪≫ (InputTripleNodes.preNode f v' h' 3).2⟩
  rw [pre_post_source, pre_post_source]
  change (⟨InputSimplex.sourceMap v h ≫ evaluationRawMap f,
    eqToIso e₀ ≪≫ (evaluationCompositionFirstIso f (v ≫ h) ≪≫
      isoWhiskerRight (Iso.refl _) (evaluationRawMap f).hom.toFunctor)⟩ :
        CommonReferenceNerve.Node S) =
    ⟨InputSimplex.sourceMap v' h' ≫ evaluationRawMap f,
      eqToIso e₁ ≪≫ (evaluationCompositionFirstIso f (v' ≫ h') ≪≫
        isoWhiskerRight (Iso.refl _) (evaluationRawMap f).hom.toFunctor)⟩
  simp only [isoWhiskerRight_refl]
  exact ModelSimplex.transportedReferenceNode_congr S
    (fun t : B ⟶ D => boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ t).op ≫
      evaluationModel (op A))
    (fun t : B ⟶ D => (boundedAboveFlatGlobalSectionModelFunctor.map t.op ≫
      evaluationModel (op B)) ≫ evaluationRawMap f)
    (fun t => evaluationCompositionFirstIso f t) e e₀ e₁

include hk in
private theorem secondSourceEq : (InputMixedDesc.sourceMap g).hom.toFunctor =
    (InputTripleNodes.sourceMap (k.app X) (polynomial.map g) (projection.app Y)).hom.toFunctor := by
  apply congrArg (fun t : laurent.obj X ⟶ Y =>
    (boundedAboveFlatGlobalSectionModelFunctor.map t.op ≫
      evaluationModel (op (laurent.obj X))).hom.toFunctor)
  rw [← hk Y, ← Category.assoc, k.naturality g, Category.assoc]

include hk in
private theorem lastSourceEq : (InputMixedDesc.sourceMap g).hom.toFunctor =
    (InputTripleNodes.sourceMap (k.app X) (projection.app X) g).hom.toFunctor := by
  apply congrArg (fun t : laurent.obj X ⟶ Y =>
    (boundedAboveFlatGlobalSectionModelFunctor.map t.op ≫
      evaluationModel (op (laurent.obj X))).hom.toFunctor)
  rw [← hk Y, ← Category.assoc, k.naturality g, Category.assoc, projection.naturality g]
  rfl

/-- Every second-chart node keeps the actual square transport before strict projection. -/
private theorem second_nodes (i : Fin 5) :
    InputChartSquareParameter.nodes g k hk (InputCommutingSimplex.secondFace.toOrderHom i) =
      ModelSimplex.reanchorNodes (eqToIso (secondSourceEq g k hk))
        (InputTripleNodes.preNode (k.app X) (polynomial.map g) (projection.app Y)) i := by
  unfold InputChartSquareParameter.nodes
  rw [InputCommutingSimplex.second_nodes]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change (InputChartSquareParameter.sourceIso g k hk) ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map
      (projection.app Y).op).hom.toFunctor
      (InputCommutingSimplex.sourceIso (laurent.map g) (k.app Y)
        (k.app X) (polynomial.map g) (k.naturality g) ≪≫
        InputSimplex.anchors (k.app X) (polynomial.map g) i) = _
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc]
  have h : InputChartSquareParameter.sourceIso g k hk ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map
        (projection.app Y).op).hom.toFunctor
        (InputCommutingSimplex.sourceIso (laurent.map g) (k.app Y)
          (k.app X) (polynomial.map g) (k.naturality g)) =
    eqToIso (secondSourceEq g k hk) ≪≫
      InputTripleNodes.preSourceIso (k.app X) (polynomial.map g) (projection.app Y) := by
    simp only [InputChartSquareParameter.sourceIso, InputChartReference.chartSourceIso,
      InputTripleNodes.preSourceIso, InputCommutingSimplex.sourceIso,
      associator_eqToIso, whisker_eqToIso, eqToIso_trans]
  rw [h, Iso.trans_assoc]
  rfl

private theorem last_nodes (i : Fin 5) :
    InputChartReference.preNode g k hk i =
      ModelSimplex.reanchorNodes (eqToIso (lastSourceEq g k hk))
        (InputTripleNodes.preNode (k.app X) (projection.app X) g) i := by
  have h : InputChartReference.chartSourceIso g k hk ≪≫
      InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g) = eqToIso (lastSourceEq g k hk) := by
    simp only [InputChartReference.chartSourceIso, InputRectangleNodes.lastSourceIso,
      eqToIso_trans]
  exact (ModelSimplex.reanchorNode_assoc (InputChartReference.chartSourceIso g k hk)
    (InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputTripleNodes.preNode (k.app X) (projection.app X) g i)).trans
      (congrArg (fun e => ModelSimplex.reanchorNode e
        (InputTripleNodes.preNode (k.app X) (projection.app X) g i)) h)

/-- The initial chart node is the actual mixed source with its complete identity anchor. -/
theorem source_node :
    InputChartSquareParameter.nodes g k hk 0 =
      (⟨InputMixedDesc.sourceMap g, Iso.refl _⟩ : InputChartReference.Node g) :=
  InputChartSourceNode.source_node g k hk

/-- The original X chart has the same complete strict-source reference. -/
theorem pre_source_node :
    InputChartSquareParameter.nodes g k hk 0 = InputChartReference.preNode g k hk 0 :=
  InputChartSourceNode.pre_source_node g k hk

/-- Strict polynomial naturality identifies the full original X evaluation-cut node. -/
theorem pre_target_node :
    InputChartSquareParameter.nodes g k hk 6 = InputChartReference.preNode g k hk 3 := by
  change InputChartSquareParameter.nodes g k hk
    (InputCommutingSimplex.secondFace.toOrderHom 3) = _
  rw [second_nodes, last_nodes]
  exact cut_transport (k.app X) (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) (InputMixedDesc.sourceMap g) _ _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartFaceNodes
