/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTripleNodes

/-!
# Full precomposed evaluation nodes in the original raw triple

Strict precomposition of the original evaluation chart retains its original source transport.
Appending the actual evaluation comparison along the final scheme map identifies three
complete dependent nodes with the right binary face of the original raw split triple.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTripleNodes
open GlobalSectionChangeIndex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The strict precomposition reference retains scheme association and original reindexing. -/
def preSourceIso : (sourceMap f g h).hom.toFunctor ≅
    (boundedAboveFlatGlobalSectionModelFunctor.map h.op ≫
      InputSimplex.sourceMap f g).hom.toFunctor :=
  eqToIso (congrArg (fun k : X ⟶ T =>
    (boundedAboveFlatGlobalSectionModelFunctor.map k.op ≫ evaluationModel (op X)).hom.toFunctor)
      (Category.assoc f g h).symm) ≪≫
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op X)).hom.toFunctor)
    (congrArg (fun k ↦ k.hom.toFunctor)
      (boundedAboveFlatGlobalSectionModelFunctor.map_comp h.op (f ≫ g).op))) ≪≫
  Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor
    (evaluationModel (op X)).hom.toFunctor

/-- All five original evaluation-chart nodes after strict precomposition. -/
def preNode (i : Fin 5) : Node f g h :=
  ⟨boundedAboveFlatGlobalSectionModelFunctor.map h.op ≫ InputSimplex.vertices f g i,
    preSourceIso f g h ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (InputSimplex.anchors f g i)⟩

/-- The total node is converted by the actual final evaluation comparison. -/
def preTotalNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫ evaluationRawMap (f ≫ g),
    (preNode f g h 1).2 ≪≫
      isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).hom.toFunctor⟩

/-- The genuine binary intermediate is converted by the same actual evaluation comparison. -/
def preIntermediateNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫
      BoundedFlatPerfectBinarySimplex.intermediateMap f g,
    (preNode f g h 2).2 ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor⟩

/-- The split target retains the original raw suffix in its final evaluation bridge. -/
def preTargetNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫ (evaluationRawMap g ≫ evaluationRawMap f),
    (preNode f g h 4).2 ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (evaluationRawMap g ≫ evaluationRawMap f).hom.toFunctor⟩

private theorem comparison_transport {A B : Scheme.{u}} {a b : A ⟶ B} (e : a = b) :
    eqToHom (congrArg (fun k : A ⟶ B =>
      (boundedAboveFlatGlobalSectionModelFunctor.map k.op ≫
        evaluationModel (op A)).hom.toFunctor) e) ≫
      (evaluationComparisonIso b).hom =
    (evaluationComparisonIso a).hom ≫
      whiskerLeft (evaluationModel (op B)).hom.toFunctor
        (eqToHom (congrArg (fun k : A ⟶ B => (evaluationRawMap k).hom.toFunctor) e)) := by
  subst b
  apply NatTrans.ext
  funext x
  change (𝟙 _ ≫ (evaluationComparisonIso a).hom.app x) =
    ((evaluationComparisonIso a).hom.app x ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

private theorem right_reference : BoundedFlatPerfectTripleSimplex.rightFirst f g h =
    eqToIso (congrArg (fun k : X ⟶ T => (evaluationRawMap k).hom.toFunctor)
      (Category.assoc f g h).symm) ≪≫ evaluationRawCompIso (f ≫ g) h := by
  rw [evaluationRawCompIso_eq_asSmall]
  unfold BoundedFlatPerfectTripleSimplex.rightFirst asSmallCompositionIso
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem pre_first_anchor :
    (preSourceIso f g h).hom ≫
      (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g))).hom =
    eqToHom (congrArg (fun k : X ⟶ T =>
      (boundedAboveFlatGlobalSectionModelFunctor.map k.op ≫ evaluationModel (op X)).hom.toFunctor)
        (Category.assoc f g h).symm) ≫
      (evaluationCompositionFirstIso (f ≫ g) h).hom := by
  apply NatTrans.ext
  funext x
  simp only [preSourceIso, evaluationCompositionFirstIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, comp_obj,
    Category.id_comp, Category.assoc]
  erw [Category.comp_id]

private theorem pre_total_anchor :
    ((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g))).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).hom.toFunctor).hom =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).hom.toFunctor
        (BoundedFlatPerfectTripleSimplex.rightFirst f g h)).hom := by
  rw [pre_first_anchor, Category.assoc]
  change _ ≫ ((evaluationCompositionFirstIso (f ≫ g) h).hom ≫
    (evaluationCompositionSecondIso (f ≫ g) h).hom) = _
  rw [← evaluationComposition_pasting, ← Category.assoc,
    comparison_transport (Category.assoc f g h).symm]
  rw [right_reference]
  apply NatTrans.ext
  funext x
  simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, eqToIso.hom,
    Functor.associator_inv_app, Category.comp_id, Category.assoc]

/-- The full converted total node is the original right normalized triple node. -/
theorem pre_total_node : preTotalNode f g h = rawNode f g h 5 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  exact pre_total_anchor f g h

set_option maxHeartbeats 1200000 in
-- The componentwise naturality equality compares three concrete normalized pullback models.
private theorem pre_conversion_anchor
    (F : asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
    (α : (evaluationRawMap (f ≫ g)).hom.toFunctor ≅ F.hom.toFunctor) :
    ((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g) ≪≫
          isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor α)).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) F.hom.toFunctor).hom =
    (((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g))).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).hom.toFunctor).hom) ≫
      (isoWhiskerLeft (evaluationModel (op T) ≫ evaluationRawMap h).hom.toFunctor α).hom := by
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc]
  erw [← α.hom.naturality ((evaluationComparisonIso h).hom.app x)]

/-- The full converted intermediate node is the original right geometric split node. -/
theorem pre_intermediate_node : preIntermediateNode f g h = rawNode f g h 6 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
      (evaluationComparisonIso (f ≫ g) ≪≫
        isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor
          (BoundedFlatPerfectBinarySimplex.first f g))).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h)
      (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor).hom) = _
  rw [pre_conversion_anchor, pre_total_anchor]
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, Category.assoc]
  rfl

/-- The full converted split target retains the raw triple's original left reference route. -/
theorem pre_target_node : preTargetNode f g h = rawNode f g h 7 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
      (evaluationComparisonIso (f ≫ g) ≪≫ evaluationCompositionTargetIso f g)).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h)
      (evaluationRawMap g ≫ evaluationRawMap f).hom.toFunctor).hom) = _
  have hs : (evaluationCompositionTargetIso f g).hom =
      (isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor (evaluationRawCompIso f g)).hom := by
    apply NatTrans.ext
    funext x
    simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
  have hi : evaluationCompositionTargetIso f g =
      isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor (evaluationRawCompIso f g) := Iso.ext hs
  rw [hi]
  trans (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
      (evaluationComparisonIso (f ≫ g))).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).hom.toFunctor).hom) ≫
    (isoWhiskerLeft (evaluationModel (op T) ≫ evaluationRawMap h).hom.toFunctor
      (evaluationRawCompIso f g)).hom
  · exact pre_conversion_anchor f g h (evaluationRawMap g ≫ evaluationRawMap f)
      (evaluationRawCompIso f g)
  rw [pre_total_anchor]
  change ((evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
    (isoWhiskerLeft (evaluationModel (op T)).hom.toFunctor
      (BoundedFlatPerfectTripleSimplex.rightFirst f g h)).hom) ≫ _ =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).hom.toFunctor
        (BoundedFlatPerfectTripleSimplex.leftFirst f g h ≪≫
          BoundedFlatPerfectTripleSimplex.leftSecond f g h)).hom
  have hr := congrArg (whiskerLeft (evaluationModel (op T)).hom.toFunctor)
    (BoundedFlatPerfectTripleSimplex.two_routes f g h)
  rw [whiskerLeft_comp, whiskerLeft_comp] at hr
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_comp, Category.assoc]
  rw [hr]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTripleNodes
