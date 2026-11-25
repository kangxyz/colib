/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTriplePreNodes
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNodeTransport

/-!
# Strict association of the original first evaluation cut

Complete dependent nodes agree before carrier realization. The proof retains the original
strict reindexing transports and evaluation comparison at every object.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCutAssociation
open GlobalSectionChangeIndex
attribute [local irreducible] evaluationComparisonIso evaluationCompositionFirstIso

private theorem abstract_cut_reference
    {C₀ C₁ C₂ C₃ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁]
    (H : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃)
    (E : C₃ ⥤ D₁) (V : C₂ ⥤ D₀) (P : D₀ ⥤ D₁)
    (Rfg : C₁ ⥤ C₃) (Rgh : C₀ ⥤ C₂) (T Tleft : C₀ ⥤ C₃)
    (e0 : T = Tleft) (e1 : Tleft = H ⋙ Rfg)
    (e2 : Rfg = G ⋙ F) (e3 : Rgh = H ⋙ G) (e4 : T = Rgh ⋙ F)
    (κ : F ⋙ E ≅ V ⋙ P) :
    ((eqToIso (congrArg (fun K => K ⋙ E) e0) ≪≫
       eqToIso (congrArg (fun K => K ⋙ E) e1) ≪≫
       Functor.associator H Rfg E).hom ≫
      whiskerLeft H ((eqToIso (congrArg (fun K => K ⋙ E) e2) ≪≫
        Functor.associator G F E ≪≫ isoWhiskerLeft G κ ≪≫
        (Functor.associator G V P).symm).hom)) ≫
      eqToHom (congrArg (fun K => (K ⋙ V) ⋙ P) e3.symm) =
    (eqToIso (congrArg (fun K => K ⋙ E) e4) ≪≫
      Functor.associator Rgh F E ≪≫ isoWhiskerLeft Rgh κ ≪≫
      (Functor.associator Rgh V P).symm).hom ≫
      whiskerRight (𝟙 (Rgh ⋙ V)) P := by
  subst Rfg
  subst Rgh
  subst Tleft
  subst T
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, NatTrans.id_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    comp_obj, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem cut_functor_eq {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (InputTripleNodes.preNode f g h 3).1.hom.toFunctor =
      (InputTripleNodes.postNode f g h 0).1.hom.toFunctor :=
  congrArg (fun F => (F ⋙ (evaluationModel (op B)).hom.toFunctor) ⋙
    (evaluationRawMap f).hom.toFunctor) (evaluationReindexComp g h).symm

set_option maxHeartbeats 800000 in
-- Specializing the abstract cut compares two fully composed strict reindexing diagrams.
set_option backward.isDefEq.respectTransparency true in
private theorem cut_reference {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (InputTripleNodes.preNode f g h 3).2.hom ≫ eqToHom (cut_functor_eq f g h) =
      (InputTripleNodes.postNode f g h 0).2.hom := by
  change ((InputTripleNodes.preSourceIso f g h).hom ≫
      whiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationCompositionFirstIso f g).hom) ≫ eqToHom _ =
    (evaluationCompositionFirstIso f (g ≫ h)).hom ≫
      whiskerRight (𝟙 _) (evaluationRawMap f).hom.toFunctor
  unfold InputTripleNodes.preSourceIso evaluationCompositionFirstIso
  have hcut := abstract_cut_reference
    (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
    (evaluationModel (op A)).hom.toFunctor
    (evaluationModel (op B)).hom.toFunctor
    (evaluationRawMap f).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map (g ≫ h).op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g ≫ h).op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map ((f ≫ g) ≫ h).op).hom.toFunctor
    (congrArg (fun k : A ⟶ D => (boundedAboveFlatGlobalSectionModelFunctor.map k.op).hom.toFunctor)
      (Category.assoc f g h).symm)
    (evaluationReindexComp (f ≫ g) h)
    (evaluationReindexComp f g)
    (evaluationReindexComp g h)
    (evaluationReindexComp f (g ≫ h))
    (evaluationComparisonIso f)
  exact hcut


/-- Strict source association preserves the full original first evaluation-cut node. -/
theorem pre_post_source {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    InputTripleNodes.preNode f g h 3 = InputTripleNodes.postNode f g h 0 :=
  ModelSimplex.reference_node_eq (cut_functor_eq f g h) _ _ (cut_reference f g h)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCutAssociation
