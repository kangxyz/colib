/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictAttachment

/-!
# The original source node of the strict evaluation seed carrier

The source attachment is fixed by the actual scheme square and strict reindexing. Cancelling
its original evaluation comparison identifies the complete polynomial source node before
realization, rather than cancelling the positive chart map after realization.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictNodes
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedStrictAttachment

private theorem globalReindex_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor :=
  congrArg (fun k ↦ k.hom.toFunctor)
    (boundedAboveFlatGlobalSectionModelFunctor.map_comp g.op f.op)

private theorem cancel_source_transport
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (P : A ⥤ B) (Q : B ⥤ C) (R : C ⥤ E) (U : B ⥤ D) (V : D ⥤ E)
    (S : A ⥤ C) (F : A ⥤ E) (h₁ : F = S ⋙ R) (h₂ : S = P ⋙ Q)
    (e : Q ⋙ R ≅ U ⋙ V) (h : F = P ⋙ (Q ⋙ R)) :
    (eqToIso h₁ ≪≫ eqToIso (congrArg (fun K ↦ K ⋙ R) h₂) ≪≫
      Functor.associator P Q R ≪≫ isoWhiskerLeft P e ≪≫
        (Functor.associator P U V).symm) ≪≫
      Functor.associator P U V ≪≫ (isoWhiskerLeft P e).symm = eqToIso h := by
  subst F
  subst S
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]
  change eqToIso _ ≪≫ eqToIso _ ≪≫ eqToIso (Functor.assoc P Q R) = eqToIso h
  simp only [eqToIso_trans]

private theorem source_node {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  (P : V ⟶ W) (R : W ⟶ T)
    (F : V ⟶ T) (h : F = P ≫ R) :
    attachPrecompNode R P F (eqToIso (congrArg (fun k ↦ k.hom.toFunctor) h))
      (⟨R, Iso.refl _⟩ : Node R) = (⟨F, Iso.refl _⟩ : Node F) := by
  subst F
  change (⟨P ≫ R, Iso.refl _ ≪≫ isoWhiskerLeft P.hom.toFunctor (Iso.refl _)⟩ :
    Node (P ≫ R)) = _
  rw [isoWhiskerLeft_refl, Iso.refl_trans]
  rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual projection square and strict reindexing identify the complete source arrow. -/
theorem source_eq : InputSeedCarrier.polyRef g =
    boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ InputSeedEvaluationCarrier.polyRef X := by
  change boundedAboveFlatGlobalSectionModelFunctor.map ((polynomial.map g) ≫ projection.app Y).op ≫
    evaluationModel (op (polynomial.obj X)) = _
  rw [projection.naturality g]
  change boundedAboveFlatGlobalSectionModelFunctor.map ((projection.app X) ≫ g).op ≫
    evaluationModel (op (polynomial.obj X)) = _
  simp only [op_comp, Functor.map_comp, Category.assoc]

private theorem sixth_anchor {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C) (h : p ≫ v = q ≫ w) :
    (InputCommutingSimplex.nodes p v q w h 6).2 =
      InputCommutingSimplex.sourceIso p v q w h ≪≫ evaluationCompositionFirstIso q w := rfl

attribute [local irreducible] evaluationComparisonIso boundedAboveFlatGlobalSectionModelFunctor
attribute [local irreducible] evaluationModel evaluationRawMap

set_option backward.isDefEq.respectTransparency true in
/-- Cancelling the unchanged comparison leaves the exact strict source transport. -/
theorem source_iso : polynomialSourceIso g =
    eqToIso (congrArg (fun k ↦ k.hom.toFunctor) (source_eq g)) := by
  unfold polynomialSourceIso InputSpanParameterNodes.projectionNodes
  rw [sixth_anchor]
  unfold evaluationCompositionFirstIso InputCommutingSimplex.sourceIso
  simp only [Functor.id_obj]
  exact cancel_source_transport _ _ _ _ _ _ _ _
    (globalReindex_comp (projection.app X) g) _ _

/-- The entire initial polynomial node is the original projection-square source node. -/
theorem polynomial_zero :
    polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes X 0) =
      InputSpanParameterNodes.projectionNodes g 0 := by
  rw [InputSeedEvaluationCarrier.polynomialNodes_zero]
  change attachPrecompNode _ _ _ (polynomialSourceIso g) _ = _
  rw [source_iso]
  exact source_node (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputSeedEvaluationCarrier.polyRef X)
    (InputSeedCarrier.polyRef g) (source_eq g)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictNodes
