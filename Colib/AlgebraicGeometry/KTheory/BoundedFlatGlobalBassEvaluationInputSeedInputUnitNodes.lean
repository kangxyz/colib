/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedUnitNodes

/-! Full anchored corners of the original strict-unit times Laurent evaluation product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputUnitNodes
open GlobalSectionChangeIndex InputNormalizationPrism CommonReferenceNerve
open InputSeedInputUnitProduct

private theorem functorAssoc {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) := rfl

private theorem pair_iso
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {F₀ F₁ : V ⟶ W}
      {G₀ G₁ : W ⟶ T}
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso (e.prod d) =
      isoWhiskerRight e G₀.hom.toFunctor ≪≫ isoWhiskerLeft F₁.hom.toFunctor d := by
  apply Iso.ext
  rfl

private theorem source_shift_node
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (R : V ⟶ T)
    (H : V ⟶ W) (G₀ G₁ : W ⟶ T) (η : R.hom.toFunctor ≅ (H ≫ G₀).hom.toFunctor)
    (ρ : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) (α : H.hom.toFunctor ≅ H.hom.toFunctor)
    (τ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : τ ≪≫ η = η ≪≫ isoWhiskerRight α G₀.hom.toFunctor) :
    (⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
      (α.prod ρ)⟩ : Node R) =
    ModelSimplex.reanchorNode τ
      ⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
        ((Iso.refl _).prod ρ)⟩ := by
  apply congrArg (fun θ ↦ (⟨H ≫ G₁, θ⟩ : Node R))
  rw [pair_iso, pair_iso]
  simp only [isoWhiskerRight_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc]

private theorem identity_anchor_node
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F G : V ⟶ W)
    (h : F.hom.toFunctor = G.hom.toFunctor) :
    (⟨G, eqToIso h⟩ : Node F) = ⟨F, Iso.refl _⟩ := by
  apply ModelSimplex.reference_node_eq h.symm
  change eqToHom h ≫ eqToHom h.symm = 𝟙 _
  rw [eqToHom_trans, eqToHom_refl]

private theorem preserves_comp
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W) (G : W ⟶ T)
    (α : 𝟭 V.obj.Obj ≅ 𝟭 V.obj.Obj) (β : 𝟭 W.obj.Obj ≅ 𝟭 W.obj.Obj)
    (γ : 𝟭 T.obj.Obj ≅ 𝟭 T.obj.Obj)
    (hF : Preserves F.hom.toFunctor α β) (hG : Preserves G.hom.toFunctor β γ) :
    Preserves (F ≫ G).hom.toFunctor α γ := fun A ↦
  (congrArg G.hom.toFunctor.map (hF A)).trans (hG (F.hom.toFunctor.obj A))

private theorem preserved_onFunctor
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W) (G : W ⟶ T)
    (α : 𝟭 W.obj.Obj ≅ 𝟭 W.obj.Obj) (β : 𝟭 T.obj.Obj ≅ 𝟭 T.obj.Obj)
    (h : Preserves G.hom.toFunctor α β) :
    isoWhiskerRight (onFunctor F.hom.toFunctor α) G.hom.toFunctor =
      onFunctor (F ≫ G).hom.toFunctor β := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact h (F.hom.toFunctor.obj A)

private theorem reassociate_node
    {V W T U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (R : V ⟶ U)
    (H : V ⟶ W) (E : W ⟶ T) (D : T ⟶ U)
    (ρ : R.hom.toFunctor ≅ (H ≫ (E ≫ D)).hom.toFunctor)
    (τ : R.hom.toFunctor ≅ ((H ≫ E) ≫ D).hom.toFunctor)
    (h : ρ ≪≫ (Functor.associator H.hom.toFunctor E.hom.toFunctor D.hom.toFunctor).symm = τ) :
    (⟨H ≫ (E ≫ D), ρ⟩ : Node R) = ⟨(H ≫ E) ≫ D, τ⟩ := by
  apply ModelSimplex.reference_node_eq
    (functorAssoc H.hom.toFunctor E.hom.toFunctor D.hom.toFunctor).symm
  exact congrArg Iso.hom h

private theorem original_anchor_word
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (R : A ⥤ D) (H : A ⥤ B) (F : B ⥤ C) (P : C ⥤ D) (Q : B ⥤ E) (J : E ⥤ D)
    (h : R = (H ⋙ F) ⋙ P) (h' : R = H ⋙ (F ⋙ P)) (e : F ⋙ P ≅ Q ⋙ J) :
    (eqToIso h' ≪≫ isoWhiskerLeft H e) ≪≫
        (Functor.associator H Q J).symm =
    eqToIso h ≪≫ Functor.associator H F P ≪≫ isoWhiskerLeft H e ≪≫
        (Functor.associator H Q J).symm := by
  have hp : eqToIso h' = eqToIso h ≪≫ Functor.associator H F P :=
    (congrArg (fun p : R = H ⋙ (F ⋙ P) ↦ eqToIso p)
      (Subsingleton.elim h' (h.trans (functorAssoc H F P)))).trans
      (eqToIso_trans h (functorAssoc H F P)).symm
  refine (congrArg (fun a ↦ (a ≪≫ isoWhiskerLeft H e) ≪≫
    (Functor.associator H Q J).symm) hp).trans ?_
  simp only [Iso.trans_assoc]

private theorem original_model_anchor_word
    {V W T U S : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (R : V ⟶ U) (H : V ⟶ W) (F : W ⟶ T) (P : T ⟶ U) (Q : W ⟶ S) (J : S ⟶ U)
    (h : R.hom.toFunctor = (H.hom.toFunctor ⋙ F.hom.toFunctor) ⋙ P.hom.toFunctor)
    (h' : R.hom.toFunctor = (H ≫ (F ≫ P)).hom.toFunctor)
    (e : (F ≫ P).hom.toFunctor ≅ (Q ≫ J).hom.toFunctor) :
    (eqToIso h' ≪≫ isoWhiskerLeft H.hom.toFunctor e) ≪≫
        (Functor.associator H.hom.toFunctor Q.hom.toFunctor J.hom.toFunctor).symm =
    eqToIso h ≪≫ Functor.associator H.hom.toFunctor F.hom.toFunctor P.hom.toFunctor ≪≫
      isoWhiskerLeft H.hom.toFunctor e ≪≫
        (Functor.associator H.hom.toFunctor Q.hom.toFunctor J.hom.toFunctor).symm :=
  original_anchor_word R.hom.toFunctor H.hom.toFunctor F.hom.toFunctor P.hom.toFunctor
    Q.hom.toFunctor J.hom.toFunctor h h' e

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem product_node (i j : Fin 2) :
    nodes g (Topology.SimplexGrid.index 1 1 (i, j)) =
      (⟨unitMap Y ≫ firstVertices (laurent.map g) j, InputSeedInputUnitProduct.anchor g ≪≫
        (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
          ((unitAnchors Y i).prod (firstAnchors (laurent.map g) j))⟩ :
        Node (InputSeedCarrier.laurentRef g)) := by
  unfold InputSeedInputUnitProduct.nodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Topology.SimplexGrid.decode_index]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The initial product corner is the original full mixed source, not only its native image. -/
theorem zero_node : nodes g 0 = InputSeedUnitNodes.lower g 0 := by
  change nodes g (Topology.SimplexGrid.index 1 1 (0, 0)) = _
  rw [product_node]
  change (⟨unitMap Y ≫ firstSource (laurent.map g), InputSeedInputUnitProduct.anchor g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (unitMap Y).hom.toFunctor).prod
        (Iso.refl (firstSource (laurent.map g)).hom.toFunctor))⟩ :
      Node (InputSeedCarrier.laurentRef g)) = _
  rw [pair_iso, isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_trans]
  refine (congrArg (fun e ↦ (⟨unitMap Y ≫ firstSource (laurent.map g), e⟩ :
    Node (InputSeedCarrier.laurentRef g)))
      (Iso.trans_refl (InputSeedInputUnitProduct.anchor g))).trans ?_
  exact identity_anchor_node (InputSeedCarrier.laurentRef g)
    (unitMap Y ≫ firstSource (laurent.map g)) (source_eq g)

private theorem terminal_anchor :
    (InputSeedInputUnitProduct.anchor g ≪≫ isoWhiskerLeft (unitMap Y).hom.toFunctor
      (evaluationComparisonIso (laurent.map g))) ≪≫
      (Functor.associator (unitMap Y).hom.toFunctor (evaluationModel
        (op (laurent.obj Y))).hom.toFunctor
        (evaluationRawMap (laurent.map g)).hom.toFunctor).symm =
      evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y) := by
  unfold InputSeedInputUnitProduct.anchor evaluationCompositionFirstIso
  exact original_model_anchor_word (InputSeedCarrier.laurentRef g) (unitMap Y)
    (boundedAboveFlatGlobalSectionModelFunctor.map (laurent.map g).op)
    (evaluationModel (op (laurent.obj X))) (evaluationModel (op (laurent.obj Y)))
    (evaluationRawMap (laurent.map g))
    (congrArg (fun K ↦ K ⋙ (evaluationModel (op (laurent.obj X))).hom.toFunctor)
      (evaluationReindexComp (laurent.map g) (GlobalRawBass.laurentProjection.app Y)))
    (source_eq g) (evaluationComparisonIso (laurent.map g))

set_option backward.isDefEq.respectTransparency true in
/-- The terminal lower corner retains the original Laurent evaluation reference word. -/
theorem one_node : nodes g 1 = InputSeedUnitNodes.lower g 3 := by
  change nodes g (Topology.SimplexGrid.index 1 1 (0, 1)) = _
  rw [product_node]
  change (⟨unitMap Y ≫ firstTarget (laurent.map g), InputSeedInputUnitProduct.anchor g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (unitMap Y).hom.toFunctor).prod (evaluationComparisonIso (laurent.map g)))⟩ :
      Node (InputSeedCarrier.laurentRef g)) = _
  rw [pair_iso, isoWhiskerRight_refl, Iso.refl_trans]
  exact reassociate_node (InputSeedCarrier.laurentRef g) (unitMap Y)
    (evaluationModel (op (laurent.obj Y))) (evaluationRawMap (laurent.map g))
    (InputSeedInputUnitProduct.anchor g ≪≫
      isoWhiskerLeft (unitMap Y).hom.toFunctor (evaluationComparisonIso (laurent.map g)))
    (evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y))
    (terminal_anchor g)

/-- Actual strict Laurent reindexing and evaluation preserve the unchanged source unit. -/
theorem evaluation_preserves : Preserves (firstSource (laurent.map g)).hom.toFunctor
    (strictLaurentUnit (op Y))
    (evaluationSmallUnit (op (laurent.obj X)) (laurentScalar (op X))) :=
  preserves_comp (boundedAboveFlatGlobalSectionModelFunctor.map (laurent.map g).op) (evaluationModel
    (op (laurent.obj X)))
    (strictLaurentUnit (op Y)) (strictLaurentUnit (op X))
    (evaluationSmallUnit (op (laurent.obj X)) (laurentScalar (op X)))
    (strictLaurentUnit_naturality g.op)
    (evaluationModel_unit (op (laurent.obj X)) (laurentScalar (op X)))

set_option backward.isDefEq.respectTransparency true in
/-- The full original product reference intertwines the strict source unit. -/
theorem anchor_unit :
    InputSeedCarrier.commonUnit g ≪≫ InputSeedInputUnitProduct.anchor g =
      InputSeedInputUnitProduct.anchor g ≪≫
        isoWhiskerRight (unitIso Y) (firstSource (laurent.map g)).hom.toFunctor := by
  have h := preserved_onFunctor (unitMap Y) (firstSource (laurent.map g))
    (strictLaurentUnit (op Y))
    (evaluationSmallUnit (op (laurent.obj X)) (laurentScalar (op X)))
    (evaluation_preserves g)
  exact (InputSeedCarrier.anchor_unit g
    ⟨unitMap Y ≫ firstSource (laurent.map g), InputSeedInputUnitProduct.anchor g⟩).trans
      (congrArg (fun e ↦ InputSeedInputUnitProduct.anchor g ≪≫ e) h.symm)

/-- Every shifted product node retains its actual common-unit anchor before realization. -/
theorem shifted_node (j : Fin 2) :
    nodes g (Topology.SimplexGrid.index 1 1 (1, j)) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (nodes g (Topology.SimplexGrid.index 1 1 (0, j))) := by
  rw [product_node, product_node]
  exact source_shift_node (InputSeedCarrier.laurentRef g) (unitMap Y)
    (firstSource (laurent.map g)) (firstVertices (laurent.map g) j)
    (InputSeedInputUnitProduct.anchor g)
    (firstAnchors (laurent.map g) j) (unitIso Y) (InputSeedCarrier.commonUnit g) (anchor_unit g)

/-- The first shifted corner is the separately anchored original source. -/
theorem two_node : nodes g 2 = InputSeedUnitNodes.upper g 0 :=
  (shifted_node g 0).trans
    (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)) (zero_node g))

/-- The terminal shifted corner is the separately anchored original evaluation cut. -/
theorem three_node : nodes g 3 = InputSeedUnitNodes.upper g 3 :=
  (shifted_node g 1).trans
    (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)) (one_node g))

/-- The actual product order is unit first; the public square coordinates are evaluation first. -/
def cornerIndex : Fin 4 → Fin 16 := ![0, 3, 8, 11]

/-- Every product corner agrees as a complete dependent node in the main sixteen-node family. -/
theorem corners (i : Fin 4) : nodes g i = InputSeedUnitNodes.nodes g (cornerIndex i) := by
  fin_cases i
  · exact zero_node g
  · exact one_node g
  · exact two_node g
  · exact three_node g

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputUnitNodes
