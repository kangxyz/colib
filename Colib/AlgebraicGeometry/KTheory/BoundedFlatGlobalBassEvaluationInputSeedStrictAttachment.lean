/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationCarrier
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCarrier
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPreAttachment
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# The actual strict-precomposition attachments of the evaluation seed carrier

The existing complete terminal polynomial node fixes the source reference. Both full attaching
squares then follow before realization. The second square retains the same original strict
Laurent unit on both references, rather than merely identifying its native values.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity CategoryTheory.Waldhausen Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictAttachment
open GlobalSectionChangeIndex CommonReferenceNerve ModelSimplex

private theorem cancel_identity {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (e : D ≅ B) : f ≫ (𝟙 B ≫ e.inv ≫ e.hom) = f := by
  rw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem pinned_pre_node
    {V W T U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (P : V ⟶ W) (E : W ⟶ T)
    (R : T ⟶ U) (H : W ⟶ U) (F : V ⟶ U)
    (a : F.hom.toFunctor ≅ ((P ≫ E) ≫ R).hom.toFunctor)
    (δ : H.hom.toFunctor ≅ (E ≫ R).hom.toFunctor) :
    attachPrecompNode H P F
      (a ≪≫ Functor.associator P.hom.toFunctor E.hom.toFunctor R.hom.toFunctor ≪≫
        (isoWhiskerLeft P.hom.toFunctor δ).symm) ⟨E ≫ R, δ⟩ =
      (⟨(P ≫ E) ≫ R, a⟩ : Node F) := by
  apply ModelSimplex.reference_node_eq
    (Functor.assoc P.hom.toFunctor E.hom.toFunctor R.hom.toFunctor).symm
  apply NatTrans.ext
  funext Z
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerLeft_inv, whiskerLeft_app, Functor.associator_hom_app,
    eqToHom_refl, Category.comp_id, Category.assoc]
  change a.hom.app Z ≫ (𝟙 ((E.hom.toFunctor ⋙ R.hom.toFunctor).obj (P.hom.toFunctor.obj Z)) ≫
    δ.inv.app (P.hom.toFunctor.obj Z) ≫ δ.hom.app (P.hom.toFunctor.obj Z)) = a.hom.app Z
  exact cancel_identity (a.hom.app Z) (δ.app (P.hom.toFunctor.obj Z))

private theorem unit_from_anchor
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ T)
    (P : V ⟶ W) (R : W ⟶ T) (e : F.hom.toFunctor ≅ (P ≫ R).hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (δ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (β : 𝟭 T.obj.Obj ≅ 𝟭 T.obj.Obj)
    (ha : α ≪≫ e = e ≪≫
      CategoryTheory.Functor.IdentityAutomorphism.onFunctor (P ≫ R).hom.toFunctor β)
    (hb : δ = CategoryTheory.Functor.IdentityAutomorphism.onFunctor R.hom.toFunctor β) :
    α ≪≫ e = e ≪≫ isoWhiskerLeft P.hom.toFunctor δ := by
  subst δ
  exact ha

private theorem reanchor_pre
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ T)
    (P : V ⟶ W) (R : W ⟶ T) (e : F.hom.toFunctor ≅ (P ≫ R).hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (δ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : α ≪≫ e = e ≪≫ isoWhiskerLeft P.hom.toFunctor δ) (N : Node R) :
    ModelSimplex.reanchorNode α (attachPrecompNode R P F e N) =
      attachPrecompNode R P F e (ModelSimplex.reanchorNode δ N) := by
  apply congrArg (fun ρ => (⟨P ≫ N.1, ρ⟩ : Node F))
  change α ≪≫ (e ≪≫ isoWhiskerLeft P.hom.toFunctor N.2) =
    e ≪≫ isoWhiskerLeft P.hom.toFunctor (δ ≪≫ N.2)
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original polynomial evaluation endpoint fixes the entire strict reference. -/
def polynomialSourceIso : (InputSeedCarrier.polyRef g).hom.toFunctor ≅
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
      InputSeedEvaluationCarrier.polyRef X).hom.toFunctor :=
  (InputSpanParameterNodes.projectionNodes g 6).2 ≪≫
    Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (evaluationModel (op X)).hom.toFunctor
      (evaluationRawMap (projection.app X)).hom.toFunctor ≪≫
    (isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (evaluationComparisonIso (projection.app X))).symm

/-- Every polynomial node is strictly precomposed with its original Model map. -/
def polynomialNode := attachPrecompNode (InputSeedEvaluationCarrier.polyRef X)
  (boundedAboveFlatGlobalSectionModelFunctor.map g.op) (InputSeedCarrier.polyRef g)
    (polynomialSourceIso g)

/-- Every Laurent node uses the previously proved full strict source attachment. -/
def laurentNode := InputMixedDesc.preNode g

/-- The whole terminal polynomial reference agrees with the existing original projection node. -/
theorem polynomial_one : polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes X 1) =
    InputSpanParameterNodes.projectionNodes g 6 :=
  pinned_pre_node (boundedAboveFlatGlobalSectionModelFunctor.map g.op) (evaluationModel (op X))
    (evaluationRawMap (projection.app X)) (InputSeedEvaluationCarrier.polyRef X)
    (InputSeedCarrier.polyRef g) (InputSpanParameterNodes.projectionNodes g 6).2
    (evaluationComparisonIso (projection.app X))

/-- The ordinary objectwise chart attachment retains its full original source anchor. -/
def originalOrdinaryNode := attachPostcompNode (InputSeedEvaluationCarrier.polyRef X)
  (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.laurentRef X)
  (InputSeedEvaluationCarrier.ordinary X)

/-- The mixed ordinary attachment is the frozen actual positive chart attachment. -/
def ordinaryNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g)

/-- The original complete terminal chart node fixes the entire ordinary attaching square. -/
theorem ordinary_terminal :
    laurentNode g (originalOrdinaryNode (X := X)
      (InputSeedEvaluationCarrier.polynomialNodes X 1)) =
    ordinaryNode g (polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes X 1)) := by
  rw [polynomial_one]
  have ho := InputSeedEvaluationCarrier.polynomial_nodes X 1
  have hp := InputChartReference.pre_nodes g plus GlobalRawBass.plus_projection 4
  have hr := InputChartReference.prism_pre_nodes g plus GlobalRawBass.plus_projection 2
  exact (congrArg (laurentNode g) ho.symm).trans
    (hp.symm.trans (hr.symm.trans
      (InputSpanParameterNodes.node_six g plus GlobalRawBass.plus_projection).symm))

/-- Every complete polynomial node satisfies the actual ordinary attachment square. -/
theorem ordinary_node (N : Node (InputSeedEvaluationCarrier.polyRef X)) :
    laurentNode g (originalOrdinaryNode (X := X) N) =
      ordinaryNode g (polynomialNode g N) :=
  prePost_families_match (InputSeedCarrier.laurentRef g)
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.polyRef X) (fun M => M)
    (fun M => pre_post_node (InputSeedCarrier.laurentRef g)
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
      (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.polyRef X) (fun M => M)
      (InputSeedEvaluationCarrier.ordinary X) (InputMixedDesc.preSourceIso g) M)
    (fun M => post_pre_node (InputSeedCarrier.laurentRef g)
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
      (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.polyRef X) (fun M => M)
      (polynomialSourceIso g) (InputSeedCarrier.ordinary g) M)
    (InputSeedEvaluationCarrier.polynomialNodes X 1) (ordinary_terminal g) N

/-- The actual strict Laurent units intertwine the entire original precomposition reference. -/
theorem laurent_unit :
    InputSeedCarrier.commonUnit g ≪≫ InputMixedDesc.preSourceIso g =
      InputMixedDesc.preSourceIso g ≪≫
        isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
        (InputSeedEvaluationCarrier.commonUnit X) :=
  unit_from_anchor (InputSeedCarrier.laurentRef g)
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputSeedEvaluationCarrier.laurentRef X) (InputMixedDesc.preSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit X)
    (evaluationSmallUnit (op (laurent.obj X))
      (laurentScalar (op X)))
    (InputSeedCarrier.anchor_unit g
      ⟨boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ InputSeedEvaluationCarrier.laurentRef X,
        InputMixedDesc.preSourceIso g⟩)
    (InputSeedEvaluationCarrier.commonUnit_eq_target X)

/-- The complete Laurent node, including its unit anchor, survives strict precomposition. -/
theorem laurent_shift (N : Node (InputSeedEvaluationCarrier.laurentRef X)) :
    ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g) (laurentNode g N) =
      laurentNode g
        (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit X) N) :=
  reanchor_pre (InputSeedCarrier.laurentRef g) (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputSeedEvaluationCarrier.laurentRef X) (InputMixedDesc.preSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit X) (laurent_unit g) N

/-- The second objectwise attachment retains the distinct original unit-shifted sheet. -/
def originalShiftedNode := attachPostcompNode (InputSeedEvaluationCarrier.polyRef X)
  (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.laurentRef X)
  (InputSeedEvaluationCarrier.shifted X)

/-- The second mixed attachment retains its original common Laurent unit. -/
def shiftedNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) (InputSeedCarrier.laurentRef g) (InputSeedCarrier.shifted g)

/-- Every node satisfies the entire shifted attachment square before realization. -/
theorem shifted_node (N : Node (InputSeedEvaluationCarrier.polyRef X)) :
    laurentNode g (originalShiftedNode (X := X) N) =
      shiftedNode g (polynomialNode g N) := by
  have ho := reanchor_attach_node (InputSeedEvaluationCarrier.polyRef X)
    (InputSeedCarrier.chart (X := X)) (InputSeedEvaluationCarrier.laurentRef X)
    (InputSeedEvaluationCarrier.commonUnit X) (InputSeedEvaluationCarrier.ordinary X) N
  exact (congrArg (laurentNode g) ho.symm).trans
    ((laurent_shift g (originalOrdinaryNode (X := X) N)).symm.trans
      ((congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
        (ordinary_node g N)).trans (InputSeedCarrier.shifted_node g (polynomialNode g N))))

private theorem parameter_square
    {V W V' W' T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (F : V ⟶ W) (G : V ⟶ T) (F' : V' ⟶ W') (G' : V' ⟶ T)
    (a : Node F → Node G) (b : Node F' → Node G')
    (p : Node F → Node F') (q : Node G → Node G')
    (h : ∀ N, q (a N) = b (p N)) (y : |nerve (Codiscrete (Node F))|) :
    mapParameter q (mapParameter a y) = mapParameter b (mapParameter p y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns => parameter G' ns z) (funext fun i => h (N i))

/-- The whole ordinary attaching square retains every actual original nerve parameter. -/
theorem ordinary_parameter
    (y : |nerve (Codiscrete (Node (InputSeedEvaluationCarrier.polyRef X)))|) :
    mapParameter (laurentNode g)
      (mapParameter (originalOrdinaryNode (X := X)) y) =
    mapParameter (ordinaryNode g) (mapParameter (polynomialNode g) y) :=
  parameter_square (InputSeedEvaluationCarrier.polyRef X)
    (InputSeedEvaluationCarrier.laurentRef X) (InputSeedCarrier.polyRef g)
    (InputSeedCarrier.laurentRef g) (originalOrdinaryNode (X := X)) (ordinaryNode g)
    (polynomialNode g) (laurentNode g) (ordinary_node g) y

/-- Every point of the second attaching square keeps its distinct original Laurent-unit sheet. -/
theorem shifted_parameter
    (y : |nerve (Codiscrete (Node (InputSeedEvaluationCarrier.polyRef X)))|) :
    mapParameter (laurentNode g)
      (mapParameter (originalShiftedNode (X := X)) y) =
    mapParameter (shiftedNode g) (mapParameter (polynomialNode g) y) :=
  parameter_square (InputSeedEvaluationCarrier.polyRef X)
    (InputSeedEvaluationCarrier.laurentRef X) (InputSeedCarrier.polyRef g)
    (InputSeedCarrier.laurentRef g) (originalShiftedNode (X := X)) (shiftedNode g)
    (polynomialNode g) (laurentNode g) (shifted_node g) y

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictAttachment
