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

/-!
# The complete strict source of the attached chart square

The original pure reference transports identify the source as a complete Model arrow
with its original anchor, before any scalar or native realization.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSourceNode
open GlobalSectionChangeIndex

private theorem associator_eqToIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    Functor.associator F G H = eqToIso (Functor.assoc F G H) := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem pure_source_node
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (R F : V ⟶ W)
    (e : R.hom.toFunctor = F.hom.toFunctor) :
    (⟨F, eqToIso e⟩ : CommonReferenceNerve.Node R) = ⟨R, Iso.refl _⟩ := by
  apply ModelSimplex.reference_node_eq e.symm
  simp only [eqToIso.hom, eqToHom_trans, eqToHom_refl, Iso.refl_hom]

private theorem pure_trans {C : Type*} [Category C] {A B D : C}
    (α : A ≅ B) (β : B ≅ D)
    (hα : ∃ e : A = B, α = eqToIso e) (hβ : ∃ e : B = D, β = eqToIso e) :
    ∃ e : A = D, α ≪≫ β = eqToIso e := by
  obtain ⟨e, rfl⟩ := hα
  obtain ⟨f, rfl⟩ := hβ
  exact ⟨e.trans f, eqToIso_trans e f⟩

private theorem sourceIso_pure :
    ∃ e : (InputMixedDesc.sourceMap g).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op ≫
        InputSimplex.sourceMap (laurent.map g) (k.app Y)).hom.toFunctor,
      InputChartSquareParameter.sourceIso g k hk = eqToIso e := by
  unfold InputChartSquareParameter.sourceIso InputChartReference.chartSourceIso
    InputTripleNodes.preSourceIso
  rw [associator_eqToIso]
  exact pure_trans _ _ ⟨_, rfl⟩
    (pure_trans _ _ ⟨_, rfl⟩ (pure_trans _ _ ⟨_, rfl⟩ ⟨_, rfl⟩))

/-- The initial chart node is the actual mixed source with its complete identity anchor. -/
theorem source_node :
    InputChartSquareParameter.nodes g k hk 0 =
      (⟨InputMixedDesc.sourceMap g, Iso.refl _⟩ : InputChartReference.Node g) := by
  refine (CommonReferenceNerve.attachPrecompNode_source
    (InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y))
    (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op)
    (InputMixedDesc.sourceMap g) (InputChartSquareParameter.sourceIso g k hk)).trans ?_
  obtain ⟨e, he⟩ := sourceIso_pure g k hk
  rw [he]
  exact pure_source_node (InputMixedDesc.sourceMap g)
    (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op ≫
      InputSimplex.sourceMap (laurent.map g) (k.app Y)) e

private theorem preSourceIso_pure :
    ∃ e : (InputMixedDesc.sourceMap g).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
        InputChartSimplex.sourceMap X).hom.toFunctor,
      InputMixedDesc.preSourceIso g = eqToIso e := by
  unfold InputMixedDesc.preSourceIso
  rw [associator_eqToIso]
  exact pure_trans _ _ ⟨_, rfl⟩ (pure_trans _ _ ⟨_, rfl⟩ ⟨_, rfl⟩)

/-- The original X chart has the same complete strict-source reference. -/
theorem pre_source_node :
    InputChartSquareParameter.nodes g k hk 0 = InputChartReference.preNode g k hk 0 := by
  refine (source_node g k hk).trans ?_
  symm
  rw [InputChartReference.pre_nodes, InputChartSimplex.chartNodes_zero]
  refine (CommonReferenceNerve.attachPrecompNode_source (InputChartSimplex.sourceMap X)
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputMixedDesc.sourceMap g) (InputMixedDesc.preSourceIso g)).trans ?_
  obtain ⟨e, he⟩ := preSourceIso_pure g
  rw [he]
  exact pure_source_node (InputMixedDesc.sourceMap g)
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ InputChartSimplex.sourceMap X)
    e

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSourceNode
