/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference

/-!
# Complete strict-precomposition attachment of the original evaluation charts

The actual chart equation and both geometric squares identify the entire strict source
reference with the mixed Laurent reference. Appending each unchanged original chart anchor
then attaches all five strict-precomposed nodes, before any evaluation-comparison bridges.
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
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem associator_eqToIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    Functor.associator F G H = eqToIso (Functor.assoc F G H) := by
  rfl

private theorem whisker_eqToIso {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F : A ⥤ B) {G H : B ⥤ C} (e : G = H) :
    isoWhiskerLeft F (eqToIso e) = eqToIso (congrArg (fun K => F ⋙ K) e) := by
  cases e
  rfl

/-- Both original square transports and strict composition agree with the mixed reference. -/
theorem pre_source_iso :
    (chartSourceIso g k hk ≪≫
      InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g)) ≪≫
      InputTripleNodes.preSourceIso (k.app X) (projection.app X) g =
    InputMixedDesc.preSourceIso g ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
        (eqToIso (congrArg (fun F ↦ F.hom.toFunctor)
          (InputChartSimplex.source_eq X (k.app X) (hk X)).symm)) := by
  simp only [chartSourceIso, InputRectangleNodes.lastSourceIso,
    InputTripleNodes.preSourceIso, InputMixedDesc.preSourceIso,
    associator_eqToIso, whisker_eqToIso, eqToIso_trans]

private theorem append_reference {A B C : Type*}
    [Category A] [Category B] [Category C]
    (J : A ⥤ B) {U V W : A ⥤ C} {F G H : B ⥤ C}
    (e₀ : U ≅ V) (e₁ : V ≅ W) (e₂ : W ≅ J ⋙ G) (e : U ≅ J ⋙ F)
    (t : F ≅ G) (a : G ≅ H)
    (h : (e₀ ≪≫ e₁) ≪≫ e₂ = e ≪≫ isoWhiskerLeft J t) :
    e₀ ≪≫ (e₁ ≪≫ (e₂ ≪≫ isoWhiskerLeft J a)) =
      e ≪≫ isoWhiskerLeft J (t ≪≫ a) := by
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]
  exact Iso.trans_assoc _ _ _

private theorem append_node_reference
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (J : V ⟶ W) (S R₀ R₁ : V ⟶ T) (F G : W ⟶ T)
    (e₀ : S.hom.toFunctor ≅ R₀.hom.toFunctor) (e₁ : R₀.hom.toFunctor ≅ R₁.hom.toFunctor)
    (e₂ : R₁.hom.toFunctor ≅ (J ≫ G).hom.toFunctor) (e : S.hom.toFunctor ≅ (J ≫ F).hom.toFunctor)
    (t : F.hom.toFunctor ≅ G.hom.toFunctor)
    (N : Σ H : W ⟶ T, G.hom.toFunctor ≅ H.hom.toFunctor)
    (h : (e₀ ≪≫ e₁) ≪≫ e₂ = e ≪≫ isoWhiskerLeft J.hom.toFunctor t) :
    (⟨J ≫ N.1, e₀ ≪≫ (e₁ ≪≫ (e₂ ≪≫ isoWhiskerLeft J.hom.toFunctor N.2))⟩ :
      Σ H : V ⟶ T, S.hom.toFunctor ≅ H.hom.toFunctor) =
    ⟨J ≫ N.1, e ≪≫ isoWhiskerLeft J.hom.toFunctor (t ≪≫ N.2)⟩ :=
  congrArg (fun a => (⟨J ≫ N.1, a⟩ : Σ H : V ⟶ T, S.hom.toFunctor ≅ H.hom.toFunctor))
    (append_reference J.hom.toFunctor e₀ e₁ e₂ e t N.2 h)

/-- Every original X chart node agrees with its complete strict-precomposed mixed node. -/
theorem pre_nodes (i : Fin 5) : preNode g k hk i =
    InputMixedDesc.preNode g (InputChartSimplex.chartNodes X (k.app X) (hk X) i) :=
  append_node_reference (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
    (InputMixedDesc.sourceMap g)
    (InputTripleNodes.sourceMap (laurent.map g) (k.app Y) (projection.app Y))
    (InputTripleNodes.sourceMap (k.app X) (projection.app X) g)
    (InputChartSimplex.sourceMap X) (InputSimplex.sourceMap (k.app X) (projection.app X))
    (chartSourceIso g k hk)
    (InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputTripleNodes.preSourceIso (k.app X) (projection.app X) g)
    (InputMixedDesc.preSourceIso g)
    (eqToIso (congrArg (fun F ↦ F.hom.toFunctor)
      (InputChartSimplex.source_eq X (k.app X) (hk X)).symm))
    ⟨InputSimplex.vertices (k.app X) (projection.app X) i,
      InputSimplex.anchors (k.app X) (projection.app X) i⟩
    (pre_source_iso g k hk)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
