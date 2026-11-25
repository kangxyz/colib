/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluation
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNodeTransport

/-!
# Both actual global evaluation charts in one finite diagram

The positive and inverse chart composition diagrams share their complete source and total
nodes. Their anchors retain the original Laurent evaluation. The remaining six vertices keep
the two separate geometric normalization intermediates and original evaluation cuts.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- The original common Laurent evaluation source. -/
def sourceMap :=
  boundedAboveFlatGlobalSectionModelFunctor.map (GlobalRawBass.laurentProjection.app X).op ≫
  evaluationModel (op (laurent.obj X))

/-- The original common evaluated raw Laurent projection. -/
def totalMap := evaluationModel (op X) ≫ evaluationRawMap (GlobalRawBass.laurentProjection.app X)

/-- The actual chart equation identifies its original strict composite source. -/
theorem source_eq (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X) :
    InputSimplex.sourceMap k (projection.app X) = sourceMap X := by
  unfold InputSimplex.sourceMap sourceMap
  rw [h]

/-- Full chart nodes retain their actual Model maps and unchanged reference isomorphisms. -/
def chartNodes (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X) :
    Fin 5 → Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op X) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace),
      (sourceMap X).hom.toFunctor ≅ F.hom.toFunctor := fun i =>
  ⟨InputSimplex.vertices k (projection.app X) i,
    eqToIso (congrArg (fun f => f.hom.toFunctor) (source_eq X k h).symm) ≪≫
      InputSimplex.anchors k (projection.app X) i⟩

/-- The shared source includes the complete anchor, not merely its realized map. -/
theorem chartNodes_zero (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X) :
    chartNodes X k h 0 = ⟨sourceMap X, Iso.refl _⟩ := by
  apply ModelSimplex.reference_node_eq
    (congrArg (fun f => f.hom.toFunctor) (source_eq X k h))
  simp only [InputSimplex.anchors, Fin.cases_zero, Iso.trans_refl,
    eqToIso.hom, eqToHom_trans, eqToHom_refl, Iso.refl_hom]

/-- The shared total node retains the original Laurent evaluation isomorphism itself. -/
theorem chartNodes_one (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X) :
    chartNodes X k h 1 =
      ⟨totalMap X, evaluationComparisonIso (GlobalRawBass.laurentProjection.app X)⟩ := by
  have ha : InputSimplex.anchors k (projection.app X) 1 =
      evaluationComparisonIso (k ≫ projection.app X) := rfl
  dsimp only [chartNodes]
  rw [ha]
  let S (a : laurent.obj X ⟶ X) :=
    boundedAboveFlatGlobalSectionModelFunctor.map a.op ≫ evaluationModel (op (laurent.obj X))
  let T (a : laurent.obj X ⟶ X) := evaluationModel (op X) ≫ evaluationRawMap a
  have hh := ModelSimplex.transportedReferenceNode_congr (sourceMap X) S T
    (fun a => evaluationComparisonIso a) h
    (congrArg (fun f => f.hom.toFunctor) (source_eq X k h).symm) rfl
  simpa only [ModelSimplex.transportedReferenceNode, eqToIso_refl, Iso.refl_trans,
    InputSimplex.vertices, Matrix.cons_val_one, Matrix.cons_val_zero,
    InputSimplex.totalMap, T, totalMap] using hh

/-- The eight nodes preserve both separate chart normalization diagrams. -/
def nodes : Fin 8 → Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op X) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace),
    (sourceMap X).hom.toFunctor ≅ F.hom.toFunctor :=
  ![chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 0,
    chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 1,
    chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 2,
    chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 3,
    chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 4,
    chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) 2,
    chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) 3,
    chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) 4]

/-- One original common-reference diagram contains both full evaluation charts. -/
def simplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace)) 7 :=
  ModelSimplex.ofIsos (sourceMap X) (fun i => (nodes X i).1) (fun i => (nodes X i).2)

/-- The actual positive chart embedding. -/
def plusFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 4], by decide⟩

/-- The separate inverse chart embedding shares only the two genuine common nodes. -/
def minusFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 5, 6, 7], by decide⟩

private theorem chart_nodes_simplex (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X) :
    ModelSimplex.ofIsos (sourceMap X) (fun i => (chartNodes X k h i).1)
      (fun i => (chartNodes X k h i).2) = InputSimplex.simplex k (projection.app X) :=
  ModelSimplex.ofIsos_change_reference _ _ _

/-- The entire positive chart diagram is unchanged inside the common carrier. -/
theorem plus_face : (simplex X).face plusFace =
    InputSimplex.simplex (plus.app X) (projection.app X) := by
  rw [simplex, ModelSimplex.ofIsos_face]
  trans ModelSimplex.ofIsos (sourceMap X)
    (fun i => (chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) i).1)
    (fun i => (chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) i).2)
  · apply ModelSimplex.ofIsos_nodes_congr
    intro i
    fin_cases i <;> rfl
  · exact chart_nodes_simplex X _ _

/-- The entire inverse chart diagram shares the exact source and total anchor nodes. -/
theorem minus_face : (simplex X).face minusFace =
    InputSimplex.simplex (minus.app X) (projection.app X) := by
  rw [simplex, ModelSimplex.ofIsos_face]
  trans ModelSimplex.ofIsos (sourceMap X)
    (fun i => (chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) i).1)
    (fun i => (chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) i).2)
  · apply ModelSimplex.ofIsos_nodes_congr
    intro i
    fin_cases i
    · exact (chartNodes_zero X (plus.app X) (GlobalRawBass.plus_projection X)).trans
        (chartNodes_zero X (minus.app X) (GlobalRawBass.minus_projection X)).symm
    · exact (chartNodes_one X (plus.app X) (GlobalRawBass.plus_projection X)).trans
        (chartNodes_one X (minus.app X) (GlobalRawBass.minus_projection X)).symm
    · rfl
    · rfl
    · rfl
  · exact chart_nodes_simplex X _ _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
