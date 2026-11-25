/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRectangleFaces
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTriplePreNodes

/-!
# The actual precomposition bridges in the mixed rectangle

The original strict-precomposed evaluation chart is retained as a whole diagram. Its three
normalization nodes reach the raw rectangle only through the specified original evaluation
comparison. Both geometric square equations remain in their complete source references.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRectangleNodes
open GlobalSectionChangeIndex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The actual two-square reference transport acts on the full original dependent node. -/
def lastReferenceNode (N : InputTripleNodes.Node q' p' a) : InputTripleNodes.Node c q p :=
  ⟨N.1, lastSourceIso p q p' q' a b c hp hq ≪≫ N.2⟩

/-- All five unmodified strict-precomposed chart nodes in the common rectangle reference. -/
def preNode (i : Fin 5) : InputTripleNodes.Node c q p :=
  lastReferenceNode p q p' q' a b c hp hq (InputTripleNodes.preNode q' p' a i)

/-- The total node after its original final evaluation bridge. -/
def preTotalNode : InputTripleNodes.Node c q p :=
  lastReferenceNode p q p' q' a b c hp hq (InputTripleNodes.preTotalNode q' p' a)

/-- The actual geometric intermediate after its original final evaluation bridge. -/
def preIntermediateNode : InputTripleNodes.Node c q p :=
  lastReferenceNode p q p' q' a b c hp hq (InputTripleNodes.preIntermediateNode q' p' a)

/-- The fully split target after its original final evaluation bridge. -/
def preTargetNode : InputTripleNodes.Node c q p :=
  lastReferenceNode p q p' q' a b c hp hq (InputTripleNodes.preTargetNode q' p' a)

/-- The converted total is exactly raw rectangle node fifteen, including its complete anchor. -/
theorem pre_total_node : preTotalNode p q p' q' a b c hp hq =
    rawNode p q p' q' a b c hp hq 15 := by
  unfold preTotalNode
  rw [InputTripleNodes.pre_total_node]
  exact (last_nodes p q p' q' a b c hp hq 5).symm

/-- The converted geometric intermediate is exactly raw rectangle node sixteen. -/
theorem pre_intermediate_node : preIntermediateNode p q p' q' a b c hp hq =
    rawNode p q p' q' a b c hp hq 16 := by
  unfold preIntermediateNode
  rw [InputTripleNodes.pre_intermediate_node]
  exact (last_nodes p q p' q' a b c hp hq 6).symm

/-- The converted target is exactly raw rectangle node seventeen with the original left anchor. -/
theorem pre_target_node : preTargetNode p q p' q' a b c hp hq =
    rawNode p q p' q' a b c hp hq 17 := by
  unfold preTargetNode
  rw [InputTripleNodes.pre_target_node]
  exact (last_nodes p q p' q' a b c hp hq 7).symm

/-- The normalization triangle after the three explicit original evaluation bridges. -/
def convertedNormalizationNode : Fin 3 → InputTripleNodes.Node c q p :=
  ![preTotalNode p q p' q' a b c hp hq,
    preIntermediateNode p q p' q' a b c hp hq, preTargetNode p q p' q' a b c hp hq]

/-- The actual converted normalization triangle in the original raw rectangle. -/
def preNormalizationFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![15, 16, 17], by decide⟩

/-- The entire converted triangle agrees as a carrier point, before evaluating native maps. -/
theorem converted_normalization_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (convertedNormalizationNode p q p' q' a b c hp hq) z =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (rawNode p q p' q' a b c hp hq)
      (StdSimplex.map preNormalizationFace.toOrderHom z) := by
  rw [CommonReferenceNerve.parameter_face]
  apply congrArg (fun N => CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p) N z)
  funext i
  fin_cases i
  · exact pre_total_node p q p' q' a b c hp hq
  · exact pre_intermediate_node p q p' q' a b c hp hq
  · exact pre_target_node p q p' q' a b c hp hq

/-- The total-node carrier arrow is the actual original evaluation comparison,
not an identification. -/
theorem pre_total_bridge :
    (preNode p q p' q' a b c hp hq 1).2.inv ≫
      (preTotalNode p q p' q' a b c hp hq).2.hom =
    (isoWhiskerRight (evaluationComparisonIso a)
      (evaluationRawMap (q' ≫ p')).hom.toFunctor).hom := by
  change (lastSourceIso p q p' q' a b c hp hq ≪≫
      (InputTripleNodes.preNode q' p' a 1).2).inv ≫
    (lastSourceIso p q p' q' a b c hp hq ≪≫
      ((InputTripleNodes.preNode q' p' a 1).2 ≪≫
        isoWhiskerRight (evaluationComparisonIso a)
          (evaluationRawMap (q' ≫ p')).hom.toFunctor)).hom = _
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]

/-- The intermediate carrier arrow retains the actual original geometric suffix. -/
theorem pre_intermediate_bridge :
    (preNode p q p' q' a b c hp hq 2).2.inv ≫
      (preIntermediateNode p q p' q' a b c hp hq).2.hom =
    (isoWhiskerRight (evaluationComparisonIso a)
      (BoundedFlatPerfectBinarySimplex.intermediateMap q' p').hom.toFunctor).hom := by
  change (lastSourceIso p q p' q' a b c hp hq ≪≫
      (InputTripleNodes.preNode q' p' a 2).2).inv ≫
    (lastSourceIso p q p' q' a b c hp hq ≪≫
      ((InputTripleNodes.preNode q' p' a 2).2 ≪≫
        isoWhiskerRight (evaluationComparisonIso a)
          (BoundedFlatPerfectBinarySimplex.intermediateMap q' p').hom.toFunctor)).hom = _
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]

/-- The target carrier arrow retains the complete original split raw suffix. -/
theorem pre_target_bridge :
    (preNode p q p' q' a b c hp hq 4).2.inv ≫
      (preTargetNode p q p' q' a b c hp hq).2.hom =
    (isoWhiskerRight (evaluationComparisonIso a)
      (evaluationRawMap p' ≫ evaluationRawMap q').hom.toFunctor).hom := by
  change (lastSourceIso p q p' q' a b c hp hq ≪≫
      (InputTripleNodes.preNode q' p' a 4).2).inv ≫
    (lastSourceIso p q p' q' a b c hp hq ≪≫
      ((InputTripleNodes.preNode q' p' a 4).2 ≪≫
        isoWhiskerRight (evaluationComparisonIso a)
          (evaluationRawMap p' ≫ evaluationRawMap q').hom.toFunctor)).hom = _
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]

/-- The entire unmodified strict-precomposed original evaluation chart. -/
def preSimplex := ModelSimplex.ofIsos (InputTripleNodes.sourceMap c q p)
  (fun i => (preNode p q p' q' a b c hp hq i).1)
  (fun i => (preNode p q p' q' a b c hp hq i).2)

/-- Both reference transports preserve the entire original strict-precomposed diagram. -/
theorem pre_simplex : preSimplex p q p' q' a b c hp hq =
    (InputSimplex.simplex q' p').precomp (boundedAboveFlatGlobalSectionModelFunctor.map a.op) := by
  unfold preSimplex preNode lastReferenceNode
  rw [ModelSimplex.ofIsos_change_reference]
  unfold InputTripleNodes.preNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

/-- The original full X chart is a compact parameter in the same common-reference nerve. -/
def preParameter :=
  (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
    (preNode p q p' q' a b c hp hq)).comp InputSimplex.compositionParameter.toContinuousMap

/-- Every point retains the original selected X composition surface after strict pullback. -/
theorem pre_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op A))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputTripleNodes.sourceMap c q p)
      (preParameter p q p' q' a b c hp hq) n ((r, s), x) =
    (evaluationCompositionRelHomotopy q' p').level n
      (r, (s, (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map a.op)).map n x)) := by
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (preNode p q p' q' a b c hp hq) (r, s)
    (InputSimplex.compositionParameter (r, s)) rfl]
  change prespectrumSimplexFamily (preSimplex p q p' q' a b c hp hq) n _ = _
  rw [pre_simplex, prespectrumSimplexFamily_precomp]
  exact InputSimplex.composition_native q' p' n r s _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRectangleNodes
