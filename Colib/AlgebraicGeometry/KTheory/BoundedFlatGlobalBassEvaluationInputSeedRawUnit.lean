/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCarrier
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedUnitNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawDesc

/-!
# Original raw Laurent units in the mixed two-sheet reference

The actual pulled-back Laurent scalar identifies the original normalized source unit.
Its entire evaluation comparison intertwines the strict common unit. Consequently every
complete raw reference node commutes with the two sheet attachments before realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawUnit
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem reanchor_pre_unit {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (R : W ⟶ T) (e : F.hom.toFunctor ≅ (J ≫ R).hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (β : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : α ≪≫ e = e ≪≫ isoWhiskerLeft J.hom.toFunctor β) (N : Node R) :
    ModelSimplex.reanchorNode α (attachPrecompNode R J F e N) =
      attachPrecompNode R J F e (ModelSimplex.reanchorNode β N) := by
  apply congrArg (fun ρ => (⟨J ≫ N.1, ρ⟩ : Node F))
  change α ≪≫ (e ≪≫ isoWhiskerLeft J.hom.toFunctor N.2) =
    e ≪≫ isoWhiskerLeft J.hom.toFunctor (β ≪≫ N.2)
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

private theorem whisker_onFunctor
    {V W T : WideSubcategory preservesZero.{u}} (J : V ⟶ W) (R : W ⟶ T)
    (β : 𝟭 _ ≅ 𝟭 _) :
    isoWhiskerLeft J.hom.toFunctor (onFunctor R.hom.toFunctor β) =
      onFunctor (J ≫ R).hom.toFunctor β := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual old binary source unit, including its chosen-zero normalization. -/
def rawUnit := UnitTrackPostcompSimplex.sourceUnit (laurent.map g)
  (GlobalRawBass.laurentProjection.app Y) (laurentScalar (op Y))

/-- The actual Laurent scalar pullback identifies this unchanged raw transformation. -/
theorem rawUnit_hom : (rawUnit g).hom =
    evaluationRawUnit (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
      (laurentScalar (op X)) := by
  change evaluationRawUnit (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
    (Units.map (laurent.map g).appTop.hom.toMonoidHom
      (laurentScalar (op Y))) = _
  rw [GlobalRawBass.laurentUnit_map]

/-- The original normalized source unit is the actual target identity action. -/
theorem rawUnit_eq_target : rawUnit g =
    onFunctor
      (GlobalRawBass.InputIdentitySeedUnitNodes.source g).hom.toFunctor
      (evaluationSmallUnit (op (laurent.obj X))
        (laurentScalar (op X))) :=
  Iso.ext ((rawUnit_hom g).trans
    (evaluationRawUnit_eq (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
      (laurentScalar (op X))))

/-- The complete original total-evaluation isomorphism intertwines the two original units. -/
theorem evaluation_unit :
    InputSeedCarrier.commonUnit g ≪≫
        evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) =
      evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
        isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor (rawUnit g) := by
  let e : (InputSeedCarrier.laurentRef g).hom.toFunctor ≅
      (evaluationModel (op Y) ≫ GlobalRawBass.InputIdentitySeedUnitNodes.source g).hom.toFunctor :=
    evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
  change InputSeedCarrier.commonUnit g ≪≫ e =
    e ≪≫ isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor (rawUnit g)
  have hwhisker := whisker_onFunctor (evaluationModel (op Y))
    (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationSmallUnit (op (laurent.obj X))
      (laurentScalar (op X)))
  have hunit := congrArg (isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor)
    (rawUnit_eq_target g).symm
  have htransport := hwhisker.symm.trans hunit
  exact (InputSeedCarrier.anchor_unit g
    ⟨evaluationModel (op Y) ≫ GlobalRawBass.InputIdentitySeedUnitNodes.source g,
      e⟩).trans (congrArg (fun a => e ≪≫ a) htransport)

/-- The actual raw evaluation node retains its entire original reference isomorphism. -/
def evaluateNode (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    Node (InputSeedCarrier.laurentRef g) :=
  attachPrecompNode (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationModel (op Y)) (InputSeedCarrier.laurentRef g)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)) N

/-- Evaluation agrees with the already used original rectangle-node attachment. -/
theorem evaluateNode_eq (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    evaluateNode g N = InputRawDesc.evaluateNode g N := rfl

/-- Both sheets commute as full dependent nodes, not merely as equal native values. -/
theorem evaluate_shift (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g) (evaluateNode g N) =
      evaluateNode g (ModelSimplex.reanchorNode (rawUnit g) N) :=
  reanchor_pre_unit (InputSeedCarrier.laurentRef g) (evaluationModel (op Y))
    (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y))
    (InputSeedCarrier.commonUnit g) (rawUnit g) (evaluation_unit g) N

/-- The entire raw nerve parameter commutes with the same two original sheet attachments. -/
theorem evaluate_shift_parameter {k : ℕ}
    (N : Fin (k + 1) → Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g))
    (z : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
      (parameter (InputSeedCarrier.laurentRef g) (fun i => evaluateNode g (N i)) z) =
    parameter (InputSeedCarrier.laurentRef g)
      (fun i => evaluateNode g (ModelSimplex.reanchorNode (rawUnit g) (N i))) z := by
  rw [mapParameter_parameter]
  exact congrArg (fun ns => parameter (InputSeedCarrier.laurentRef g) ns z)
    (funext fun i => evaluate_shift g (N i))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawUnit
