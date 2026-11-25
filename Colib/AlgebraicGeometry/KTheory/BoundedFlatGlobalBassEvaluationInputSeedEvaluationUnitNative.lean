/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationUnitNodes

/-!
# The entire original evaluation-unit pasting in its complete-node simplex

The raw transformation, both nested ofLevels transports, the reversed first triangle and the
second triangle are unchanged. The lift identifies the entire native family at every level,
including its independent zero-level loop and prespectrum structure coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity CategoryTheory.Waldhausen Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
open GlobalSectionChangeIndex

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The exact inner intertwining comparison stored in the original evaluation-unit pasting. -/
def rawPasting :
    ((evaluationOldUnit f r).trans (evaluationComparison f)).RelHomotopy
      ((evaluationComparison f).trans (evaluationNewUnit f r)) :=
  prespectrumTransformationIntertwiningHomotopy
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op) (evaluationRawMap f)
    (evaluationModel (op Y)) (evaluationModel (op X))
    (sectionUnit f r).hom (evaluationRawUnit f r) (evaluationComparisonIso f).hom
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj (op X)).obj.waldhausen.weq_iso
      _ inferInstance)
    (fun K => normalizedWeakTransformation_weak
      (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullbackUnitIso f r).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
      (AsSmall.down.obj K))
    (fun A => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso f).app A).hom)))
    (evaluation_unit_square f r)

/-- The exact inner comparison has the original four-node, two-triangle lift. -/
theorem raw_native :
    HomotopyLift (simplex f r) scalarParameter (rawPasting f r) :=
  SimplexIntertwiningLift.native
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op) (evaluationRawMap f)
    (evaluationModel (op Y)) (evaluationModel (op X))
    (sectionUnit f r) (evaluationComparisonIso f)
    (evaluationRawUnit f r) _ _ _ (evaluation_unit_square f r)

private theorem ofLevels_whole {E D : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ D} {H K : Homotopy f g}
    (J L : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (hJL : J = L) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (L.level n).toContinuousMap := by
  cases hJL
  rfl

attribute [local irreducible] prespectrumTransformationIntertwiningHomotopy

/-- The final original ofLevels wrapper changes no point of the entire level family. -/
theorem original_level (n : ℕ) :
    ((evaluationUnitPasting f r).level n).toContinuousMap =
      ((rawPasting f r).level n).toContinuousMap := by
  unfold evaluationUnitPasting
  refine ofLevels_whole _ (rawPasting f r) _ _ _ _ ?_ n
  rfl

/-- The whole actual original evaluation-unit pasting, with every original clock, is lifted. -/
theorem native :
    HomotopyLift (simplex f r) scalarParameter (evaluationUnitPasting f r) := by
  intro n s t x
  exact (raw_native f r n s t x).trans
    (DFunLike.congr_fun (original_level f r n) (s, (t, x))).symm

/-- The entire square as a continuous map in both original comparison times and source point. -/
def family (n : ℕ) :
    C(unitInterval × (unitInterval ×
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n),
      (prespectrum (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).space n) :=
  (prespectrumSimplexFamily (simplex f r) n).comp
    ⟨fun z => (scalarParameter (z.1, z.2.1), z.2.2), by fun_prop⟩

/-- Equality of whole continuous maps retains every native level, not only a boundary edge. -/
theorem family_eq (n : ℕ) :
    family f r n = ((evaluationUnitPasting f r).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, t, x⟩
  exact native f r n s t x

/-- The same common family is the entire original inner intertwining comparison. -/
theorem raw_family_eq (n : ℕ) :
    family f r n = ((rawPasting f r).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, t, x⟩
  exact raw_native f r n s t x

/-- The independent original structure coordinate is preserved throughout the whole square. -/
theorem family_structure (n : ℕ) (s t v : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    family f r (n + 1)
        (s, (t,
          (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).structureMap
            n x v)) =
      (prespectrum (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).structureMap n
        (family f r n (s, (t, x))) v :=
  prespectrumSimplexFamily_structure (simplex f r) n (scalarParameter (s, t)) x v

/-- Level zero keeps its original loop coordinate separate from both comparison times. -/
theorem zero_apply (s t v : unitInterval)
    (x : Path (stagePoint 0 (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y)))
      (stagePoint 0 (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y)))) :
    (show Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) from
        family f r 0 (s, (t, x))) v =
      stageSimplexBarycentric (simplex f r) 0 (scalarParameter (s, t), x v) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
