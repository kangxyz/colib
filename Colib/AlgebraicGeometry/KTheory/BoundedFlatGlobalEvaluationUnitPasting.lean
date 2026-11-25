/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationStrictSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-! # Full original unit tracks across global evaluation -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- The original section identity-action track followed by the actual normalized evaluation. -/
def evaluationOldUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :=
  (prespectrumIsoHomotopy (boundedAboveFlatGlobalSectionModelFunctor.map f.op)
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r))).postcomp
    (prespectrumMap (evaluationModel (Opposite.op X)))

/-- Actual source evaluation followed by the original raw geometric unit homotopy. -/
def evaluationNewUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :=
  Homotopy.precomp (prespectrumMap (evaluationModel (Opposite.op Y)))
    (boundedAboveFlatPerfectUnitHomotopy f r)

/-- The categorical square compares the two original whole unit-track pastings. -/
def evaluationUnitPasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    ((evaluationOldUnit f r).trans
      (evaluationComparison f)).RelHomotopy
    ((evaluationComparison f).trans
      (evaluationNewUnit f r)) := by
  let h := boundedAboveFlatPerfectPullback_isExact f
  let J := prespectrumTransformationIntertwiningHomotopy
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op) (evaluationRawMap f)
    (evaluationModel (Opposite.op Y))
    (evaluationModel (Opposite.op X))
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r)).hom
    (evaluationRawUnit f r)
    (evaluationComparisonIso f).hom
    (fun _ ↦ (boundedAboveFlatGlobalSectionModelFunctor.obj (Opposite.op X)).obj.waldhausen.weq_iso
      _ inferInstance)
    (fun K ↦ normalizedWeakTransformation_weak h h
      (boundedAboveFlatPerfectPullbackUnitIso f
        r).hom
      (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
      (AsSmall.down.obj K))
    (fun A ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso f).hom.app A))))
    (evaluation_unit_square f r)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

/-- The actual forward Laurent track is retained literally on the global side. -/
def globalLaurentEvaluationPasting (X : Scheme.{u}ᵒᵖ) :=
  evaluationUnitPasting
    (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.coefficient.app X).unop
    (laurentScalar X)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
