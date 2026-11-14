/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnit
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumScalarOperationSquare
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality
public import Colib.Topology.Prespectrum.SelfTrackIntertwining
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-! # The original scalar is preserved by normalized coefficient evaluation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Opposite Topology.LoopPrespectrum CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules

open GlobalSectionChangeIndex

variable {R : CommRingCat.{u}}

attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

local instance coefficientEvaluationDownEquivalence (i : Index R) :
    (AsSmall.down : AsSmall.{0} (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectComplex
      (space i).toRingedSpace).FullSubcategory ⥤
      (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectComplex
        (space i).toRingedSpace).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The original section evaluation already preserves the actual scalar before rebasing. -/
theorem boundedAboveFlatCoefficientSectionSmallEquivalence_preserves_unit (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor
      (boundedAboveFlatCoefficientSectionUnitIso i r) (evaluationSmallUnit (op (space i)) r) := by
  intro S
  let C := (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectComplex
    (space i).toRingedSpace).FullSubcategory
  apply (AsSmall.down : AsSmall.{0} C ⥤ C).map_injective
  change (boundedAboveFlatCoefficientOriginalEvaluation i).map
      ((boundedAboveFlatCoefficientSectionUnitIso i r).hom.app S) = _
  rw [evaluationSmallUnit, map_lift_hom]
  exact boundedAboveFlatCoefficientSectionUnitIso_evaluation_hom i r S

/-- The chosen-zero normalized model evaluation preserves the literal scalar automorphism. -/
theorem boundedAboveFlatCoefficientSectionEvaluationModelMap_preserves_unit (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor
      (boundedAboveFlatCoefficientSectionUnitIso i r) (evaluationSmallUnit (op (space i)) r) := by
  change Preserves (CategoryTheory.rebaseFunctor
    (boundedAboveFlatCoefficientSectionSmallEquivalence i).functor
    (boundedAboveFlatCoefficientSectionWaldhausen i).zero _
    (boundedAboveFlatCoefficientSectionEvaluationZeroIso i)) _ _
  exact rebase_preserves _ _ _ _ _ _
    (boundedAboveFlatCoefficientSectionSmallEquivalence_preserves_unit i r)

/-- The full evaluation transition intertwines the actual coefficient and raw geometric units. -/
theorem boundedAboveFlatCoefficientSectionEvaluation_unit_square {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    whiskerRight (onFunctor (boundedAboveFlatCoefficientSectionModelMap f).hom.toFunctor
        (boundedAboveFlatCoefficientSectionUnitIso k r)).hom
        (boundedAboveFlatCoefficientSectionEvaluationModelMap k).hom.toFunctor ≫
      (boundedAboveFlatCoefficientSectionEvaluationIso f).hom =
    (boundedAboveFlatCoefficientSectionEvaluationIso f).hom ≫
      whiskerLeft (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor
        (evaluationRawUnit (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) r) := by
  rw [evaluationRawUnit_eq]
  exact onFunctor_whisker_square (boundedAboveFlatCoefficientSectionModelMap f).hom.toFunctor
    (boundedAboveFlatCoefficientOriginalModelMap f).hom.toFunctor
    (boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor
    (boundedAboveFlatCoefficientSectionEvaluationModelMap k).hom.toFunctor
    (boundedAboveFlatCoefficientSectionEvaluationIso f).hom
    (boundedAboveFlatCoefficientSectionUnitIso k r) (evaluationSmallUnit (op (space k)) r)
    (boundedAboveFlatCoefficientSectionEvaluationModelMap_preserves_unit k r).whisker

/-- The original whole coefficient automorphism on its actual exact model map. -/
def boundedAboveFlatCoefficientSectionScalarTrack {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    Homotopy (prespectrumMap (boundedAboveFlatCoefficientSectionModelMap f))
      (prespectrumMap (boundedAboveFlatCoefficientSectionModelMap f)) :=
  prespectrumIsoHomotopy (boundedAboveFlatCoefficientSectionModelMap f)
    (onFunctor (boundedAboveFlatCoefficientSectionModelMap f).hom.toFunctor
      (boundedAboveFlatCoefficientSectionUnitIso k r))

set_option maxHeartbeats 700000 in
-- The two original chosen-zero model tracks are large when specialized to this exact square.
/-- The actual coefficient Model track evaluates to the original raw bounded-flat unit track. -/
theorem boundedAboveFlatCoefficientSectionEvaluation_stableOperation {i k : Index R}
    (f : i ⟶ k) (r : (Γ(space k, ⊤))ˣ) (d : ℤ) :
    (boundedAboveFlatCoefficientSectionScalarTrack f r).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap k) =
    (stableHomotopyFunctor d).map (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i) ≫
      (boundedAboveFlatPerfectUnitHomotopy
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) r).stableOperation d := by
  let F := boundedAboveFlatCoefficientSectionModelMap f
  let G := boundedAboveFlatCoefficientOriginalModelMap f
  let A := boundedAboveFlatCoefficientSectionEvaluationModelMap i
  let B := boundedAboveFlatCoefficientSectionEvaluationModelMap k
  let η := onFunctor F.hom.toFunctor (boundedAboveFlatCoefficientSectionUnitIso k r)
  let θ := evaluationRawUnit (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) r
  let T := boundedAboveFlatCoefficientSectionEvaluationIso f
  have he : whiskerRight η.hom B.hom.toFunctor ≫ T.hom =
      T.hom ≫ whiskerLeft A.hom.toFunctor θ :=
    boundedAboveFlatCoefficientSectionEvaluation_unit_square f r
  have hθ : ∀ x, (asSmallCategory
      (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectWaldhausen
        (space k).toRingedSpace)).obj.waldhausen.weq (θ.app x) := by
    intro x
    dsimp only [θ]
    rw [evaluationRawUnit_eq]
    exact (asSmallCategory (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectWaldhausen
      (space k).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance
  exact prespectrumTransformation_stableOperation_square F G A B η.hom θ T.hom
    (fun _ => (boundedAboveFlatCoefficientSectionWaldhausen k).weq_iso _ inferInstance)
    hθ (fun _ => (asSmallCategory
      (AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectWaldhausen
      (space k).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance) he d

end AlgebraicGeometry.Scheme.Modules
