/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentEvaluationUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientConnectiveEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientConnectiveChart
public import Colib.AlgebraicGeometry.ProjectiveLine.CoefficientLaurentUnitOperation
public import Colib.RingTheory.KTheory.Bass.StrictLaurentInverseAction
public import Colib.KTheory.Waldhausen.Iterated.ExactSelfTrackStableOperation
public import Colib.AlgebraicGeometry.Modules.PerfectGlobalUnit

/-! # The actual ambient inverse Laurent scalar under geometric evaluation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
open Topology.LoopPrespectrum KTheory.Bass

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

local notation "A" => (boundedAboveFlatCoefficientAmbientLaurentAction P)

abbrev coefficientLaurentObject : Under R := Functor.obj (laurentUnderFunctor R) a
abbrev coefficientLaurentScalar :
    (Γ(space (Opposite.op P, coefficientLaurentObject a), ⊤))ˣ :=
  boundedAboveFlatCoefficientUnit (Opposite.op P, coefficientLaurentObject a)
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate a.right)
abbrev coefficientLaurentArrow :
    (Opposite.op P, a) ⟶ (Opposite.op P, coefficientLaurentObject a) :=
  (𝟙 (Opposite.op P), NatTrans.app (laurentUnderCoefficient R) a)

local notation "l" => (coefficientLaurentObject a)
local notation "q" => (coefficientLaurentScalar P a)
local notation "proj" =>
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection P a)
local notation "J" => (coefficientLaurentArrow P a)

/-- The forward coefficient unit is the literal original strict Model action on every level. -/
theorem coefficientAmbientForwardScalarTrack (d : ℤ) :
    ((A).track.homotopy a).stableOperation d =
      (boundedAboveFlatCoefficientSectionScalarTrack J q).stableOperation d := rfl

attribute [local irreducible] boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap
  boundedAboveFlatPerfectUnitHomotopy perfectFlatUnitHomotopy

variable [CompactSpace P.left]

private theorem scalarOperation_comp_evaluation {B₁ B₂ F₁ F₂ K₁ K₂ : AddCommGrpCat}
    (h : B₁ ⟶ B₂) (g : F₁ ⟶ F₂) (k : K₁ ⟶ K₂)
    (e : B₁ ⟶ F₁) (e' : B₂ ⟶ F₂) (i : F₁ ⟶ K₁) (i' : F₂ ⟶ K₂)
    (he : h ≫ e' = e ≫ g) (hi : g ≫ i' = i ≫ k) :
    h ≫ (e' ≫ i') = (e ≫ i) ≫ k :=
  (Category.assoc h e' i').symm.trans
    ((congrArg (fun z => z ≫ i') he).trans
      ((Category.assoc e g i').trans
        ((congrArg (fun z => e ≫ z) hi).trans (Category.assoc e i k).symm)))

/-- Both original evaluation maps preserve the whole forward scalar operation. -/
theorem coefficientAmbientForwardScalar_evaluationCore (d : ℤ) :
    (boundedAboveFlatCoefficientSectionScalarTrack J q).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, l)) =
    (stableHomotopyFunctor d).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, a)) ≫
      (perfectFlatUnitHomotopy proj q).stableOperation d := by
  let E := boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap (Opposite.op P, a)
  let E' := boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap (Opposite.op P, l)
  let I := boundedAboveFlatPerfectToPerfectPrespectrumMap (space (Opposite.op P, a)).toRingedSpace
  let I' := boundedAboveFlatPerfectToPerfectPrespectrumMap (space (Opposite.op P, l)).toRingedSpace
  let H := boundedAboveFlatCoefficientSectionScalarTrack J q
  let f := AlgebraicGeometry.Scheme.BaseChange.Coefficients.map J
  have ef : f = proj := rfl
  let : Flat f := ef.symm ▸ compactFiberLaurentProjection_flat P a
  let G := boundedAboveFlatPerfectUnitHomotopy f q
  let U := perfectFlatUnitHomotopy f q
  let F := stableHomotopyFunctor d
  let F' := stableHomotopyFunctor (d + 1)
  have h : H.stableOperation d ≫ F'.map E' = F.map E ≫ G.stableOperation d :=
    boundedAboveFlatCoefficientSectionEvaluation_stableOperation J q d
  have h' : G.stableOperation d ≫ F'.map I' = F.map I ≫ U.stableOperation d :=
    boundedAboveFlatPerfectUnitHomotopy_stableOperation_inclusion f q d
  have hL := F'.map_comp E' I'
  have hR := F.map_comp E I
  let h₀ := scalarOperation_comp_evaluation (H.stableOperation d) (G.stableOperation d)
    (U.stableOperation d) (F.map E) (F'.map E') (F.map I) (F'.map I') h h'
  have h₁ := congrArg (fun t => H.stableOperation d ≫ t) hL
  have h₂ := congrArg (fun t => t ≫ U.stableOperation d) hR.symm
  have hu : U.stableOperation d = (perfectFlatUnitHomotopy proj q).stableOperation d := by
    dsimp only [U, f]
    rfl
  exact h₁.trans (h₀.trans (h₂.trans (congrArg (fun k => F.map (E ≫ I) ≫ k) hu)))

/-- After actual perfect evaluation the forward fine action is the forward Laurent
operation on the native coefficient fiber. -/
theorem coefficientAmbientForwardScalar_evaluation (d : ℤ) :
    ((A).track.homotopy a).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, l)) =
    (stableHomotopyFunctor d).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, a)) ≫
      (perfectFlatUnitHomotopy proj q).stableOperation d := by
  exact (congrArg (fun t => t ≫ (stableHomotopyFunctor (d + 1)).map
    (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, l)))
    (coefficientAmbientForwardScalarTrack P a d)).trans
      (coefficientAmbientForwardScalar_evaluationCore P a d)

set_option maxHeartbeats 450000 in
-- Unfolding the exact scalar automorphism involves its chosen-zero comparison.
/-- Actual inverse Laurent coefficients induce the negative forward operation on the
same original stable groups. -/
theorem coefficientAmbientInverseScalar_evaluation (d : ℤ) :
    ((A).symm.track.homotopy a).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, l)) =
    (stableHomotopyFunctor d).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (Opposite.op P, a)) ≫
      (perfectFlatUnitHomotopy proj q⁻¹).stableOperation d := by
  have hi : (perfectFlatPullbackUnitIso proj q⁻¹) =
      (perfectFlatPullbackUnitIso proj q).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    simp only [perfectFlatPullbackUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.id_comp]
    exact congrArg Iso.hom (perfectGlobalUnitIso_app_inv _ q _)
  have hs : (perfectFlatUnitHomotopy proj q⁻¹).stableOperation d =
      -(perfectFlatUnitHomotopy proj q).stableOperation d := by
    unfold perfectFlatUnitHomotopy
    rw [hi]
    exact exactIsoSelfTrack_stableOperation_symm _ _ _ _ d
  rw [(A).symm_stableOperation, hs, Preadditive.neg_comp, Preadditive.comp_neg]
  exact congrArg Neg.neg (coefficientAmbientForwardScalar_evaluation P a d)

end AlgebraicGeometry.Scheme.Modules
