/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassCommonChartSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0OuterNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1UnaryReferences
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectReferenceCoherence
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# The common center of the first two Bass H₁ faces

Identifies the full node, including its comparison isomorphism, by the
original three-factor pullback coherence. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/H1MiddleJoinReference.lean`
and the precomposition operation in `ReferenceRowTransport.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open BoundedFlatCoefficientBassH1H0Boundary BoundedFlatCoefficientBassH1References
open BoundedFlatPerfectReferenceCoherence ModelSimplex

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/--
The first H₁ central node after Laurent postcomposition, with its Laurent naturality transport
and binary normalization reference.
-/
def firstCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap (laurentProjection P b) (coefficientMap P u),
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedAboveFlatPerfectNormalizedPullback (laurent_naturality P u))) ≪≫
        BoundedFlatPerfectBinarySimplex.total (laurentProjection P b) (coefficientMap P u)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P u)

/--
The middle H₁ central node after coefficient precomposition, with its binary Laurent
normalization reference.
-/
def middleCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b),
      BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P v)

/-- This is the original first-component node, with only its proved geometric normal form used. -/
theorem first_center_original :
    BoundedFlatCoefficientBassH1References.firstNodes P u v 26 = firstCenter P u v :=
  congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v)) (target_normal P u)

/-- This is the original middle-component node, including its exact source normalization. -/
theorem middle_center_original :
    BoundedFlatCoefficientBassH1References.middleNodes P u v 2 = middleCenter P u v :=
  congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v))
    (source_normal P v)

/-- The two center routes have the same associated target functor. -/
theorem center_functor :
    (firstCenter P u v).1.hom.toFunctor = (middleCenter P u v).1.hom.toFunctor := rfl

/-- The actual two normalization routes agree by three-factor pullback coherence. -/
theorem center_reference : (firstCenter P u v).2 = (middleCenter P u v).2 := by
  have he : eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
      (congrArg boundedAboveFlatPerfectNormalizedPullback (laurent_naturality P u))) ≪≫
        BoundedFlatPerfectBinarySimplex.total (laurentProjection P b) (coefficientMap P u) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (laurent_naturality P u)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (laurentProjection P b) (coefficientMap P u)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedAboveFlatPerfectNormalizedPullback (laurent_naturality P u))) ≪≫
        BoundedFlatPerfectBinarySimplex.total (laurentProjection P b) (coefficientMap P u))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor =
    middleIso P u v ≪≫ isoWhiskerLeft
      (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u).hom.toFunctor
      (BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b))
  rw [he]
  change smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (first_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (laurent_naturality P u)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso
          (laurentProjection P b) (coefficientMap P u)))
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (middle_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
        (coefficientMap P u)) ≪≫
    isoWhiskerLeft
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback (coefficientMap P u) ⋙ AsSmall.up)
      (smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)
      (coefficientMap P u)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (laurent_naturality P u) (middle_total P u v).symm (first_total P u v).symm).symm

/-- A full dependent H₁ boundary node is shared, not merely its endpoint functor. -/
theorem first_middle_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 26 =
    BoundedFlatCoefficientBassH1References.middleNodes P u v 2 := by
  rw [first_center_original, middle_center_original]
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (center_functor P u v)
  · have href := heq_of_eq (center_reference P u v)
    exact href

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
