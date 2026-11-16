/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectBassProjectionNodes

/-!
# The base-unit reference of the Bass overlap boundary

The common reference keeps the split comparison for pullback along the base identity.
Reanchoring only precomposes the specified natural isomorphisms: it does not change any
of the five actual projection functors.

Adapted from `GlobalRawBassInputIdentityNodes.lean` and
`OriginalUnitSquareSimplex.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.RingedSpace CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BassProjectionNodes

set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

/-- The native chosen-zero normalization of the identity functor. -/
abbrev unitMiddle : model X ⟶ model X :=
  asSmallCategoryMap _ _ (IsExact.id
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The geometric part of the split unit comparison. -/
def unitFirst : (pullbackMap (𝟙 X)).hom.toFunctor ≅ (unitMiddle X).hom.toFunctor := by
  let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let h := boundedAboveFlatPerfectPullback_isExact (𝟙 X)
  let k := IsExact.id W.cof W.weq
  exact isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((CategoryTheory.rebaseFunctorIso _ W.zero W.zero ((h.zero W.isZero).iso W.isZero)).symm ≪≫
      boundedAboveFlatPerfectPullbackIdIso X ≪≫
      CategoryTheory.rebaseFunctorIso _ W.zero W.zero ((k.zero W.isZero).iso W.isZero))
    AsSmall.up)

/-- Cancellation of the chosen-zero normalization of the identity. -/
def unitSecond : (unitMiddle X).hom.toFunctor ≅ (𝟙 (model X)).hom.toFunctor := by
  let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let k := IsExact.id W.cof W.weq
  exact modelAsSmallIdentityIso W _
    (CategoryTheory.rebaseFunctorIso _ W.zero W.zero ((k.zero W.isZero).iso W.isZero)).symm
    rfl rfl

/-- The reference of the entire overlap boundary, including the base-unit factor. -/
abbrev overlapReference := pullbackMap (𝟙 X) ≫ source X

/-- The original two-step comparison, whiskered by the entire projection functor. -/
def sourceToProjection : (overlapReference X).hom.toFunctor ≅ (source X).hom.toFunctor :=
  isoWhiskerRight (unitFirst X ≪≫ unitSecond X) (source X).hom.toFunctor

/-- The five actual projection maps, with references now starting at the base-unit composite. -/
def overlapNodes (i : Fin 5) : CommonReferenceNerve.Node (overlapReference X) :=
  ⟨(nodes X i).1, sourceToProjection X ≪≫ (nodes X i).2⟩

/-- The transition between two reanchored nodes is the unchanged original natural transformation. -/
theorem overlapNodes_transition (i j : Fin 5) :
    (overlapNodes X i).2.inv ≫ (overlapNodes X j).2.hom =
      (nodes X i).2.inv ≫ (nodes X j).2.hom := by
  simp [overlapNodes, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.BassProjectionNodes
