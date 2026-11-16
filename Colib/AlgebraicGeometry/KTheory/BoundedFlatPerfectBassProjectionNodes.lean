/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactStageZero
public import Colib.KTheory.Waldhausen.Iterated.NormalizationNaturality
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso

/-!
# The common-reference projection nodes for the Bass overlap boundary

The two charts give equal scheme maps to the base. Their chosen-zero
normalization triangles nevertheless have distinct middle and terminal vertices.
We share only the source, and retain all four specified natural isomorphisms.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
GlobalRawBassInputIdentityProjection.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BassProjectionNodes

open PolynomialLaurent.GlobalIndex

set_option backward.isDefEq.respectTransparency false

/-- The native small Waldhausen category of bounded-above flat perfect complexes. -/
abbrev model (X : Scheme.{u}) :=
  asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)

/-- The actual geometric pullback with its existing chosen-zero normalization. -/
abbrev map {X Y : Scheme.{u}} (f : X ⟶ Y) : model Y ⟶ model X :=
  asSmallCategoryMap _ _ (boundedAboveFlatPerfectPullback_isExact f).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- Normalize the raw composite of the two original pullbacks just once. -/
abbrev middle {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : model Z ⟶ model X :=
  asSmallCategoryMap _ _ ((boundedAboveFlatPerfectPullback_isExact g).comp
    (boundedAboveFlatPerfectPullback_isExact f)).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The geometric pullback composition isomorphism, conjugated by the two zero rebases. -/
def first {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (map (f ≫ g)).hom.toFunctor ≅ (middle f g).hom.toFunctor := by
  let i := boundedAboveFlatPerfectPullbackCompIso f g
  let h := boundedAboveFlatPerfectPullback_isExact (f ≫ g)
  let k := (boundedAboveFlatPerfectPullback_isExact g).comp
    (boundedAboveFlatPerfectPullback_isExact f)
  let W := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace
  let V := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  exact isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((CategoryTheory.rebaseFunctorIso _ W.zero V.zero ((h.zero W.isZero).iso V.isZero)).symm ≪≫
      i ≪≫ CategoryTheory.rebaseFunctorIso _ W.zero V.zero ((k.zero W.isZero).iso V.isZero))
    AsSmall.up)

/-- The canonical passage from one normalization of a composite to two successive ones. -/
def second {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (middle f g).hom.toFunctor ≅ (map g ≫ map f).hom.toFunctor :=
  modelAsSmallCompositionIso _ _ _ _ _
    (exactNormalizationCompIso (boundedAboveFlatPerfectPullback_isExact g)
      (boundedAboveFlatPerfectPullback_isExact f)) rfl rfl

variable (X : Scheme.{u})

/-- The reference is pullback along the actual positive-chart projection. -/
abbrev source := map (plus.app X ≫ projection.app X)

/-- The inverse-chart projection reuses that reference by the literal scheme-map equality. -/
def sourceIso :
    (source X).hom.toFunctor ≅ (map (minus.app X ≫ projection.app X)).hom.toFunctor :=
  eqToIso (congrArg (fun f ↦ (map f).hom.toFunctor) (chart_projection X))

/-- All five nodes of the two normalization triangles in their common-reference nerve. -/
def nodes : Fin 5 → CommonReferenceNerve.Node (source X) :=
  ![⟨source X, Iso.refl _⟩,
    ⟨middle (plus.app X) (projection.app X), first (plus.app X) (projection.app X)⟩,
    ⟨map (projection.app X) ≫ map (plus.app X),
      first (plus.app X) (projection.app X) ≪≫ second (plus.app X) (projection.app X)⟩,
    ⟨middle (minus.app X) (projection.app X),
      sourceIso X ≪≫ first (minus.app X) (projection.app X)⟩,
    ⟨map (projection.app X) ≫ map (minus.app X),
      sourceIso X ≪≫
        (first (minus.app X) (projection.app X) ≪≫ second (minus.app X) (projection.app X))⟩]

/-- The positive normalization triangle selects vertices `0,1,2`. -/
def plusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The inverse normalization triangle selects vertices `0,3,4`. -/
def minusFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

end AlgebraicGeometry.Scheme.Modules.BassProjectionNodes
