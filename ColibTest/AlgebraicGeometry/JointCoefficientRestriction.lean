/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalCoefficientRestriction

/-! The joint index is tested on arbitrary schemes over the base and arbitrary coefficient maps. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.Modules
universe u

example (R : CommRingCat.{u}) : Index R = ((Over (Spec R))ᵒᵖ × Under R) := rfl

example {R : CommRingCat.{u}} {i k : Index R} (f : i ⟶ k) :
    Coefficients.map f ≫ coefficientProjection i =
      coefficientProjection k ≫ Spec.map f.2.right := map_coefficientProjection f

example {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    IsPullback (schemeMap f a) (projection (op P, a)) (projection (op Q, a)) f.left :=
  schemeMap_isPullback f a

example {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under R) : IsOpenImmersion (schemeMap f a) := inferInstance

example {R : CommRingCat.{u}} (P : Over (Spec R)) :
    (identityProjectionIso P).hom = projection (op P, Under.mk (𝟙 R)) := rfl

example (R : CommRingCat.{u}) (i : Index R) :
    (boundedAboveFlatGlobalCoefficientRestriction R i).IsEquivalence := inferInstance

example (R : CommRingCat.{u}) (i : Index R) :
    boundedAboveFlatGlobalCoefficientRestriction R i ⋙
        boundedAboveFlatCoefficientOriginalEvaluation i =
      boundedAboveFlatGlobalSectionEvaluation ((Coefficients.functor R).obj i) :=
  boundedAboveFlatGlobalCoefficientRestriction_evaluation R i

example (R : CommRingCat.{u}) (i : Index R) :
    (boundedAboveFlatGlobalCoefficientRestriction R i).obj
        (boundedAboveFlatGlobalSectionZero ((Coefficients.functor R).obj i)) =
      boundedAboveFlatCoefficientSectionZero i :=
  boundedAboveFlatGlobalCoefficientRestriction_zero R i

example {R : CommRingCat.{u}} {i k : Index R} (f : i ⟶ k) :
    boundedAboveFlatGlobalSectionsMap ((Coefficients.functor R).map f) ⋙
        boundedAboveFlatGlobalCoefficientRestriction R k =
      boundedAboveFlatGlobalCoefficientRestriction R i ⋙ boundedAboveFlatCoefficientSectionsMap f :=
  boundedAboveFlatGlobalCoefficientRestriction_naturality f
