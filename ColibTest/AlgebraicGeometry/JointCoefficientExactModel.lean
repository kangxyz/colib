/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientModelRestriction

/-! The joint Waldhausen diagram keeps the original maps, zero and both exact equivalence legs. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.Modules
universe u

example {R : CommRingCat.{u}} (i : Index R) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).zero =
      boundedAboveFlatCoefficientSectionZero i := rfl

example {R : CommRingCat.{u}} (i : Index R) :
    IsZero (boundedAboveFlatCoefficientSectionZero i) :=
  boundedAboveFlatCoefficientSectionZero_isZero i

example {R : CommRingCat.{u}} {i k : Index R} (f : i ⟶ k) :
    (boundedAboveFlatCoefficientSectionModelMap f).hom.toFunctor =
      boundedAboveFlatCoefficientSectionsMap f := rfl

example (R : CommRingCat.{u}) {i k l : Index R} (f : i ⟶ k) (g : k ⟶ l) :
    (boundedAboveFlatCoefficientSectionModelFunctor R).map (f ≫ g) =
      (boundedAboveFlatCoefficientSectionModelFunctor R).map f ≫
        (boundedAboveFlatCoefficientSectionModelFunctor R).map g :=
  (boundedAboveFlatCoefficientSectionModelFunctor R).map_comp f g

example (R : CommRingCat.{u}) (i : Index R) :
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor =
      boundedAboveFlatGlobalCoefficientRestriction R i := rfl

example (R : CommRingCat.{u}) (i : Index R) :
    Waldhausen.IsExact
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).cof
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).weq
      (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatGlobalCoefficientRestriction R i) :=
  boundedAboveFlatGlobalCoefficientRestriction_exact R i

example (R : CommRingCat.{u}) (i : Index R) :
    Waldhausen.IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).cof
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).weq
      (boundedAboveFlatGlobalCoefficientRestriction R i).asEquivalence.inverse :=
  boundedAboveFlatGlobalCoefficientRestriction_inverse_exact R i

example (R : CommRingCat.{u}) (i : Index R) :
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor.obj
        (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).zero =
      (boundedAboveFlatCoefficientSectionWaldhausen i).zero :=
  ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).property

example {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    (boundedAboveFlatCoefficientSectionModelRestriction f).app a =
      boundedAboveFlatCoefficientSectionModelMap (f.op, 𝟙 a) := rfl

example (R : CommRingCat.{u}) {i k : Index R} (f : i ⟶ k) :
    (Coefficients.functor R ⋙ boundedAboveFlatGlobalSectionModelFunctor).map f ≫
        (boundedAboveFlatGlobalCoefficientModelRestriction R).app k =
      (boundedAboveFlatGlobalCoefficientModelRestriction R).app i ≫
        (boundedAboveFlatCoefficientSectionModelFunctor R).map f :=
  (boundedAboveFlatGlobalCoefficientModelRestriction R).naturality f
