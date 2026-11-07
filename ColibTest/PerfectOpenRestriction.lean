/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar

/-! Regression examples for literal open restriction and scalar multiplication. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
  (f : K ⟶ L)

-- The functor's object and arrow are literal, not transports through another perfect model.
example : ((perfectComplexesRestrictOpenImmersion j).obj K).obj =
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

example : ((perfectComplexesRestrictOpenImmersion j).map f).hom =
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom := rfl

example : Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
    (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).cof
    (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
    (perfectComplexesRestrictOpenImmersion j) := perfectComplexesRestrictOpenImmersion_isExact j

-- The old open-subset interface remains available verbatim.
example (U : X.Opens) : ((perfectComplexesRestrictFunctor X U).obj K).obj =
    ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

-- Multiplication is the pinned Stacks scalar, including the actual inverse unit.
example (q : (Γ(X, ⊤))ˣ) (n : ℤ) :
    (((perfectGlobalUnitIso X q).hom.app K).hom).f n =
      (Stacks.RegularSequence.globalSmulCenter X (q : Γ(X, ⊤))).app (K.obj.X n) := rfl

example (q : (Γ(X, ⊤))ˣ) (n : ℤ) :
    (((perfectGlobalUnitIso X q).inv.app K).hom).f n =
      (Stacks.RegularSequence.globalSmulCenter X (↑(q⁻¹) : Γ(X, ⊤))).app (K.obj.X n) := rfl

example (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    (perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K) =
      (perfectGlobalUnitIso Y q).hom.app ((perfectComplexesRestrictOpenImmersion j).obj K) :=
  perfectRestrict_scalar_eq_globalUnit j r q hq K

example (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    IsIso ((perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K)) :=
  isIso_perfectRestrict_scalar j r q hq K

example (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
      ((perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K)) :=
  quasiIso_restrict_complexGlobalScalar j r q hq K.obj
