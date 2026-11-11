/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientAutomorphism

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u
noncomputable section

example (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
      Obj (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌ :=
  boundedAboveFlatPerfectTensorUnitFirstRow X

example (X : Scheme.{u}) :
    boundedAboveFlatPerfectTensorUnitFirstRow X ≅
      boundedAboveFlatPerfectTensorUnit X ⋙
        oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) := tensorUnitFirstRowIso X

example (X : Scheme.{u}) :
    IsExact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).weq
      (boundedAboveFlatPerfectTensorUnitFirstRow X) :=
  boundedAboveFlatPerfectTensorUnitFirstRow_exact X

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientRow X ≅ tensorUnitCoefficientRow X := tensorUnitCoefficientRowAutomorphism X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectTensorUnitFirstRow X ≅ boundedAboveFlatPerfectTensorUnitFirstRow X :=
  tensorUnitFirstRowAutomorphism X r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitFirstRowAutomorphism X r).hom ≫ (tensorUnitFirstRowIso X).hom =
      (tensorUnitFirstRowIso X).hom ≫
        (Functor.isoWhiskerRight (boundedAboveFlatPerfectTensorUnitAutomorphism X r)
          (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).hom :=
  tensorUnitFirstRowAutomorphism_comparison X r
