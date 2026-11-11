/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRow

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u v
noncomputable section

local instance tensorUnitRowTestMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance tensorUnitRowTestPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

example {C : Type u} [Category.{v} C] (W : Structure C) {n : SimplexCategory}
    {F G : Interval n ⥤ C} (hF : IsRow W F) (e : F ≅ G) : IsRow W G := hF.of_iso W e

example {X : Scheme.{u}} {L : X.Modules} (hL : IsZero L)
    (K : CochainComplex X.Modules ℤ) :
    IsZero (((MonoidalCategory.tensorLeft L).mapHomologicalComplex (.up ℤ)).obj K) :=
  complexTensorLeft_isZero_of_coefficient hL K

example (X : Scheme.{u}) :
    (MonoidalCategory.tensorLeft (0 : X.Modules)).mapHomologicalComplex (.up ℤ) ≅
      (Functor.const (CochainComplex X.Modules ℤ)).obj 0 := complexTensorLeftZeroIso X

example (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    ((complexTensorUnitRows X).obj K).obj (interval 0 1 (by decide)) =
      ((MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ)).obj K :=
  complexTensorUnitRows_whole X K

example (X : Scheme.{u})
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectTensorUnitRows X).obj K ≅
      oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectTensorUnit X).obj K) := tensorUnitRowDiagramIso X K

example (X : Scheme.{u})
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    IsRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      ((boundedAboveFlatPerfectTensorUnitRows X).obj K) :=
  boundedAboveFlatPerfectTensorUnitRows_isRow X K
