/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.TensorCoefficients

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
  (K L : ChainComplex (ModuleCat.{u} R) ℕ)

example : HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K :=
  ChainComplex.tensorOrderIso K L

example :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (HomologicalComplex.tensorObj K L)) ≅
        HomologicalComplex.tensorObj K
          (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj L) :=
  ChainComplex.tensorCoefficientsIso M K L

example :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (HomologicalComplex.tensorObj K L)) ≅
        HomologicalComplex.tensorObj L
          (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  ChainComplex.tensorCoefficientsReverseIso M K L
