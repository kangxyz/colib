/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction

/-! # A commuting square of literal open restriction functors -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion i] [IsOpenImmersion j]

/-- The literal restrictions along two equal composites are naturally isomorphic. -/
def openSquareRestrictCochainIso (h : a ≫ i = b ≫ j) :
    (restrictFunctor i).mapHomologicalComplex (.up ℤ) ⋙
      (restrictFunctor a).mapHomologicalComplex (.up ℤ) ≅
    (restrictFunctor j).mapHomologicalComplex (.up ℤ) ⋙
      (restrictFunctor b).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (restrictFunctorComp a i).symm (.up ℤ)) ≪≫
    NatIso.mapHomologicalComplex (restrictFunctorCongr h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (restrictFunctorComp b j).symm (.up ℤ)).symm

end AlgebraicGeometry.Scheme.Modules
