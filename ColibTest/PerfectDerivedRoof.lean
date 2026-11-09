/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.PerfectDerivedRoof

/-! # Regression tests for native perfect chain-map roof representatives -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d₁ d₂

section CommonFraction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

example {R K E : CochainComplex C ℤ}
    (s : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj K)
    (t : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj E) :
    ∃ (R' : CochainComplex C ℤ) (r : R' ⟶ R) (q : R' ⟶ K) (a : R' ⟶ E),
      QuasiIso r ∧ DerivedCategory.Q.map r ≫ s = DerivedCategory.Q.map q ∧
        DerivedCategory.Q.map r ≫ t = DerivedCategory.Q.map a :=
  DerivedCategory.exists_common_right_fraction s t

end CommonFraction

section OpenRestriction

open Scheme.Modules

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d₁} X.Modules] [HasDerivedCategory.{d₂} U.Modules]

-- Neither scheme is assumed quasi-compact or quasi-separated in the representative comparison.
-- The two derived-category models can have different morphism universes.
example {K E : CochainComplex X.Modules ℤ}
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) (f : K ⟶ E) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ K) (a : R ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  refine exists_isPerfectComplex_chainMap_roof j hK (𝟙 _) (DerivedCategory.Q.map f)
    (DerivedCategory.Q.map
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (by infer_instance) ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((restrictFunctor j).mapDerivedCategoryFactors_hom_naturality f).symm

end OpenRestriction
