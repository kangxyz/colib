/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of the actual module-localization functor

The native localization of morphisms is the actual scalar-extended linear map.
Its linearity retains the specified base-ring action on the target category.

The proof follows the existing private `localizedModuleFunctor_linear` proof in
`StacksFrontier/Homology/Perfect/MinimalRepresentative/HomEquations.lean:121-130`
at the pinned Stacks source, here at the public lower module-category owner.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
namespace ModuleCat

/-- Localization of actual module morphisms is linear over the original base ring. -/
instance localizedModuleFunctor_linear {R : Type u} [CommRing R] [Small.{v} R]
    (S : Submonoid R) : (localizedModuleFunctor.{v} S).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    let L := IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) (Localization S)
    change L (r • f.hom) = algebraMap R (Localization S) r • L f.hom
    rw [IsScalarTower.algebraMap_smul]
    exact L.map_smul r f.hom

end ModuleCat
