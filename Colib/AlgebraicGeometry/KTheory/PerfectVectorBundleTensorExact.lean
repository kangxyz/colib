/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor

/-! # Ambient exactness of native vector-bundle tensor -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (L : X.Modules)

local instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

local instance : MonoidalPreadditive X.Modules := by
  let := Abelian.hasFiniteBiproducts (C := X.Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

local notation "Perf" =>
  ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]

set_option backward.isDefEq.respectTransparency false in
/-- The native right vector-bundle tensor is additive. -/
instance perfectTensorRight_additive : (perfectTensorRight L).Additive := by
  constructor
  intro K K' f g
  apply ObjectProperty.hom_ext
  exact Functor.map_add ((tensorRight L).mapHomologicalComplex (ComplexShape.up ℤ))

set_option backward.isDefEq.respectTransparency false in
/-- The right vector-bundle tensor preserves the ambient short exact sequences on native perfect
complexes. -/
theorem perfectTensorRight_shortExact (A : ShortComplex Perf)
    (hA : (A.map (ObjectProperty.ι _)).ShortExact) :
    ((A.map (perfectTensorRight L)).map (ObjectProperty.ι _)).ShortExact := by
  let T := tensorRight L
  let F := T.mapHomologicalComplex (ComplexShape.up ℤ)
  have hT : exactFunctor _ _ T := by
    change exactFunctor _ _ ((curriedTensor X.Modules).flip.obj L)
    exact Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat X.sheaf L
      (isFlat_of_isFiniteLocallyFree L)
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).mp hT
  exact hA.map_of_exact F

end AlgebraicGeometry.Scheme.Modules
