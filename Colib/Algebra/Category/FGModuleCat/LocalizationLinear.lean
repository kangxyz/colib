/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.LocalizationLinear
public import Colib.Algebra.Category.FGModuleCat.Localization

/-!
# Linearity of native finite-module localization

The original finite-module functor is the literal restriction of the native
module-localization functor. Forgetting finite generation proves its unchanged
maps preserve base-ring scalars, including for the zero localized ring.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
namespace FGModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original finite-module coefficient functor is linear over its base ring. -/
instance localizedModuleFunctor_linear {R : Type u} [CommRing R] [Small.{v, u} R]
    (S : Submonoid R) : (localizedModuleFunctor.{u, v} S).Linear R where
  map_smul {M N} f r := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.localizedModuleFunctor S).map_smul r f.hom

/-- Exact-functor packaging retains this original linearity. -/
instance localizationExactFunctor_linear {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Small.{v, u} R] (S : Submonoid R) :
    (localizationExactFunctor.{u, v} S).toFunctor.Linear R :=
  localizedModuleFunctor_linear S

end FGModuleCat
